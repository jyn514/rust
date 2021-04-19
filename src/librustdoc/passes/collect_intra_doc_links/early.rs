use rustc_ast as ast;
use rustc_hir::def::Namespace::{self, *};
use rustc_hir::def_id::{DefId, LocalDefId, CRATE_DEF_INDEX};
use rustc_interface::interface;
use rustc_resolve::Resolver;

use std::cell::RefCell;
use std::mem;
use std::rc::Rc;

use super::*;

// Letting the resolver escape at the end of the function leads to inconsistencies between the
// crates the TyCtxt sees and the resolver sees (because the resolver could load more crates
// after escaping). Hopefully `IntraLinkCrateLoader` gets all the crates we need ...
crate struct IntraLinkCrateLoader {
    current_mod: DefId,
    crate resolver: Rc<RefCell<interface::BoxedResolver>>,

    // TODO: pass on all these fields to the late loader
    /// A stack of modules used to decide what scope to resolve in.
    ///
    /// The last module will be used if the parent scope of the current item is
    /// unknown.
    mod_ids: Vec<DefId>,
    /// This is used to store the kind of associated items,
    /// because `clean` and the disambiguator code expect them to be different.
    /// See the code for associated items on inherent impls for details.
    kind_side_channel: Cell<Option<(DefKind, DefId)>>,
    /// Cache the resolved links so we can avoid resolving (and emitting errors for) the same link.
    /// The link will be `None` if it could not be resolved (i.e. the error was cached).
    visited_links: FxHashMap<ResolutionInfo, LinkResult<CachedLink>>,
}

impl IntraLinkCrateLoader {
	crate fn new(resolver: Rc<RefCell<interface::BoxedResolver>>) -> Self {
		let crate_id = LocalDefId { local_def_index: CRATE_DEF_INDEX }.to_def_id();
		Self { current_mod: crate_id, resolver, mod_ids: vec![], kind_side_channel: Cell::new(None), visited_links: FxHashMap::default() }
	}

    crate fn enter_resolver<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut Resolver<'_>) -> R,
    {
        self.resolver.borrow_mut().access(f)
    }

}

impl ast::visit::Visitor<'_> for IntraLinkCrateLoader {
    fn visit_attribute(&mut self, attr: &ast::Attribute) {
        use crate::html::markdown::markdown_links;
        use crate::passes::collect_intra_doc_links::preprocess_link;

        if let Some(doc) = attr.doc_str() {
            for link in markdown_links(&doc.as_str()) {
                let path_str = if let Some(Ok(x)) = preprocess_link(&link) {
                    x.path_str
                } else {
                    continue;
                };
                self.resolver.borrow_mut().access(|resolver| {
                    let _ = resolver.resolve_str_path_error(
                        attr.span,
                        &path_str,
                        TypeNS,
                        self.current_mod,
                    );
                });
            }
        }
        ast::visit::walk_attribute(self, attr);
    }

    fn visit_item(&mut self, item: &ast::Item) {
        use rustc_ast_lowering::ResolverAstLowering;

        if let ast::ItemKind::Mod(..) = item.kind {
            let new_mod =
                self.resolver.borrow_mut().access(|resolver| resolver.local_def_id(item.id));
            let old_mod = mem::replace(&mut self.current_mod, new_mod.to_def_id());
            ast::visit::walk_item(self, item);
            self.current_mod = old_mod;
        } else {
            ast::visit::walk_item(self, item);
        }
    }
}

impl IntraLinkCrateLoader {
    /// Convenience wrapper around `resolve_str_path_error`.
    ///
    /// This also handles resolving `true` and `false` as booleans.
    /// NOTE: `resolve_str_path_error` knows only about paths, not about types.
    /// Associated items will never be resolved by this function.
    fn resolve_path(&self, path_str: &str, ns: Namespace, module_id: DefId) -> Option<Res> {
        let result = self.enter_resolver(|resolver| {
            resolver
                .resolve_str_path_error(DUMMY_SP, &path_str, ns, module_id)
                .and_then(|(_, res)| res.try_into())
        });
        debug!("{} resolved to {:?} in namespace {:?}", path_str, result, ns);
        match result {
            // resolver doesn't know about true, false, and types that aren't paths (e.g. `()`)
            // manually as bool
            Err(()) => resolve_primitive(path_str, ns).map(Into::into),
            Ok(res) => Some(res),
        }
    }

    /// Resolves a string as a path within a particular namespace. Returns an
    /// optional URL fragment in the case of variants and methods.
    fn resolve<'path>(
        &mut self,
        path_str: &'path str,
        ns: Namespace,
        module_id: DefId,
        extra_fragment: &Option<String>,
    ) -> LinkResult<EarlyRes> {
        if let Some(res) = self.resolve_path(path_str, ns, module_id) {
            match res {
                // FIXME(#76467): make this fallthrough to lookup the associated
                // item a separate function.
                Res::Def(DefKind::AssocFn | DefKind::AssocConst, _) => assert_eq!(ns, ValueNS),
                Res::Def(DefKind::AssocTy, _) => assert_eq!(ns, TypeNS),
                Res::Def(DefKind::Variant, _) => {
                    return Ok(EarlyRes::UnresolvedVariant(res));
                }
                // Not a trait item; just return what we found.
                Res::Primitive(ty) => {
                    if extra_fragment.is_some() {
                        return Err(
                            AnchorFailure::RustdocAnchorConflict(res.into()).into(),
                        );
                    }
                    return Ok(EarlyRes::Resolved(res, Some(ty.as_str().to_owned())));
                }
                _ => return Ok(EarlyRes::Resolved(res, extra_fragment.clone())),
            }
        }

        // Try looking for methods and associated items.
        let mut split = path_str.rsplitn(2, "::");
        // NB: `split`'s first element is always defined, even if the delimiter was not present.
        // NB: `item_str` could be empty when resolving in the root namespace (e.g. `::std`).
        let item_str = split.next().unwrap();
        let item_name = Symbol::intern(item_str);
        let path_root = match split.next() {
			Some(r) => r.to_owned(),
			None => {
				// If there's no `::`, it's not an associated item.
				// So we can be sure that `rustc_resolve` was accurate when it said it wasn't resolved.
                debug!("found no `::`, assumming {} was correctly not in scope", item_name);
                let err = ResolutionFailure::NotResolved {
                    module_id,
                    partial_res: None,
                    unresolved: item_str.into(),
                };
                return Err(LinkError::Resolution(err, path_str.to_string(), disambiguator));
            }
		};

        // FIXME(#83862): this arbitrarily gives precedence to primitives over modules to support
        // links to primitives when `#[doc(primitive)]` is present. It should give an ambiguity
        // error instead and special case *only* modules with `#[doc(primitive)]`, not all
        // primitives.
        let ty_res = resolve_primitive(&path_root, TypeNS)
            .map(Into::into)
            .or_else(|| self.resolve_path(&path_root, TypeNS, module_id))
			.map(|res| (res, item_name));
		let variant_res = if ns == Namespace::ValueNS {
			self.variant_res(path_str, module_id)
		} else {
			None
		};
		Ok(EarlyRes::Unresolved(UnresolvedLink {
			ty_res, variant_res
		}))
	}

	fn variant_res(&self, path_str: &str, module_id: DefId) -> Option<(Res, Symbol, Symbol)> {
		debug!("looking for enum variant {}", path_str);
		let mut split = path_str.rsplitn(3, "::");
		let (variant_field_str, variant_field_name) = split
			.next()
			.map(|f| (f, Symbol::intern(f)))
			.expect("fold_item should ensure link is non-empty");
		// we're not sure this is a variant at all, so use the full string
		// If there's no second component, the link looks like `[path]`.
		// So there's no partial res and we should say the whole link failed to resolve.
		let variant_name = Symbol::intern(split.next()?);
		let path = split.next()?.to_owned();
		let variant_res = self
			.enter_resolver(|resolver| {
				resolver.resolve_str_path_error(DUMMY_SP, &path, TypeNS, module_id)
			})
			.and_then(|(_, res)| res.try_into())
			.ok()?;
		Some((variant_res, variant_name, variant_field_name))
	}

    /// Resolves a string as a macro.
    ///
    /// FIXME(jynelson): Can this be unified with `resolve()`?
    fn resolve_macro(
        &self,
        path_str: &'a str,
        module_id: DefId,
    ) -> Result<Res, ResolutionFailure<'a>> {
        let path = ast::Path::from_ident(Ident::from_str(path_str));
        self.enter_resolver(|resolver| {
            // FIXME(jynelson): does this really need 3 separate lookups?
            if let Ok((Some(ext), res)) = resolver.resolve_macro_path(
                &path,
                None,
                &ParentScope::module(resolver.graph_root(), resolver),
                false,
                false,
            ) {
                if let SyntaxExtensionKind::LegacyBang { .. } = ext.kind {
                    return Ok(res.try_into().unwrap());
                }
            }
            if let Some(&res) = resolver.all_macros().get(&Symbol::intern(path_str)) {
                return Ok(res.try_into().unwrap());
            }
            debug!("resolving {} as a macro in the module {:?}", path_str, module_id);
            if let Ok((_, res)) =
                resolver.resolve_str_path_error(DUMMY_SP, path_str, MacroNS, module_id)
            {
                // don't resolve builtins like `#[derive]`
                if let Ok(res) = res.try_into() {
                    return Ok(res);
                }
            }
            Err(ResolutionFailure::NotResolved {
                module_id,
                partial_res: None,
                unresolved: path_str.into(),
            })
        })
    }

    /// Used for reporting better errors.
    ///
    /// Returns whether the link resolved 'fully' in another namespace.
    /// 'fully' here means that all parts of the link resolved, not just some path segments.
    /// This returns the `Res` even if it was erroneous for some reason
    /// (such as having invalid URL fragments or being in the wrong namespace).
    pub(super) fn check_full_res(
        &mut self,
        ns: Namespace,
        path_str: &str,
        module_id: DefId,
        extra_fragment: &Option<String>,
    ) -> Option<Res> {
        // resolve() can't be used for macro namespace
        let result = match ns {
            Namespace::MacroNS => self.resolve_macro(path_str, module_id).map_err(ErrorKind::from),
            Namespace::TypeNS | Namespace::ValueNS => {
                todo!();
                //self.resolve(path_str, ns, module_id, extra_fragment).map(|(res, _)| res)
            }
        };

        let res = match result {
            Ok(res) => Some(res),
            Err(ErrorKind::Resolve(box kind)) => kind.full_res(),
            Err(ErrorKind::AnchorFailure(AnchorFailure::RustdocAnchorConflict(res))) => Some(res),
            Err(ErrorKind::AnchorFailure(AnchorFailure::MultipleAnchors)) => None,
        };
        self.kind_side_channel.take().map(|(kind, id)| Res::Def(kind, id)).or(res)
    }
}

impl IntraLinkCrateLoader {
    /// This is the entry point for resolving an intra-doc link.
    ///
    /// FIXME(jynelson): this is way too many arguments
    fn resolve_link(
        &mut self,
        item: &Item,
        dox: &str,
        self_name: &Option<String>,
        parent_node: Option<DefId>,
        krate: CrateNum,
        ori_link: MarkdownLink,
    ) -> Option<LinkResult<EarlyRes>> {
        trace!("considering link '{}'", ori_link.link);

        let diag_info = DiagnosticInfo {
            item,
            dox,
            ori_link: &ori_link.link,
            link_range: ori_link.range.clone(),
        };

        match preprocess_link(&ori_link)? {
            Ok(x) => Some(self.resolve_link_inner(diag_info, x, dox, self_name, parent_node, krate, ori_link)),
            Err(err) => return Some(Err(err)),
        }
    }

    /// Helper so this function can use `?` for errors.
    fn resolve_link_inner(&mut self, diag_info: DiagnosticInfo<'_>,
        PreprocessingInfo { path_str, disambiguator, extra_fragment, link_text }: PreprocessingInfo,
        dox: &str,
        self_name: &Option<String>,
        parent_node: Option<DefId>,
        krate: CrateNum,
        ori_link: MarkdownLink,
    ) -> LinkResult<EarlyRes> {
            //     Ok(x) => x,
            //     Err(err) => {
            //         match err {
            //             PreprocessingError::Anchor(err) => anchor_failure(self.cx, diag_info, err),
            //             PreprocessingError::Disambiguator(range, msg) => {
            //                 disambiguator_error(self.cx, diag_info, range, &msg)
            //             }
            //             PreprocessingError::Resolution(err, path_str, disambiguator) => {
            //                 resolution_failure(
            //                     self,
            //                     diag_info,
            //                     &path_str,
            //                     disambiguator,
            //                     smallvec![err],
            //                 );
            //             }
            //         }
            //         return None;
            //     }
            // };
        let mut path_str = &*path_str;
        let item = &diag_info.item;

        // In order to correctly resolve intra-doc links we need to
        // pick a base AST node to work from.  If the documentation for
        // this module came from an inner comment (//!) then we anchor
        // our name resolution *inside* the module.  If, on the other
        // hand it was an outer comment (///) then we anchor the name
        // resolution in the parent module on the basis that the names
        // used are more likely to be intended to be parent names.  For
        // this, we set base_node to None for inner comments since
        // we've already pushed this node onto the resolution stack but
        // for outer comments we explicitly try and resolve against the
        // parent_node first.
        let base_node = if item.is_mod() && item.attrs.inner_docs {
            self.mod_ids.last().copied()
        } else {
            parent_node
        };

        let mut module_id = if let Some(id) = base_node {
            id
        } else {
            // This is a bug.
            debug!("attempting to resolve item without parent module: {}", path_str);
            return Err(LinkError::Resolution(
                ResolutionFailure::NoParentItem,
                path_str.to_string(),
                disambiguator,
            ));
        };

        let resolved_self;
        // replace `Self` with suitable item's parent name
        let is_lone_self = path_str == "Self";
        let is_lone_crate = path_str == "crate";
        if path_str.starts_with("Self::") || is_lone_self {
            if let Some(ref name) = self_name {
                if is_lone_self {
                    path_str = name;
                } else {
                    resolved_self = format!("{}::{}", name, &path_str[6..]);
                    path_str = &resolved_self;
                }
            }
        } else if path_str.starts_with("crate::") || is_lone_crate {
            // HACK(jynelson): rustc_resolve thinks that `crate` is the crate currently being documented.
            // But rustdoc wants it to mean the crate this item was originally present in.
            // To work around this, remove it and resolve relative to the crate root instead.
            // HACK(jynelson)(2): If we just strip `crate::` then suddenly primitives become ambiguous
            // (consider `crate::char`). Instead, change it to `self::`. This works because 'self' is now the crate root.
            // FIXME(#78696): This doesn't always work.
            if is_lone_crate {
                path_str = "self";
            } else {
                resolved_self = format!("self::{}", &path_str["crate::".len()..]);
                path_str = &resolved_self;
            }
            module_id = DefId { krate, index: CRATE_DEF_INDEX };
        }

        self.resolve_with_disambiguator_cached(
            ResolutionInfo {
                module_id,
                dis: disambiguator,
                path_str: path_str.to_owned(),
                extra_fragment: extra_fragment.map(String::from),
            },
            diag_info.clone(), // this struct should really be Copy, but Range is not :(
            matches!(ori_link.kind, LinkType::Reference | LinkType::Shortcut),
        )

        // TODO: move all this into the late pass
        // Check for a primitive which might conflict with a module
        // Report the ambiguity and require that the user specify which one they meant.
        // FIXME: could there ever be a primitive not in the type namespace?
        // if matches!(
        //     disambiguator,
        //     None | Some(Disambiguator::Namespace(Namespace::TypeNS) | Disambiguator::Primitive)
        // ) && !matches!(res, Res::Primitive(_))
        // {
        //     if let Some(prim) = resolve_primitive(path_str, TypeNS) {
        //         // `prim@char`
        //         if matches!(disambiguator, Some(Disambiguator::Primitive)) {
        //             if fragment.is_some() {
        //                 return Err(LinkError::Anchor(AnchorFailure::RustdocAnchorConflict(prim.into())));
        //             }
        //             res = prim.into();
        //             fragment = Some(prim.as_str().to_string());
        //         } else {
        //             // `[char]` when a `char` module is in scope
        //             let candidates = vec![res, prim.into()];
        //             return Err(LinkError::Ambiguous(candidates, path_str.to_string()));
        //         }
        //     }
        // }

        // let report_mismatch = |specified: Disambiguator, resolved: Disambiguator| {
        //     LinkError::DisambiguatorMismatch{
        //         specified,
        //         resolved,
        //     }
        // }; 
        //     // The resolved item did not match the disambiguator; give a better error than 'not found'
        //     let msg = format!("incompatible link kind for `{}`", path_str);
        //     let callback = |diag: &mut DiagnosticBuilder<'_>, sp| {
        //         let note = format!(
        //             "this link resolved to {} {}, which is not {} {}",
        //             resolved.article(),
        //             resolved.descr(),
        //             specified.article(),
        //             specified.descr()
        //         );
        //         diag.note(&note);
        //         suggest_disambiguator(resolved, diag, path_str, dox, sp, &ori_link.range);
        //     };
        //     report_diagnostic(self.cx.tcx, BROKEN_INTRA_DOC_LINKS, &msg, &diag_info, callback);
        // };

        // let verify = |kind: DefKind, id: DefId| {
        //     let (kind, id) = self.kind_side_channel.take().unwrap_or((kind, id));
        //     debug!("intra-doc link to {} resolved to {:?} (id: {:?})", path_str, res, id);

        //     // Disallow e.g. linking to enums with `struct@`
        //     debug!("saw kind {:?} with disambiguator {:?}", kind, disambiguator);
        //     match (kind, disambiguator) {
        //         | (DefKind::Const | DefKind::ConstParam | DefKind::AssocConst | DefKind::AnonConst, Some(Disambiguator::Kind(DefKind::Const)))
        //         // NOTE: this allows 'method' to mean both normal functions and associated functions
        //         // This can't cause ambiguity because both are in the same namespace.
        //         | (DefKind::Fn | DefKind::AssocFn, Some(Disambiguator::Kind(DefKind::Fn)))
        //         // These are namespaces; allow anything in the namespace to match
        //         | (_, Some(Disambiguator::Namespace(_)))
        //         // If no disambiguator given, allow anything
        //         | (_, None)
        //         // All of these are valid, so do nothing
        //         => {}
        //         (actual, Some(Disambiguator::Kind(expected))) if actual == expected => {}
        //         (_, Some(specified @ Disambiguator::Kind(_) | specified @ Disambiguator::Primitive)) => {
        //             return Err(report_mismatch(specified, Disambiguator::Kind(kind)));
        //         }
        //     }

        //     Ok(())
        // };

        // let did = match res {
        //     Res::Primitive(prim) => {
        //         if let Some((kind, id)) = self.kind_side_channel.take() {
        //             verify(kind, id)?;
        //         } else {
        //             match disambiguator {
        //                 Some(Disambiguator::Primitive | Disambiguator::Namespace(_)) | None => {}
        //                 Some(other) => {
        //                     return Err(report_mismatch(other, Disambiguator::Primitive));
        //                 }
        //             }
        //         }
        //         // We're actually resolving an associated item of a primitive, so we need to
        //         // verify the disambiguator (if any) matches the type of the associated item.
        //         // This case should really follow the same flow as the `Res::Def` branch below,
        //         // but attempting to add a call to `clean::register_res` causes an ICE. @jyn514
        //         // thinks `register_res` is only needed for cross-crate re-exports, but Rust
        //         // doesn't allow statements like `use str::trim;`, making this a (hopefully)
        //         // valid omission. See https://github.com/rust-lang/rust/pull/80660#discussion_r551585677
        //         // for discussion on the matter.
        //         None
        //     }
        //     Res::Def(kind, id) => {
        //         verify(kind, id)?;
        //         Some(id)
        //     }
        // };
        // Ok(ItemLink { link: ori_link.link, link_text, did, fragment })
    }

    fn resolve_with_disambiguator_cached(
        &mut self,
        key: ResolutionInfo,
        diag: DiagnosticInfo<'_>,
        cache_resolution_failure: bool,
    ) -> LinkResult<EarlyRes> {
        // TODO: add back caching
        // // Try to look up both the result and the corresponding side channel value
        // if let Some(ref cached) = self.visited_links.get(&key) {
        //     match cached {
        //         Ok(cached) => {
        //             self.kind_side_channel.set(cached.side_channel.clone());
        //             return Ok(cached.res.clone());
        //         }
        //         Err(err) if cache_resolution_failure => return Err(err.clone()),
        //         Err(_) => {
        //             // Although we hit the cache and found a resolution error, this link isn't
        //             // supposed to cache those. Run link resolution again to emit the expected
        //             // resolution error.
        //         }
        //     }
        // }

        let result = self.resolve_with_disambiguator(&key, diag);

        // // Cache only if resolved successfully - don't silence duplicate errors
        // match &result {
        //     Ok(res) => {
        //         // Store result for the actual namespace
        //         self.visited_links.insert(
        //             key,
        //             Ok(CachedLink {
        //                 res: res.clone(),
        //                 side_channel: self.kind_side_channel.clone().into_inner(),
        //             }),
        //         );
        //     }
        //     Err(err) if cache_resolution_failure => {
        //         // For reference-style links we only want to report one resolution error
        //         // so let's cache them as well.
        //         self.visited_links.insert(key, Err(err.clone()));
        //     }
        //     Err(_) => {}
        // }
        result
    }

    /// After parsing the disambiguator, resolve the main part of the link.
    // FIXME(jynelson): wow this is just so much
    fn resolve_with_disambiguator(
        &mut self,
        key: &ResolutionInfo,
        diag: DiagnosticInfo<'_>,
    ) -> LinkResult<EarlyRes> {
        let disambiguator = key.dis;
        let path_str = &key.path_str;
        let base_node = key.module_id;
        let extra_fragment = &key.extra_fragment;

        match disambiguator.map(Disambiguator::ns) {
            Some(expected_ns @ (ValueNS | TypeNS)) => {
                let mut result = self.resolve(path_str, expected_ns, base_node, extra_fragment);
                if let Err(LinkError::Resolution(ref mut kind, _, _)) = &mut result {
                    // We only looked in one namespace. Try to give a better error if possible.
                    if kind.full_res().is_none() {
                        let other_ns = if expected_ns == ValueNS { TypeNS } else { ValueNS };
                        // FIXME: really it should be `resolution_failure` that does this, not `resolve_with_disambiguator`
                        // See https://github.com/rust-lang/rust/pull/76955#discussion_r493953382 for a good approach
                        for &new_ns in &[other_ns, MacroNS] {
                            if let Some(res) =
                                self.check_full_res(new_ns, path_str, base_node, extra_fragment)
                            {
                                *kind = ResolutionFailure::WrongNamespace { res, expected_ns };
                                break;
                            }
                        }
                    }
                }
                result
            }
            None => {
                // Try everything!
                let mut candidates = PerNS {
                    macro_ns: self
                        .resolve_macro(path_str, base_node)
                        .map(|res| EarlyRes::Resolved(res, extra_fragment.clone())),
                    type_ns: match self.resolve(path_str, TypeNS, base_node, extra_fragment) {
                        Ok(res) => {
                            debug!("got res in TypeNS: {:?}", res);
                            Ok(res)
                        }
                        Err(LinkError::Resolution(kind, _, _)) => Err(kind),
                        Err(other) => return Err(other),
                    },
                    value_ns: match self.resolve(path_str, ValueNS, base_node, extra_fragment) {
                        Ok(EarlyRes::Resolved(res, fragment)) => {
                            // Constructors are picked up in the type namespace.
                            match res {
                                Res::Def(DefKind::Ctor(..), _) => {
                                    Err(ResolutionFailure::WrongNamespace { res, expected_ns: TypeNS })
                                }
                                _ => {
                                    let (res, fragment) = match (fragment, extra_fragment.clone()) {
                                        (Some(fragment), Some(_)) => {
                                            // Shouldn't happen but who knows?
                                            (res, Some(fragment))
                                        }
                                        (fragment, None) | (None, fragment) => (res, fragment),
                                    };
                                    Ok(EarlyRes::Resolved(res, fragment))
                                }
                            }
                        }
                        Ok(other) => Ok(other),
                        Err(LinkError::Resolution(kind, _, _)) => Err(kind),
                        Err(other) => return Err(other),
                    }
                };

                let len = candidates.iter().filter(|res| res.is_ok()).count();

                if len == 0 {
                    return Err(LinkError::Resolution(
                        candidates.into_iter().filter_map(|res| res.err()).collect(),
                        path_str.to_string(),
                        disambiguator,
                    ));
                }

                if len == 1 {
                    Some(candidates.into_iter().filter_map(|res| res.ok()).next().unwrap())
                } else if len == 2 && is_derive_trait_collision(&candidates) {
                    Some(candidates.type_ns.unwrap())
                } else {
                    if is_derive_trait_collision(&candidates) {
                        candidates.macro_ns = Err(ResolutionFailure::Dummy);
                    }
                    // If we're reporting an ambiguity, don't mention the namespaces that failed
                    let candidates = candidates.map(|candidate| candidate.ok().map(|(res, _)| res));
                    Err(LinkError::Ambiguous(candidates, path_str.to_string()))
                }
            }
            Some(MacroNS) => {
                match self.resolve_macro(path_str, base_node) {
                    Ok(res) => Some((res, extra_fragment.clone())),
                    Err(mut kind) => {
                        // `resolve_macro` only looks in the macro namespace. Try to give a better error if possible.
                        for &ns in &[TypeNS, ValueNS] {
                            if let Some(res) =
                                self.check_full_res(ns, path_str, base_node, extra_fragment)
                            {
                                kind =
                                    ResolutionFailure::WrongNamespace { res, expected_ns: MacroNS };
                                break;
                            }
                        }
                        resolution_failure(self, diag, path_str, disambiguator, smallvec![kind]);
                        None
                    }
                }
            }
        }
    }
}
