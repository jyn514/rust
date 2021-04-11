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
}

impl IntraLinkCrateLoader {
	crate fn new(resolver: Rc<RefCell<interface::BoxedResolver>>) -> Self {
		let crate_id = LocalDefId { local_def_index: CRATE_DEF_INDEX }.to_def_id();
		Self { current_mod: crate_id, resolver }
	}

    crate fn enter_resolver<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut Resolver<'_>) -> R,
    {
        self.resolver.borrow_mut().access(f)
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
            Err(()) => resolve_primitive(path_str, ns),
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
    ) -> EarlyResult {
        if let Some(res) = self.resolve_path(path_str, ns, module_id) {
            match res {
                // FIXME(#76467): make this fallthrough to lookup the associated
                // item a separate function.
                Res::Def(DefKind::AssocFn | DefKind::AssocConst, _) => assert_eq!(ns, ValueNS),
                Res::Def(DefKind::AssocTy, _) => assert_eq!(ns, TypeNS),
                Res::Def(DefKind::Variant, _) => {
                    return EarlyResult::UnresolvedVariant(res);
                }
                // Not a trait item; just return what we found.
                Res::Primitive(ty) => {
                    if extra_fragment.is_some() {
                        return EarlyResult::Error(ErrorKind::AnchorFailure(
                            AnchorFailure::RustdocAnchorConflict(res),
                        ));
                    }
                    return EarlyResult::Resolved(res, Some(ty.as_str().to_owned()));
                }
                _ => return EarlyResult::Resolved(res, extra_fragment.clone()),
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
                return EarlyResult::Error(ResolutionFailure::NotResolved {
                    module_id,
                    partial_res: None,
                    unresolved: item_str.into(),
                }.into());
            }
		};

        // FIXME(#83862): this arbitrarily gives precedence to primitives over modules to support
        // links to primitives when `#[doc(primitive)]` is present. It should give an ambiguity
        // error instead and special case *only* modules with `#[doc(primitive)]`, not all
        // primitives.
        let ty_res = resolve_primitive(&path_root, TypeNS)
            .or_else(|| self.resolve_path(&path_root, TypeNS, module_id));
		let variant_res = if ns == Namespace::ValueNS {
			self.variant_res(path_str, module_id)
		} else {
			None
		};
		EarlyResult::Unresolved(UnresolvedLink {
			ty_res, variant_res
		})
	}

	fn variant_res(&self, path_str: &str, module_id: DefId) -> Option<Res> {
		debug!("looking for enum variant {}", path_str);
		let mut split = path_str.rsplitn(3, "::");
		let (variant_field_str, variant_field_name) = split
			.next()
			.map(|f| (f, Symbol::intern(f)))
			.expect("fold_item should ensure link is non-empty");
		// we're not sure this is a variant at all, so use the full string
		// If there's no second component, the link looks like `[path]`.
		// So there's no partial res and we should say the whole link failed to resolve.
		let variant_str = split.next()?;
		let variant_name = Symbol::intern(variant_str);
		let path = split.next()?.to_owned();
		self
			.enter_resolver(|resolver| {
				resolver.resolve_str_path_error(DUMMY_SP, &path, TypeNS, module_id)
			})
			.and_then(|(_, res)| res.try_into())
			.ok()
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
