use super::*;

pub(super) struct LinkCollector<'a, 'tcx> {
    pub(super) cx: &'a mut DocContext<'tcx>,
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
    visited_links: FxHashMap<ResolutionInfo, Option<CachedLink>>,
}

impl<'a, 'tcx> DocFolder for LinkCollector<'a, 'tcx> {
    fn fold_item(&mut self, item: Item) -> Option<Item> {
        use rustc_middle::ty::DefIdTree;

        let parent_node = if item.is_fake() {
            None
        } else {
            find_nearest_parent_module(self.cx.tcx, item.def_id)
        };

        if parent_node.is_some() {
            trace!("got parent node for {:?} {:?}, id {:?}", item.type_(), item.name, item.def_id);
        }

        // find item's parent to resolve `Self` in item's docs below
        debug!("looking for the `Self` type");
        let self_id = if item.is_fake() {
            None
        // Checking if the item is a field in an enum variant
        } else if (matches!(self.cx.tcx.def_kind(item.def_id), DefKind::Field)
            && matches!(
                self.cx.tcx.def_kind(self.cx.tcx.parent(item.def_id).unwrap()),
                DefKind::Variant
            ))
        {
            self.cx.tcx.parent(item.def_id).and_then(|item_id| self.cx.tcx.parent(item_id))
        } else if matches!(
            self.cx.tcx.def_kind(item.def_id),
            DefKind::AssocConst
                | DefKind::AssocFn
                | DefKind::AssocTy
                | DefKind::Variant
                | DefKind::Field
        ) {
            self.cx.tcx.parent(item.def_id)
        // HACK(jynelson): `clean` marks associated types as `TypedefItem`, not as `AssocTypeItem`.
        // Fixing this breaks `fn render_deref_methods`.
        // As a workaround, see if the parent of the item is an `impl`; if so this must be an associated item,
        // regardless of what rustdoc wants to call it.
        } else if let Some(parent) = self.cx.tcx.parent(item.def_id) {
            let parent_kind = self.cx.tcx.def_kind(parent);
            Some(if parent_kind == DefKind::Impl { parent } else { item.def_id })
        } else {
            Some(item.def_id)
        };

        // FIXME(jynelson): this shouldn't go through stringification, rustdoc should just use the DefId directly
        let self_name = self_id.and_then(|self_id| {
            if matches!(self.cx.tcx.def_kind(self_id), DefKind::Impl) {
                // using `ty.to_string()` (or any variant) has issues with raw idents
                let ty = self.cx.tcx.type_of(self_id);
                let name = match ty.kind() {
                    ty::Adt(def, _) => Some(self.cx.tcx.item_name(def.did).to_string()),
                    other if other.is_primitive() => Some(ty.to_string()),
                    _ => None,
                };
                debug!("using type_of(): {:?}", name);
                name
            } else {
                let name = self.cx.tcx.opt_item_name(self_id).map(|sym| sym.to_string());
                debug!("using item_name(): {:?}", name);
                name
            }
        });

        if item.is_mod() && item.attrs.inner_docs {
            self.mod_ids.push(item.def_id);
        }

        // We want to resolve in the lexical scope of the documentation.
        // In the presence of re-exports, this is not the same as the module of the item.
        // Rather than merging all documentation into one, resolve it one attribute at a time
        // so we know which module it came from.
        for (parent_module, doc) in item.attrs.collapsed_doc_value_by_module_level() {
            debug!("combined_docs={}", doc);

            let (krate, parent_node) = if let Some(id) = parent_module {
                (id.krate, Some(id))
            } else {
                (item.def_id.krate, parent_node)
            };
            // NOTE: if there are links that start in one crate and end in another, this will not resolve them.
            // This is a degenerate case and it's not supported by rustdoc.
            for md_link in markdown_links(&doc) {
                let link = self.resolve_link(&item, &doc, &self_name, parent_node, krate, md_link);
                if let Some(link) = link {
                    self.cx.cache.intra_doc_links.entry(item.def_id).or_default().push(link);
                }
            }
        }

        Some(if item.is_mod() {
            if !item.attrs.inner_docs {
                self.mod_ids.push(item.def_id);
            }

            let ret = self.fold_item_recur(item);
            self.mod_ids.pop();
            ret
        } else {
            self.fold_item_recur(item)
        })
    }
}

impl<'a, 'tcx> LinkCollector<'a, 'tcx> {
	pub(super) fn new(cx: &'a mut DocContext<'tcx>) -> Self {
		Self {
			cx,
			mod_ids: Vec::new(),
			kind_side_channel: Cell::new(None),
			visited_links: FxHashMap::default(),
		}
	}

    /// Given a full link, parse it as an [enum struct variant].
    ///
    /// In particular, this will return an error whenever there aren't three
    /// full path segments left in the link.
    ///
    /// [enum struct variant]: hir::VariantData::Struct
    fn variant_field(
        &self,
        (variant_res, variant_name, variant_field_name): (Res, Symbol, Symbol),
		module_id: DefId,
    ) -> Result<(Res, String), ErrorKind<'path>> {
        let tcx = self.cx.tcx;

        match variant_res {
            Res::Def(DefKind::Enum, did) => {
                if tcx
                    .inherent_impls(did)
                    .iter()
                    .flat_map(|imp| tcx.associated_items(*imp).in_definition_order())
                    .any(|item| item.ident.name == variant_name)
                {
                    // This is just to let `fold_item` know that this shouldn't be considered;
                    // it's a bug for the error to make it to the user
                    return Err(ResolutionFailure::Dummy.into());
                }
                match tcx.type_of(did).kind() {
                    ty::Adt(def, _) if def.is_enum() => {
                        if def.all_fields().any(|item| item.ident.name == variant_field_name) {
                            Ok((
                                variant_res,
                                format!(
                                    "variant.{}.field.{}",
                                    variant_name, variant_field_name
                                ),
                            ))
                        } else {
                            Err(ResolutionFailure::NotResolved {
                                module_id,
                                partial_res: Some(Res::Def(DefKind::Enum, def.did)),
                                unresolved: variant_field_name.into(),
                            }
                            .into())
                        }
                    }
                    _ => unreachable!(),
                }
            }
            _ => Err(ResolutionFailure::NotResolved {
                module_id,
                partial_res: Some(variant_res),
                unresolved: variant_name.into(),
            }
            .into()),
        }
    }

    /// Given a primitive type, try to resolve an associated item.
    fn resolve_primitive_associated_item(
        &self,
        prim_ty: PrimitiveType,
        ns: Namespace,
        item_name: Symbol,
    ) -> Option<(Res, String, Option<(DefKind, DefId)>)> {
        let tcx = self.cx.tcx;

        prim_ty.impls(tcx).into_iter().find_map(|&impl_| {
            tcx.associated_items(impl_)
                .find_by_name_and_namespace(tcx, Ident::with_dummy_span(item_name), ns, impl_)
                .map(|item| {
                    let kind = item.kind;
                    let out = match kind {
                        ty::AssocKind::Fn => "method",
                        ty::AssocKind::Const => "associatedconstant",
                        ty::AssocKind::Type => "associatedtype",
                    };
                    let fragment = format!("{}#{}.{}", prim_ty.as_str(), out, item_name);
                    (Res::Primitive(prim_ty), fragment, Some((kind.as_def_kind(), item.def_id)))
                })
        })
    }

    /// Returns:
    /// - None if no associated item was found
    /// - Some((_, _, Some(_))) if an item was found and should go through a side channel
    /// - Some((_, _, None)) otherwise
    fn resolve_associated_item(
        &mut self,
        root_res: Res,
        item_name: Symbol,
        ns: Namespace,
        module_id: DefId,
    ) -> Option<(Res, String, Option<(DefKind, DefId)>)> {
        let tcx = self.cx.tcx;

        match root_res {
            Res::Primitive(prim) => self.resolve_primitive_associated_item(prim, ns, item_name),
            Res::Def(
                DefKind::Struct
                | DefKind::Union
                | DefKind::Enum
                | DefKind::TyAlias
                | DefKind::ForeignTy,
                did,
            ) => {
                debug!("looking for associated item named {} for item {:?}", item_name, did);
                // Checks if item_name belongs to `impl SomeItem`
                let assoc_item = tcx
                    .inherent_impls(did)
                    .iter()
                    .flat_map(|&imp| {
                        tcx.associated_items(imp).find_by_name_and_namespace(
                            tcx,
                            Ident::with_dummy_span(item_name),
                            ns,
                            imp,
                        )
                    })
                    .map(|item| (item.kind, item.def_id))
                    // There should only ever be one associated item that matches from any inherent impl
                    .next()
                    // Check if item_name belongs to `impl SomeTrait for SomeItem`
                    // FIXME(#74563): This gives precedence to `impl SomeItem`:
                    // Although having both would be ambiguous, use impl version for compatibility's sake.
                    // To handle that properly resolve() would have to support
                    // something like [`ambi_fn`](<SomeStruct as SomeTrait>::ambi_fn)
                    .or_else(|| {
                        let kind =
                            resolve_associated_trait_item(did, module_id, item_name, ns, self.cx);
                        debug!("got associated item kind {:?}", kind);
                        kind
                    });

                if let Some((kind, id)) = assoc_item {
                    let out = match kind {
                        ty::AssocKind::Fn => "method",
                        ty::AssocKind::Const => "associatedconstant",
                        ty::AssocKind::Type => "associatedtype",
                    };
                    // HACK(jynelson): `clean` expects the type, not the associated item
                    // but the disambiguator logic expects the associated item.
                    // Store the kind in a side channel so that only the disambiguator logic looks at it.
                    return Some((
                        root_res,
                        format!("{}.{}", out, item_name),
                        Some((kind.as_def_kind(), id)),
                    ));
                }

                if ns != Namespace::ValueNS {
                    return None;
                }
                debug!("looking for variants or fields named {} for {:?}", item_name, did);
                // FIXME: this doesn't really belong in `associated_item` (maybe `variant_field` is better?)
                // NOTE: it's different from variant_field because it resolves fields and variants,
                // not variant fields (2 path segments, not 3).
                let def = match tcx.type_of(did).kind() {
                    ty::Adt(def, _) => def,
                    _ => return None,
                };
                let field = if def.is_enum() {
                    def.all_fields().find(|item| item.ident.name == item_name)
                } else {
                    def.non_enum_variant().fields.iter().find(|item| item.ident.name == item_name)
                }?;
                let kind = if def.is_enum() { DefKind::Variant } else { DefKind::Field };
                Some((
                    root_res,
                    format!(
                        "{}.{}",
                        if def.is_enum() { "variant" } else { "structfield" },
                        field.ident
                    ),
                    Some((kind, field.did)),
                ))
            }
            Res::Def(DefKind::Trait, did) => tcx
                .associated_items(did)
                .find_by_name_and_namespace(tcx, Ident::with_dummy_span(item_name), ns, did)
                .map(|item| {
                    let kind = match item.kind {
                        ty::AssocKind::Const => "associatedconstant",
                        ty::AssocKind::Type => "associatedtype",
                        ty::AssocKind::Fn => {
                            if item.defaultness.has_value() {
                                "method"
                            } else {
                                "tymethod"
                            }
                        }
                    };

                    let res = Res::Def(item.kind.as_def_kind(), item.def_id);
                    (res, format!("{}.{}", kind, item_name), None)
                }),
            _ => None,
        }
    }
}

/// Given an enum variant's res, return the res of its enum and the associated fragment.
fn handle_variant(
    cx: &DocContext<'_>,
    res: Res,
    extra_fragment: &Option<String>,
) -> Result<(Res, Option<String>), ErrorKind<'static>> {
    use rustc_middle::ty::DefIdTree;

    if extra_fragment.is_some() {
        return Err(ErrorKind::AnchorFailure(AnchorFailure::RustdocAnchorConflict(res)));
    }
    cx.tcx
        .parent(res.def_id())
        .map(|parent| {
            let parent_def = Res::Def(DefKind::Enum, parent);
            let variant = cx.tcx.expect_variant_res(res.as_hir_res().unwrap());
            (parent_def, Some(format!("variant.{}", variant.ident.name)))
        })
        .ok_or_else(|| ResolutionFailure::NoParentItem.into())
}
