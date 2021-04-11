//! This module implements [RFC 1946]: Intra-rustdoc-links
//!
//! [RFC 1946]: https://github.com/rust-lang/rfcs/blob/master/text/1946-intra-rustdoc-links.md

use rustc_ast as ast;
use rustc_data_structures::{fx::FxHashMap, stable_set::FxHashSet};
use rustc_errors::{Applicability, DiagnosticBuilder};
use rustc_expand::base::SyntaxExtensionKind;
use rustc_hir as hir;
use rustc_hir::def::{
    DefKind,
    Namespace::{self, *},
    PerNS,
};
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::TyCtxt;
use rustc_middle::{bug, ty};
use rustc_resolve::ParentScope;
use rustc_session::lint::Lint;
use rustc_span::hygiene::{MacroKind, SyntaxContext};
use rustc_span::symbol::{sym, Ident, Symbol};
use rustc_span::DUMMY_SP;
use smallvec::{smallvec, SmallVec};

use pulldown_cmark::LinkType;

use std::borrow::Cow;
use std::cell::Cell;
use std::convert::{TryFrom, TryInto};
use std::mem;
use std::ops::Range;

use crate::clean::{self, utils::find_nearest_parent_module, Crate, Item, ItemLink, PrimitiveType};
use crate::core::DocContext;
use crate::fold::DocFolder;
use crate::html::markdown::{markdown_links, MarkdownLink};
use crate::lint::{BROKEN_INTRA_DOC_LINKS, PRIVATE_INTRA_DOC_LINKS};
use crate::passes::Pass;

use super::span_of_attrs;

mod early;
crate use early::IntraLinkCrateLoader;

mod late;
use late::LinkCollector;

crate const COLLECT_INTRA_DOC_LINKS: Pass = Pass {
    name: "collect-intra-doc-links",
    run: collect_intra_doc_links,
    description: "resolves intra-doc links",
};

fn collect_intra_doc_links(krate: Crate, cx: &mut DocContext<'_>) -> Crate {
    LinkCollector::new(cx).fold_crate(krate)
}

/// Top-level errors emitted by this pass.
enum ErrorKind<'a> {
    Resolve(Box<ResolutionFailure<'a>>),
    AnchorFailure(AnchorFailure),
}

impl<'a> From<ResolutionFailure<'a>> for ErrorKind<'a> {
    fn from(err: ResolutionFailure<'a>) -> Self {
        ErrorKind::Resolve(box err)
    }
}

crate enum EarlyResult {
    Resolved(Res, Option<String>),
    Unresolved(UnresolvedLink),
    UnresolvedVariant(Res),
    Error(ErrorKind<'static>),
}

crate struct UnresolvedLink {
    /// The resolution for all path segments excluding the last.
    ///
    /// For example, in `[a::b::c]`, it will hold the Res for `a::b`.
    /// This is used for `resolve_associated_item`.
    ty_res: Option<Res>,
    /// The resolution for all path segments excluding the last two.
    ///
    /// For example, in `[a::b::c]`, it will hold the Res for `a`.
    /// This is used for `variant_field`.
    variant_res: Option<Res>,
    /* TODO */
}

#[derive(Copy, Clone, Debug, Hash)]
enum Res {
    Def(DefKind, DefId),
    Primitive(PrimitiveType),
}

type ResolveRes = rustc_hir::def::Res<rustc_ast::NodeId>;

impl Res {
    fn descr(self) -> &'static str {
        match self {
            Res::Def(kind, id) => ResolveRes::Def(kind, id).descr(),
            Res::Primitive(_) => "builtin type",
        }
    }

    fn article(self) -> &'static str {
        match self {
            Res::Def(kind, id) => ResolveRes::Def(kind, id).article(),
            Res::Primitive(_) => "a",
        }
    }

    fn name(self, tcx: TyCtxt<'_>) -> String {
        match self {
            Res::Def(_, id) => tcx.item_name(id).to_string(),
            Res::Primitive(prim) => prim.as_str().to_string(),
        }
    }

    fn def_id(self) -> DefId {
        self.opt_def_id().expect("called def_id() on a primitive")
    }

    fn opt_def_id(self) -> Option<DefId> {
        match self {
            Res::Def(_, id) => Some(id),
            Res::Primitive(_) => None,
        }
    }

    fn as_hir_res(self) -> Option<rustc_hir::def::Res> {
        match self {
            Res::Def(kind, id) => Some(rustc_hir::def::Res::Def(kind, id)),
            // FIXME: maybe this should handle the subset of PrimitiveType that fits into hir::PrimTy?
            Res::Primitive(_) => None,
        }
    }
}

impl TryFrom<ResolveRes> for Res {
    type Error = ();

    fn try_from(res: ResolveRes) -> Result<Self, ()> {
        use rustc_hir::def::Res::*;
        match res {
            Def(kind, id) => Ok(Res::Def(kind, id)),
            PrimTy(prim) => Ok(Res::Primitive(PrimitiveType::from_hir(prim))),
            // e.g. `#[derive]`
            NonMacroAttr(..) | Err => Result::Err(()),
            other => bug!("unrecognized res {:?}", other),
        }
    }
}

/// A link failed to resolve.
#[derive(Debug)]
enum ResolutionFailure<'a> {
    /// This resolved, but with the wrong namespace.
    WrongNamespace {
        /// What the link resolved to.
        res: Res,
        /// The expected namespace for the resolution, determined from the link's disambiguator.
        ///
        /// E.g., for `[fn@Result]` this is [`Namespace::ValueNS`],
        /// even though `Result`'s actual namespace is [`Namespace::TypeNS`].
        expected_ns: Namespace,
    },
    /// The link failed to resolve. [`resolution_failure`] should look to see if there's
    /// a more helpful error that can be given.
    NotResolved {
        /// The scope the link was resolved in.
        module_id: DefId,
        /// If part of the link resolved, this has the `Res`.
        ///
        /// In `[std::io::Error::x]`, `std::io::Error` would be a partial resolution.
        partial_res: Option<Res>,
        /// The remaining unresolved path segments.
        ///
        /// In `[std::io::Error::x]`, `x` would be unresolved.
        unresolved: Cow<'a, str>,
    },
    /// This happens when rustdoc can't determine the parent scope for an item.
    /// It is always a bug in rustdoc.
    NoParentItem,
    /// This link has malformed generic parameters; e.g., the angle brackets are unbalanced.
    MalformedGenerics(MalformedGenerics),
    /// Used to communicate that this should be ignored, but shouldn't be reported to the user.
    ///
    /// This happens when there is no disambiguator and one of the namespaces
    /// failed to resolve.
    Dummy,
}

#[derive(Debug)]
enum MalformedGenerics {
    /// This link has unbalanced angle brackets.
    ///
    /// For example, `Vec<T` should trigger this, as should `Vec<T>>`.
    UnbalancedAngleBrackets,
    /// The generics are not attached to a type.
    ///
    /// For example, `<T>` should trigger this.
    ///
    /// This is detected by checking if the path is empty after the generics are stripped.
    MissingType,
    /// The link uses fully-qualified syntax, which is currently unsupported.
    ///
    /// For example, `<Vec as IntoIterator>::into_iter` should trigger this.
    ///
    /// This is detected by checking if ` as ` (the keyword `as` with spaces around it) is inside
    /// angle brackets.
    HasFullyQualifiedSyntax,
    /// The link has an invalid path separator.
    ///
    /// For example, `Vec:<T>:new()` should trigger this. Note that `Vec:new()` will **not**
    /// trigger this because it has no generics and thus [`strip_generics_from_path`] will not be
    /// called.
    ///
    /// Note that this will also **not** be triggered if the invalid path separator is inside angle
    /// brackets because rustdoc mostly ignores what's inside angle brackets (except for
    /// [`HasFullyQualifiedSyntax`](MalformedGenerics::HasFullyQualifiedSyntax)).
    ///
    /// This is detected by checking if there is a colon followed by a non-colon in the link.
    InvalidPathSeparator,
    /// The link has too many angle brackets.
    ///
    /// For example, `Vec<<T>>` should trigger this.
    TooManyAngleBrackets,
    /// The link has empty angle brackets.
    ///
    /// For example, `Vec<>` should trigger this.
    EmptyAngleBrackets,
}

impl ResolutionFailure<'a> {
    /// This resolved fully (not just partially) but is erroneous for some other reason
    ///
    /// Returns the full resolution of the link, if present.
    fn full_res(&self) -> Option<Res> {
        match self {
            Self::WrongNamespace { res, expected_ns: _ } => Some(*res),
            _ => None,
        }
    }
}

enum AnchorFailure {
    /// User error: `[std#x#y]` is not valid
    MultipleAnchors,
    /// The anchor provided by the user conflicts with Rustdoc's generated anchor.
    ///
    /// This is an unfortunate state of affairs. Not every item that can be
    /// linked to has its own page; sometimes it is a subheading within a page,
    /// like for associated items. In those cases, rustdoc uses an anchor to
    /// link to the subheading. Since you can't have two anchors for the same
    /// link, Rustdoc disallows having a user-specified anchor.
    ///
    /// Most of the time this is fine, because you can just link to the page of
    /// the item if you want to provide your own anchor. For primitives, though,
    /// rustdoc uses the anchor as a side channel to know which page to link to;
    /// it doesn't show up in the generated link. Ideally, rustdoc would remove
    /// this limitation, allowing you to link to subheaders on primitives.
    RustdocAnchorConflict(Res),
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct ResolutionInfo {
    module_id: DefId,
    dis: Option<Disambiguator>,
    path_str: String,
    extra_fragment: Option<String>,
}

#[derive(Clone)]
struct DiagnosticInfo<'a> {
    item: &'a Item,
    dox: &'a str,
    ori_link: &'a str,
    link_range: Range<usize>,
}

#[derive(Clone, Debug, Hash)]
struct CachedLink {
    pub res: (Res, Option<String>),
    pub side_channel: Option<(DefKind, DefId)>,
}

/// Look to see if a resolved item has an associated item named `item_name`.
///
/// Given `[std::io::Error::source]`, where `source` is unresolved, this would
/// find `std::error::Error::source` and return
/// `<io::Error as error::Error>::source`.
fn resolve_associated_trait_item(
    did: DefId,
    module: DefId,
    item_name: Symbol,
    ns: Namespace,
    cx: &mut DocContext<'_>,
) -> Option<(ty::AssocKind, DefId)> {
    // FIXME: this should also consider blanket impls (`impl<T> X for T`). Unfortunately
    // `get_auto_trait_and_blanket_impls` is broken because the caching behavior is wrong. In the
    // meantime, just don't look for these blanket impls.

    // Next consider explicit impls: `impl MyTrait for MyType`
    // Give precedence to inherent impls.
    let traits = traits_implemented_by(cx, did, module);
    debug!("considering traits {:?}", traits);
    let mut candidates = traits.iter().filter_map(|&trait_| {
        cx.tcx
            .associated_items(trait_)
            .find_by_name_and_namespace(cx.tcx, Ident::with_dummy_span(item_name), ns, trait_)
            .map(|assoc| (assoc.kind, assoc.def_id))
    });
    // FIXME(#74563): warn about ambiguity
    debug!("the candidates were {:?}", candidates.clone().collect::<Vec<_>>());
    candidates.next()
}

/// Given a type, return all traits in scope in `module` implemented by that type.
///
/// NOTE: this cannot be a query because more traits could be available when more crates are compiled!
/// So it is not stable to serialize cross-crate.
fn traits_implemented_by(cx: &mut DocContext<'_>, type_: DefId, module: DefId) -> FxHashSet<DefId> {
    let mut resolver = cx.resolver.borrow_mut();
    let in_scope_traits = cx.module_trait_cache.entry(module).or_insert_with(|| {
        resolver.access(|resolver| {
            let parent_scope = &ParentScope::module(resolver.get_module(module), resolver);
            resolver
                .traits_in_scope(None, parent_scope, SyntaxContext::root(), None)
                .into_iter()
                .map(|candidate| candidate.def_id)
                .collect()
        })
    });

    let tcx = cx.tcx;
    let ty = tcx.type_of(type_);
    let iter = in_scope_traits.iter().flat_map(|&trait_| {
        trace!("considering explicit impl for trait {:?}", trait_);

        // Look at each trait implementation to see if it's an impl for `did`
        tcx.find_map_relevant_impl(trait_, ty, |impl_| {
            let trait_ref = tcx.impl_trait_ref(impl_).expect("this is not an inherent impl");
            // Check if these are the same type.
            let impl_type = trait_ref.self_ty();
            trace!(
                "comparing type {} with kind {:?} against type {:?}",
                impl_type,
                impl_type.kind(),
                type_
            );
            // Fast path: if this is a primitive simple `==` will work
            let saw_impl = impl_type == ty
                || match impl_type.kind() {
                    // Check if these are the same def_id
                    ty::Adt(def, _) => {
                        debug!("adt def_id: {:?}", def.did);
                        def.did == type_
                    }
                    ty::Foreign(def_id) => *def_id == type_,
                    _ => false,
                };

            if saw_impl { Some(trait_) } else { None }
        })
    });
    iter.collect()
}

/// Check for resolve collisions between a trait and its derive.
///
/// These are common and we should just resolve to the trait in that case.
fn is_derive_trait_collision<T>(ns: &PerNS<Result<(Res, T), ResolutionFailure<'_>>>) -> bool {
    matches!(
        *ns,
        PerNS {
            type_ns: Ok((Res::Def(DefKind::Trait, _), _)),
            macro_ns: Ok((Res::Def(DefKind::Macro(MacroKind::Derive), _), _)),
            ..
        }
    )
}

enum PreprocessingError<'a> {
    Anchor(AnchorFailure),
    Disambiguator(Range<usize>, String),
    Resolution(ResolutionFailure<'a>, String, Option<Disambiguator>),
}

impl From<AnchorFailure> for PreprocessingError<'_> {
    fn from(err: AnchorFailure) -> Self {
        Self::Anchor(err)
    }
}

struct PreprocessingInfo {
    path_str: String,
    disambiguator: Option<Disambiguator>,
    extra_fragment: Option<String>,
    link_text: String,
}

/// Returns:
/// - `None` if the link should be ignored.
/// - `Some(Err)` if the link should emit an error
/// - `Some(Ok)` if the link is valid
///
/// `link_buffer` is needed for lifetime reasons; it will always be overwritten and the contents ignored.
fn preprocess_link<'a>(
    ori_link: &'a MarkdownLink,
) -> Option<Result<PreprocessingInfo, PreprocessingError<'a>>> {
    // [] is mostly likely not supposed to be a link
    if ori_link.link.is_empty() {
        return None;
    }

    // Bail early for real links.
    if ori_link.link.contains('/') {
        return None;
    }

    let stripped = ori_link.link.replace("`", "");
    let mut parts = stripped.split('#');

    let link = parts.next().unwrap();
    if link.trim().is_empty() {
        // This is an anchor to an element of the current page, nothing to do in here!
        return None;
    }
    let extra_fragment = parts.next();
    if parts.next().is_some() {
        // A valid link can't have multiple #'s
        return Some(Err(AnchorFailure::MultipleAnchors.into()));
    }

    // Parse and strip the disambiguator from the link, if present.
    let (path_str, disambiguator) = match Disambiguator::from_str(&link) {
        Ok(Some((d, path))) => (path.trim(), Some(d)),
        Ok(None) => (link.trim(), None),
        Err((err_msg, relative_range)) => {
            // Only report error if we would not have ignored this link. See issue #83859.
            if !should_ignore_link_with_disambiguators(link) {
                let no_backticks_range = range_between_backticks(&ori_link);
                let disambiguator_range = (no_backticks_range.start + relative_range.start)
                    ..(no_backticks_range.start + relative_range.end);
                return Some(Err(PreprocessingError::Disambiguator(disambiguator_range, err_msg)));
            } else {
                return None;
            }
        }
    };

    if should_ignore_link(path_str) {
        return None;
    }

    // We stripped `()` and `!` when parsing the disambiguator.
    // Add them back to be displayed, but not prefix disambiguators.
    let link_text =
        disambiguator.map(|d| d.display_for(path_str)).unwrap_or_else(|| path_str.to_owned());

    // Strip generics from the path.
    let path_str = if path_str.contains(['<', '>'].as_slice()) {
        match strip_generics_from_path(&path_str) {
            Ok(path) => path,
            Err(err_kind) => {
                debug!("link has malformed generics: {}", path_str);
                return Some(Err(PreprocessingError::Resolution(
                    err_kind,
                    path_str.to_owned(),
                    disambiguator,
                )));
            }
        }
    } else {
        path_str.to_owned()
    };

    // Sanity check to make sure we don't have any angle brackets after stripping generics.
    assert!(!path_str.contains(['<', '>'].as_slice()));

    // The link is not an intra-doc link if it still contains spaces after stripping generics.
    if path_str.contains(' ') {
        return None;
    }

    Some(Ok(PreprocessingInfo {
        path_str,
        disambiguator,
        extra_fragment: extra_fragment.map(String::from),
        link_text,
    }))
}

/// Get the section of a link between the backticks,
/// or the whole link if there aren't any backticks.
///
/// For example:
///
/// ```text
/// [`Foo`]
///   ^^^
/// ```
fn range_between_backticks(ori_link: &MarkdownLink) -> Range<usize> {
    let after_first_backtick_group = ori_link.link.bytes().position(|b| b != b'`').unwrap_or(0);
    let before_second_backtick_group = ori_link
        .link
        .bytes()
        .skip(after_first_backtick_group)
        .position(|b| b == b'`')
        .unwrap_or(ori_link.link.len());
    (ori_link.range.start + after_first_backtick_group)
        ..(ori_link.range.start + before_second_backtick_group)
}

/// Returns true if we should ignore `link` due to it being unlikely
/// that it is an intra-doc link. `link` should still have disambiguators
/// if there were any.
///
/// The difference between this and [`should_ignore_link()`] is that this
/// check should only be used on links that still have disambiguators.
fn should_ignore_link_with_disambiguators(link: &str) -> bool {
    link.contains(|ch: char| !(ch.is_alphanumeric() || ":_<>, !*&;@()".contains(ch)))
}

/// Returns true if we should ignore `path_str` due to it being unlikely
/// that it is an intra-doc link.
fn should_ignore_link(path_str: &str) -> bool {
    path_str.contains(|ch: char| !(ch.is_alphanumeric() || ":_<>, !*&;".contains(ch)))
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
/// Disambiguators for a link.
enum Disambiguator {
    /// `prim@`
    ///
    /// This is buggy, see <https://github.com/rust-lang/rust/pull/77875#discussion_r503583103>
    Primitive,
    /// `struct@` or `f()`
    Kind(DefKind),
    /// `type@`
    Namespace(Namespace),
}

impl Disambiguator {
    /// The text that should be displayed when the path is rendered as HTML.
    ///
    /// NOTE: `path` is not the original link given by the user, but a name suitable for passing to `resolve`.
    fn display_for(&self, path: &str) -> String {
        match self {
            // FIXME: this will have different output if the user had `m!()` originally.
            Self::Kind(DefKind::Macro(MacroKind::Bang)) => format!("{}!", path),
            Self::Kind(DefKind::Fn) => format!("{}()", path),
            _ => path.to_owned(),
        }
    }

    /// Given a link, parse and return `(disambiguator, path_str)`.
    ///
    /// This returns `Ok(Some(...))` if a disambiguator was found,
    /// `Ok(None)` if no disambiguator was found, or `Err(...)`
    /// if there was a problem with the disambiguator.
    fn from_str(link: &str) -> Result<Option<(Self, &str)>, (String, Range<usize>)> {
        use Disambiguator::{Kind, Namespace as NS, Primitive};

        if let Some(idx) = link.find('@') {
            let (prefix, rest) = link.split_at(idx);
            let d = match prefix {
                "struct" => Kind(DefKind::Struct),
                "enum" => Kind(DefKind::Enum),
                "trait" => Kind(DefKind::Trait),
                "union" => Kind(DefKind::Union),
                "module" | "mod" => Kind(DefKind::Mod),
                "const" | "constant" => Kind(DefKind::Const),
                "static" => Kind(DefKind::Static),
                "function" | "fn" | "method" => Kind(DefKind::Fn),
                "derive" => Kind(DefKind::Macro(MacroKind::Derive)),
                "type" => NS(Namespace::TypeNS),
                "value" => NS(Namespace::ValueNS),
                "macro" => NS(Namespace::MacroNS),
                "prim" | "primitive" => Primitive,
                _ => return Err((format!("unknown disambiguator `{}`", prefix), 0..idx)),
            };
            Ok(Some((d, &rest[1..])))
        } else {
            let suffixes = [
                ("!()", DefKind::Macro(MacroKind::Bang)),
                ("()", DefKind::Fn),
                ("!", DefKind::Macro(MacroKind::Bang)),
            ];
            for &(suffix, kind) in &suffixes {
                if let Some(link) = link.strip_suffix(suffix) {
                    // Avoid turning `!` or `()` into an empty string
                    if !link.is_empty() {
                        return Ok(Some((Kind(kind), link)));
                    }
                }
            }
            Ok(None)
        }
    }

    fn from_res(res: Res) -> Self {
        match res {
            Res::Def(kind, _) => Disambiguator::Kind(kind),
            Res::Primitive(_) => Disambiguator::Primitive,
        }
    }

    /// Used for error reporting.
    fn suggestion(self) -> Suggestion {
        let kind = match self {
            Disambiguator::Primitive => return Suggestion::Prefix("prim"),
            Disambiguator::Kind(kind) => kind,
            Disambiguator::Namespace(_) => panic!("display_for cannot be used on namespaces"),
        };
        if kind == DefKind::Macro(MacroKind::Bang) {
            return Suggestion::Macro;
        } else if kind == DefKind::Fn || kind == DefKind::AssocFn {
            return Suggestion::Function;
        }

        let prefix = match kind {
            DefKind::Struct => "struct",
            DefKind::Enum => "enum",
            DefKind::Trait => "trait",
            DefKind::Union => "union",
            DefKind::Mod => "mod",
            DefKind::Const | DefKind::ConstParam | DefKind::AssocConst | DefKind::AnonConst => {
                "const"
            }
            DefKind::Static => "static",
            DefKind::Macro(MacroKind::Derive) => "derive",
            // Now handle things that don't have a specific disambiguator
            _ => match kind
                .ns()
                .expect("tried to calculate a disambiguator for a def without a namespace?")
            {
                Namespace::TypeNS => "type",
                Namespace::ValueNS => "value",
                Namespace::MacroNS => "macro",
            },
        };

        Suggestion::Prefix(prefix)
    }

    fn ns(self) -> Namespace {
        match self {
            Self::Namespace(n) => n,
            Self::Kind(k) => {
                k.ns().expect("only DefKinds with a valid namespace can be disambiguators")
            }
            Self::Primitive => TypeNS,
        }
    }

    fn article(self) -> &'static str {
        match self {
            Self::Namespace(_) => panic!("article() doesn't make sense for namespaces"),
            Self::Kind(k) => k.article(),
            Self::Primitive => "a",
        }
    }

    fn descr(self) -> &'static str {
        match self {
            Self::Namespace(n) => n.descr(),
            // HACK(jynelson): by looking at the source I saw the DefId we pass
            // for `expected.descr()` doesn't matter, since it's not a crate
            Self::Kind(k) => k.descr(DefId::local(hir::def_id::DefIndex::from_usize(0))),
            Self::Primitive => "builtin type",
        }
    }
}

/// A suggestion to show in a diagnostic.
enum Suggestion {
    /// `struct@`
    Prefix(&'static str),
    /// `f()`
    Function,
    /// `m!`
    Macro,
}

impl Suggestion {
    fn descr(&self) -> Cow<'static, str> {
        match self {
            Self::Prefix(x) => format!("prefix with `{}@`", x).into(),
            Self::Function => "add parentheses".into(),
            Self::Macro => "add an exclamation mark".into(),
        }
    }

    fn as_help(&self, path_str: &str) -> String {
        // FIXME: if this is an implied shortcut link, it's bad style to suggest `@`
        match self {
            Self::Prefix(prefix) => format!("{}@{}", prefix, path_str),
            Self::Function => format!("{}()", path_str),
            Self::Macro => format!("{}!", path_str),
        }
    }
}

/// Reports a diagnostic for an intra-doc link.
///
/// If no link range is provided, or the source span of the link cannot be determined, the span of
/// the entire documentation block is used for the lint. If a range is provided but the span
/// calculation fails, a note is added to the diagnostic pointing to the link in the markdown.
///
/// The `decorate` callback is invoked in all cases to allow further customization of the
/// diagnostic before emission. If the span of the link was able to be determined, the second
/// parameter of the callback will contain it, and the primary span of the diagnostic will be set
/// to it.
fn report_diagnostic(
    tcx: TyCtxt<'_>,
    lint: &'static Lint,
    msg: &str,
    DiagnosticInfo { item, ori_link: _, dox, link_range }: &DiagnosticInfo<'_>,
    decorate: impl FnOnce(&mut DiagnosticBuilder<'_>, Option<rustc_span::Span>),
) {
    let hir_id = match DocContext::as_local_hir_id(tcx, item.def_id) {
        Some(hir_id) => hir_id,
        None => {
            // If non-local, no need to check anything.
            info!("ignoring warning from parent crate: {}", msg);
            return;
        }
    };

    let attrs = &item.attrs;
    let sp = span_of_attrs(attrs).unwrap_or(item.span.inner());

    tcx.struct_span_lint_hir(lint, hir_id, sp, |lint| {
        let mut diag = lint.build(msg);

        let span = super::source_span_for_markdown_range(tcx, dox, link_range, attrs);

        if let Some(sp) = span {
            diag.set_span(sp);
        } else {
            // blah blah blah\nblah\nblah [blah] blah blah\nblah blah
            //                       ^     ~~~~
            //                       |     link_range
            //                       last_new_line_offset
            let last_new_line_offset = dox[..link_range.start].rfind('\n').map_or(0, |n| n + 1);
            let line = dox[last_new_line_offset..].lines().next().unwrap_or("");

            // Print the line containing the `link_range` and manually mark it with '^'s.
            diag.note(&format!(
                "the link appears in this line:\n\n{line}\n\
                     {indicator: <before$}{indicator:^<found$}",
                line = line,
                indicator = "",
                before = link_range.start - last_new_line_offset,
                found = link_range.len(),
            ));
        }

        decorate(&mut diag, span);

        diag.emit();
    });
}

/// Reports a link that failed to resolve.
///
/// This also tries to resolve any intermediate path segments that weren't
/// handled earlier. For example, if passed `Item::Crate(std)` and `path_str`
/// `std::io::Error::x`, this will resolve `std::io::Error`.
fn resolution_failure(
    collector: &mut LinkCollector<'_, '_>,
    diag_info: DiagnosticInfo<'_>,
    path_str: &str,
    disambiguator: Option<Disambiguator>,
    kinds: SmallVec<[ResolutionFailure<'_>; 3]>,
) {
    let tcx = collector.cx.tcx;
    report_diagnostic(
        tcx,
        BROKEN_INTRA_DOC_LINKS,
        &format!("unresolved link to `{}`", path_str),
        &diag_info,
        |diag, sp| {
            let item = |res: Res| format!("the {} `{}`", res.descr(), res.name(tcx),);
            let assoc_item_not_allowed = |res: Res| {
                let name = res.name(tcx);
                format!(
                    "`{}` is {} {}, not a module or type, and cannot have associated items",
                    name,
                    res.article(),
                    res.descr()
                )
            };
            // ignore duplicates
            let mut variants_seen = SmallVec::<[_; 3]>::new();
            for mut failure in kinds {
                let variant = std::mem::discriminant(&failure);
                if variants_seen.contains(&variant) {
                    continue;
                }
                variants_seen.push(variant);

                if let ResolutionFailure::NotResolved { module_id, partial_res, unresolved } =
                    &mut failure
                {
                    use DefKind::*;

                    let module_id = *module_id;
                    // FIXME(jynelson): this might conflict with my `Self` fix in #76467
                    // FIXME: maybe use itertools `collect_tuple` instead?
                    fn split(path: &str) -> Option<(&str, &str)> {
                        let mut splitter = path.rsplitn(2, "::");
                        splitter.next().and_then(|right| splitter.next().map(|left| (left, right)))
                    }

                    // Check if _any_ parent of the path gets resolved.
                    // If so, report it and say the first which failed; if not, say the first path segment didn't resolve.
                    let mut name = path_str;
                    'outer: loop {
                        let (start, end) = if let Some(x) = split(name) {
                            x
                        } else {
                            // avoid bug that marked [Quux::Z] as missing Z, not Quux
                            if partial_res.is_none() {
                                *unresolved = name.into();
                            }
                            break;
                        };
                        name = start;
                        for &ns in &[TypeNS, ValueNS, MacroNS] {
                            if let Some(res) =
                                collector.check_full_res(ns, &start, module_id, &None)
                            {
                                debug!("found partial_res={:?}", res);
                                *partial_res = Some(res);
                                *unresolved = end.into();
                                break 'outer;
                            }
                        }
                        *unresolved = end.into();
                    }

                    let last_found_module = match *partial_res {
                        Some(Res::Def(DefKind::Mod, id)) => Some(id),
                        None => Some(module_id),
                        _ => None,
                    };
                    // See if this was a module: `[path]` or `[std::io::nope]`
                    if let Some(module) = last_found_module {
                        let note = if partial_res.is_some() {
                            // Part of the link resolved; e.g. `std::io::nonexistent`
                            let module_name = tcx.item_name(module);
                            format!("no item named `{}` in module `{}`", unresolved, module_name)
                        } else {
                            // None of the link resolved; e.g. `Notimported`
                            format!("no item named `{}` in scope", unresolved)
                        };
                        if let Some(span) = sp {
                            diag.span_label(span, &note);
                        } else {
                            diag.note(&note);
                        }

                        // If the link has `::` in it, assume it was meant to be an intra-doc link.
                        // Otherwise, the `[]` might be unrelated.
                        // FIXME: don't show this for autolinks (`<>`), `()` style links, or reference links
                        if !path_str.contains("::") {
                            diag.help(r#"to escape `[` and `]` characters, add '\' before them like `\[` or `\]`"#);
                        }

                        continue;
                    }

                    // Otherwise, it must be an associated item or variant
                    let res = partial_res.expect("None case was handled by `last_found_module`");
                    let name = res.name(tcx);
                    let kind = match res {
                        Res::Def(kind, _) => Some(kind),
                        Res::Primitive(_) => None,
                    };
                    let path_description = if let Some(kind) = kind {
                        match kind {
                            Mod | ForeignMod => "inner item",
                            Struct => "field or associated item",
                            Enum | Union => "variant or associated item",
                            Variant
                            | Field
                            | Closure
                            | Generator
                            | AssocTy
                            | AssocConst
                            | AssocFn
                            | Fn
                            | Macro(_)
                            | Const
                            | ConstParam
                            | ExternCrate
                            | Use
                            | LifetimeParam
                            | Ctor(_, _)
                            | AnonConst => {
                                let note = assoc_item_not_allowed(res);
                                if let Some(span) = sp {
                                    diag.span_label(span, &note);
                                } else {
                                    diag.note(&note);
                                }
                                return;
                            }
                            Trait | TyAlias | ForeignTy | OpaqueTy | TraitAlias | TyParam
                            | Static => "associated item",
                            Impl | GlobalAsm => unreachable!("not a path"),
                        }
                    } else {
                        "associated item"
                    };
                    let note = format!(
                        "the {} `{}` has no {} named `{}`",
                        res.descr(),
                        name,
                        disambiguator.map_or(path_description, |d| d.descr()),
                        unresolved,
                    );
                    if let Some(span) = sp {
                        diag.span_label(span, &note);
                    } else {
                        diag.note(&note);
                    }

                    continue;
                }
                let note = match failure {
                    ResolutionFailure::NotResolved { .. } => unreachable!("handled above"),
                    ResolutionFailure::Dummy => continue,
                    ResolutionFailure::WrongNamespace { res, expected_ns } => {
                        if let Res::Def(kind, _) = res {
                            let disambiguator = Disambiguator::Kind(kind);
                            suggest_disambiguator(
                                disambiguator,
                                diag,
                                path_str,
                                diag_info.dox,
                                sp,
                                &diag_info.link_range,
                            )
                        }

                        format!(
                            "this link resolves to {}, which is not in the {} namespace",
                            item(res),
                            expected_ns.descr()
                        )
                    }
                    ResolutionFailure::NoParentItem => {
                        diag.level = rustc_errors::Level::Bug;
                        "all intra-doc links should have a parent item".to_owned()
                    }
                    ResolutionFailure::MalformedGenerics(variant) => match variant {
                        MalformedGenerics::UnbalancedAngleBrackets => {
                            String::from("unbalanced angle brackets")
                        }
                        MalformedGenerics::MissingType => {
                            String::from("missing type for generic parameters")
                        }
                        MalformedGenerics::HasFullyQualifiedSyntax => {
                            diag.note("see https://github.com/rust-lang/rust/issues/74563 for more information");
                            String::from("fully-qualified syntax is unsupported")
                        }
                        MalformedGenerics::InvalidPathSeparator => {
                            String::from("has invalid path separator")
                        }
                        MalformedGenerics::TooManyAngleBrackets => {
                            String::from("too many angle brackets")
                        }
                        MalformedGenerics::EmptyAngleBrackets => {
                            String::from("empty angle brackets")
                        }
                    },
                };
                if let Some(span) = sp {
                    diag.span_label(span, &note);
                } else {
                    diag.note(&note);
                }
            }
        },
    );
}

/// Report an anchor failure.
fn anchor_failure(cx: &DocContext<'_>, diag_info: DiagnosticInfo<'_>, failure: AnchorFailure) {
    let msg = match failure {
        AnchorFailure::MultipleAnchors => {
            format!("`{}` contains multiple anchors", diag_info.ori_link)
        }
        AnchorFailure::RustdocAnchorConflict(res) => format!(
            "`{}` contains an anchor, but links to {kind}s are already anchored",
            diag_info.ori_link,
            kind = res.descr(),
        ),
    };

    report_diagnostic(cx.tcx, BROKEN_INTRA_DOC_LINKS, &msg, &diag_info, |diag, sp| {
        if let Some(sp) = sp {
            diag.span_label(sp, "contains invalid anchor");
        }
    });
}

/// Report an error in the link disambiguator.
fn disambiguator_error(
    cx: &DocContext<'_>,
    mut diag_info: DiagnosticInfo<'_>,
    disambiguator_range: Range<usize>,
    msg: &str,
) {
    diag_info.link_range = disambiguator_range;
    report_diagnostic(cx.tcx, BROKEN_INTRA_DOC_LINKS, msg, &diag_info, |diag, _sp| {
        let msg = format!(
            "see https://doc.rust-lang.org/{}/rustdoc/linking-to-items-by-name.html#namespaces-and-disambiguators \
             for more info about disambiguators",
            crate::doc_rust_lang_org_channel(),
        );
        diag.note(&msg);
    });
}

/// Report an ambiguity error, where there were multiple possible resolutions.
fn ambiguity_error(
    cx: &DocContext<'_>,
    diag_info: DiagnosticInfo<'_>,
    path_str: &str,
    candidates: Vec<Res>,
) {
    let mut msg = format!("`{}` is ", path_str);

    match candidates.as_slice() {
        [first_def, second_def] => {
            msg += &format!(
                "both {} {} and {} {}",
                first_def.article(),
                first_def.descr(),
                second_def.article(),
                second_def.descr(),
            );
        }
        _ => {
            let mut candidates = candidates.iter().peekable();
            while let Some(res) = candidates.next() {
                if candidates.peek().is_some() {
                    msg += &format!("{} {}, ", res.article(), res.descr());
                } else {
                    msg += &format!("and {} {}", res.article(), res.descr());
                }
            }
        }
    }

    report_diagnostic(cx.tcx, BROKEN_INTRA_DOC_LINKS, &msg, &diag_info, |diag, sp| {
        if let Some(sp) = sp {
            diag.span_label(sp, "ambiguous link");
        } else {
            diag.note("ambiguous link");
        }

        for res in candidates {
            let disambiguator = Disambiguator::from_res(res);
            suggest_disambiguator(
                disambiguator,
                diag,
                path_str,
                diag_info.dox,
                sp,
                &diag_info.link_range,
            );
        }
    });
}

/// In case of an ambiguity or mismatched disambiguator, suggest the correct
/// disambiguator.
fn suggest_disambiguator(
    disambiguator: Disambiguator,
    diag: &mut DiagnosticBuilder<'_>,
    path_str: &str,
    dox: &str,
    sp: Option<rustc_span::Span>,
    link_range: &Range<usize>,
) {
    let suggestion = disambiguator.suggestion();
    let help = format!("to link to the {}, {}", disambiguator.descr(), suggestion.descr());

    if let Some(sp) = sp {
        let msg = if dox.bytes().nth(link_range.start) == Some(b'`') {
            format!("`{}`", suggestion.as_help(path_str))
        } else {
            suggestion.as_help(path_str)
        };

        diag.span_suggestion(sp, &help, msg, Applicability::MaybeIncorrect);
    } else {
        diag.help(&format!("{}: {}", help, suggestion.as_help(path_str)));
    }
}

/// Report a link from a public item to a private one.
fn privacy_error(cx: &DocContext<'_>, diag_info: &DiagnosticInfo<'_>, path_str: &str) {
    let sym;
    let item_name = match diag_info.item.name {
        Some(name) => {
            sym = name.as_str();
            &*sym
        }
        None => "<unknown>",
    };
    let msg =
        format!("public documentation for `{}` links to private item `{}`", item_name, path_str);

    report_diagnostic(cx.tcx, PRIVATE_INTRA_DOC_LINKS, &msg, diag_info, |diag, sp| {
        if let Some(sp) = sp {
            diag.span_label(sp, "this item is private");
        }

        let note_msg = if cx.render_options.document_private {
            "this link resolves only because you passed `--document-private-items`, but will break without"
        } else {
            "this link will resolve properly if you pass `--document-private-items`"
        };
        diag.note(note_msg);
    });
}

/// Resolve a primitive type or value.
fn resolve_primitive(path_str: &str, ns: Namespace) -> Option<Res> {
    if ns != TypeNS {
        return None;
    }
    use PrimitiveType::*;
    let prim = match path_str {
        "isize" => Isize,
        "i8" => I8,
        "i16" => I16,
        "i32" => I32,
        "i64" => I64,
        "i128" => I128,
        "usize" => Usize,
        "u8" => U8,
        "u16" => U16,
        "u32" => U32,
        "u64" => U64,
        "u128" => U128,
        "f32" => F32,
        "f64" => F64,
        "char" => Char,
        "bool" | "true" | "false" => Bool,
        "str" | "&str" => Str,
        // See #80181 for why these don't have symbols associated.
        "slice" => Slice,
        "array" => Array,
        "tuple" => Tuple,
        "unit" => Unit,
        "pointer" | "*const" | "*mut" => RawPointer,
        "reference" | "&" | "&mut" => Reference,
        "fn" => Fn,
        "never" | "!" => Never,
        _ => return None,
    };
    debug!("resolved primitives {:?}", prim);
    Some(Res::Primitive(prim))
}

fn strip_generics_from_path(path_str: &str) -> Result<String, ResolutionFailure<'static>> {
    let mut stripped_segments = vec![];
    let mut path = path_str.chars().peekable();
    let mut segment = Vec::new();

    while let Some(chr) = path.next() {
        match chr {
            ':' => {
                if path.next_if_eq(&':').is_some() {
                    let stripped_segment =
                        strip_generics_from_path_segment(mem::take(&mut segment))?;
                    if !stripped_segment.is_empty() {
                        stripped_segments.push(stripped_segment);
                    }
                } else {
                    return Err(ResolutionFailure::MalformedGenerics(
                        MalformedGenerics::InvalidPathSeparator,
                    ));
                }
            }
            '<' => {
                segment.push(chr);

                match path.next() {
                    Some('<') => {
                        return Err(ResolutionFailure::MalformedGenerics(
                            MalformedGenerics::TooManyAngleBrackets,
                        ));
                    }
                    Some('>') => {
                        return Err(ResolutionFailure::MalformedGenerics(
                            MalformedGenerics::EmptyAngleBrackets,
                        ));
                    }
                    Some(chr) => {
                        segment.push(chr);

                        while let Some(chr) = path.next_if(|c| *c != '>') {
                            segment.push(chr);
                        }
                    }
                    None => break,
                }
            }
            _ => segment.push(chr),
        }
        trace!("raw segment: {:?}", segment);
    }

    if !segment.is_empty() {
        let stripped_segment = strip_generics_from_path_segment(segment)?;
        if !stripped_segment.is_empty() {
            stripped_segments.push(stripped_segment);
        }
    }

    debug!("path_str: {:?}\nstripped segments: {:?}", path_str, &stripped_segments);

    let stripped_path = stripped_segments.join("::");

    if !stripped_path.is_empty() {
        Ok(stripped_path)
    } else {
        Err(ResolutionFailure::MalformedGenerics(MalformedGenerics::MissingType))
    }
}

fn strip_generics_from_path_segment(
    segment: Vec<char>,
) -> Result<String, ResolutionFailure<'static>> {
    let mut stripped_segment = String::new();
    let mut param_depth = 0;

    let mut latest_generics_chunk = String::new();

    for c in segment {
        if c == '<' {
            param_depth += 1;
            latest_generics_chunk.clear();
        } else if c == '>' {
            param_depth -= 1;
            if latest_generics_chunk.contains(" as ") {
                // The segment tries to use fully-qualified syntax, which is currently unsupported.
                // Give a helpful error message instead of completely ignoring the angle brackets.
                return Err(ResolutionFailure::MalformedGenerics(
                    MalformedGenerics::HasFullyQualifiedSyntax,
                ));
            }
        } else {
            if param_depth == 0 {
                stripped_segment.push(c);
            } else {
                latest_generics_chunk.push(c);
            }
        }
    }

    if param_depth == 0 {
        Ok(stripped_segment)
    } else {
        // The segment has unbalanced angle brackets, e.g. `Vec<T` or `Vec<T>>`
        Err(ResolutionFailure::MalformedGenerics(MalformedGenerics::UnbalancedAngleBrackets))
    }
}
