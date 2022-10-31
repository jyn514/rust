use rustdoc_types::{Crate, Id};
use syn::{Ident, Meta, NestedMeta, Lit};

use crate::features::{CollectedFeatures, Features, Status};
use std::collections::{BTreeSet, HashMap};
use std::fs;
use std::io::{BufReader, BufRead};
use std::path::{Path, PathBuf};

pub const PATH_STR: &str = "doc/unstable-book";

pub const COMPILER_FLAGS_DIR: &str = "src/compiler-flags";

pub const LANG_FEATURES_DIR: &str = "src/language-features";

pub const LIB_FEATURES_DIR: &str = "src/library-features";

fn full_path(krate: &Crate, item: &Id) -> String {
    todo!()
}

fn is_ident(ident: &Ident, name: &str) -> bool {
    *ident == Ident::new(name, ident.span())
}

/// Returns an item name -> item unstable attributes mapping.
fn load_rustdoc_json_metadata(doc_dir: &Path) -> HashMap<String, String> {
    let mut all_items = HashMap::new();

    for file in fs::read_dir(doc_dir).expect("failed to list files in directory") {
        let entry = file.expect("failed to list file in directory");
        let file = fs::File::open(entry.path()).expect("failed to open file");
        let krate: Crate = serde_json::from_reader(BufReader::new(file)).expect("failed to parse JSON docs");

        let mut crate_items = HashMap::new();
        for item in krate.index.values() {
            if item.name.is_none() {
                continue;
            }
            let unstable_feature = item.attrs.iter().find_map(|attr: &String| {
                let parsed: syn::Attribute = syn::parse_str(attr).expect("failed to parse attribute");

                // Make sure this is an `unstable` attribute.
                if !is_ident(parsed.path.get_ident()?, "unstable") {
                    return None;
                }

                // Given `#[unstable(feature = "xyz")]`, return `(feature = "xyz")`.
                let list = match parsed.parse_meta() {
                    Ok(Meta::List(list)) => list,
                    _ => return None,
                };

                // Given a `NestedMeta` like `feature = "xyz"`, returns `xyz`.
                let get_feature_name = |nested: &_| {
                    match nested {
                        NestedMeta::Meta(Meta::NameValue(name_value)) => {
                            if !is_ident(name_value.path.get_ident()?, "feature") {
                                return None;
                            }
                            match name_value.lit {
                                Lit::Str(s) => Some(s.value()),
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                };

                for nested in list.nested.iter() {
                    if let Some(feat) = get_feature_name(nested) {
                        return Some(feat);
                    }
                }

                None
            });
            if let Some(feat) = unstable_feature {
                crate_items[&item.id] = feat;
            }
        }

        for (item, feat) in crate_items {
            all_items.insert(full_path(&krate, item), feat.to_owned());
        }
    }

    all_items
}

/// Builds the path to the Unstable Book source directory from the Rust 'src' directory.
pub fn unstable_book_path(base_src_path: &Path) -> PathBuf {
    base_src_path.join(PATH_STR)
}

/// Builds the path to the directory where the features are documented within the Unstable Book
/// source directory.
pub fn unstable_book_lang_features_path(base_src_path: &Path) -> PathBuf {
    unstable_book_path(base_src_path).join(LANG_FEATURES_DIR)
}

/// Builds the path to the directory where the features are documented within the Unstable Book
/// source directory.
pub fn unstable_book_lib_features_path(base_src_path: &Path) -> PathBuf {
    unstable_book_path(base_src_path).join(LIB_FEATURES_DIR)
}

/// Tests whether `DirEntry` is a file.
fn dir_entry_is_file(dir_entry: &fs::DirEntry) -> bool {
    dir_entry.file_type().expect("could not determine file type of directory entry").is_file()
}

/// Retrieves names of all unstable features.
pub fn collect_unstable_feature_names(features: &Features) -> BTreeSet<String> {
    features
        .iter()
        .filter(|&(_, ref f)| f.level == Status::Unstable)
        .map(|(name, _)| name.replace('_', "-"))
        .collect()
}

pub fn collect_unstable_book_section_file_names(dir: &Path) -> BTreeSet<String> {
    fs::read_dir(dir)
        .expect("could not read directory")
        .map(|entry| entry.expect("could not read directory entry"))
        .filter(dir_entry_is_file)
        .map(|entry| entry.path())
        .filter(|path| path.extension().map(|e| e.to_str().unwrap()) == Some("md"))
        .map(|path| path.file_stem().unwrap().to_str().unwrap().into())
        .collect()
}

/// Retrieves file names of all library feature sections in the Unstable Book with:
///
/// * hyphens replaced by underscores,
/// * the markdown suffix ('.md') removed.
fn collect_unstable_book_lang_features_section_file_names(
    base_src_path: &Path,
) -> BTreeSet<String> {
    collect_unstable_book_section_file_names(&unstable_book_lang_features_path(base_src_path))
}

/// Retrieves file names of all language feature sections in the Unstable Book with:
///
/// * hyphens replaced by underscores,
/// * the markdown suffix ('.md') removed.
fn collect_unstable_book_lib_features_section_file_names(base_src_path: &Path) -> BTreeSet<String> {
    collect_unstable_book_section_file_names(&unstable_book_lib_features_path(base_src_path))
}

pub fn check(path: &Path, json_docs: &Path, features: CollectedFeatures, bad: &mut bool) {
    let lang_features = features.lang;
    let lib_features = features
        .lib
        .into_iter()
        .filter(|&(ref name, _)| !lang_features.contains_key(name))
        .collect::<Features>();

    // Library features
    let unstable_lib_feature_names = collect_unstable_feature_names(&lib_features);
    let unstable_book_lib_features_section_file_names =
        collect_unstable_book_lib_features_section_file_names(path);

    // Language features
    let unstable_lang_feature_names = collect_unstable_feature_names(&lang_features);
    let unstable_book_lang_features_section_file_names =
        collect_unstable_book_lang_features_section_file_names(path);

    // Check for Unstable Book sections that don't have a corresponding unstable feature
    for feature_name in &unstable_book_lib_features_section_file_names - &unstable_lib_feature_names
    {
        if !unstable_lang_feature_names.contains(&feature_name) {
            tidy_error!(
                bad,
                "The Unstable Book has a 'library feature' section '{}' which doesn't \
                         correspond to an unstable library feature",
                feature_name
            );
        }
        let feature_path = unstable_book_lib_features_path(path).join(feature_name).with_extension("md");
        if !BufReader::new(fs::File::open(&feature_path).expect("could not read lib feature file")).lines().any(|line| {
            line.expect("could not ready lib feature file").contains("https://doc.rust-lang.org")
        }) {
            tidy_error!(bad, "the library feature {} has link to the rustdoc-generated docs; add a link to doc.rust-lang.org to {}", feature_name, feature_path.display());
        }
    }

    // Check for Unstable Book sections that don't have a corresponding unstable feature.
    for feature_name in
        &unstable_book_lang_features_section_file_names - &unstable_lang_feature_names
    {
        tidy_error!(
            bad,
            "The Unstable Book has a 'language feature' section '{}' which doesn't \
                     correspond to an unstable language feature",
            feature_name
        )
    }

    // List unstable features that don't have Unstable Book sections.
    // Remove the comment marker if you want the list printed.
    /*
    println!("Lib features without unstable book sections:");
    for feature_name in &unstable_lang_feature_names -
                        &unstable_book_lang_features_section_file_names {
        println!("    * {} {:?}", feature_name, lib_features[&feature_name].tracking_issue);
    }

    println!("Lang features without unstable book sections:");
    for feature_name in &unstable_lib_feature_names-
                        &unstable_book_lib_features_section_file_names {
        println!("    * {} {:?}", feature_name, lang_features[&feature_name].tracking_issue);
    }
    // */
}
