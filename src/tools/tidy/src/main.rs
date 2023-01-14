//! Tidy checks source code in this repository.
//!
//! This program runs all of the various tidy checks for style, cleanliness,
//! etc. This is run by default on `./x.py test` and as part of the auto
//! builders. The tidy checks can be executed with `./x.py test tidy`.

use regex::Regex;
use tidy::features::Version;
use tidy::features::{collect_lang_features, Status};
use tidy::walk::walk;
use tidy::*;

use std::collections::{HashMap, HashSet};
use std::env;
use std::ffi::OsStr;
// use std::num::NonZeroUsize;
use std::path::PathBuf;
// use std::process;
// use std::str::FromStr;
// use std::sync::atomic::{AtomicBool, Ordering};
// use std::thread::{scope, ScopedJoinHandle};

fn main() {
    let root_path: PathBuf = env::args_os().nth(1).expect("need path to root of repo").into();
    // let cargo: PathBuf = env::args_os().nth(2).expect("need path to cargo").into();
    // let output_directory: PathBuf =
    //     env::args_os().nth(3).expect("need path to output directory").into();
    // let concurrency: NonZeroUsize =
    //     FromStr::from_str(&env::args().nth(4).expect("need concurrency"))
    //         .expect("concurrency must be a number");

    // let src_path = root_path.join("src");
    let library_path = root_path.join("library");
    let compiler_path = root_path.join("compiler");

    // let args: Vec<String> = env::args().skip(1).collect();

    // let verbose = args.iter().any(|s| *s == "--verbose");
    // let bless = args.iter().any(|s| *s == "--bless");

    let mut bad = false;
    let current_version: Version = include_str!("../../../version").trim_end().parse().unwrap();

    let all_lang_features = collect_lang_features(&compiler_path, &mut bad);
    assert!(!all_lang_features.is_empty());

    let all_lib_features = features::collect_lib_features(&library_path);
    assert!(!all_lib_features.is_empty());

    let mut num_features = 0;
    let mut unstable_libs_features = HashSet::new();

    // Only `stable` features have a `since` version.
    // This list was hacked together with `unstable_feature_versions.sh`.
    let feature_versions_introduced: HashMap<String, String> =
        serde_json::from_str(include_str!("../../../../feature_introduced_version.json")).unwrap();

    let mut check_feature = |name: &str| {
        num_features += 1;
        let lib_feature = match all_lib_features.get(name) {
            Some(feat) => feat,
            None => {
                assert!(all_lang_features.contains_key(name), "unknown feature {name}");
                return;
            }
        };
        match lib_feature.level {
            Status::Removed => panic!("using removed feature"),
            Status::Stable => {} // totally fine
            Status::Unstable => {
                // let stable_date = lib_feature.since.unwrap_or_else(|| panic!("missing `since` for {name}"));
                let introduced_version = feature_versions_introduced
                    .get(name)
                    .unwrap_or_else(|| panic!("missing introduced version for {name}"));
                if introduced_version.parse::<Version>().unwrap() == current_version {
                    // num_just_added_features += 1;
                    unstable_libs_features.insert(name.to_owned());
                }
            }
        }
    };

    let feature_regex = Regex::new(r"^\s*#!\[.*feature\(([a-zA-Z][^)]*)\)]").unwrap();
    walk(
        &compiler_path,
        &mut |path| path.is_file() && path.extension() != Some(OsStr::new("rs")),
        &mut |_, contents| {
            for line in contents.lines() {
                if let Some(captures) = feature_regex.captures(line) {
                    let features = captures.get(1).unwrap();
                    for feature in features.as_str().split(",") {
                        check_feature(feature.trim());
                    }
                }
            }
        },
    );

    assert!(num_features > 0);
    println!("found {} library features used in the compiler", unstable_libs_features.len());
    for feature in unstable_libs_features {
        println!("{feature}");
    }
}
