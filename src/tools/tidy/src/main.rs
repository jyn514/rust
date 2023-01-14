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

use std::collections::{HashSet, VecDeque};
use std::env;
use std::ffi::OsStr;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::process;
use std::str::FromStr;
// use std::sync::atomic::{AtomicBool, Ordering};
// use std::thread::{scope, ScopedJoinHandle};

fn main() {
    let root_path: PathBuf = env::args_os().nth(1).expect("need path to root of repo").into();
    let cargo: PathBuf = env::args_os().nth(2).expect("need path to cargo").into();
    let output_directory: PathBuf =
        env::args_os().nth(3).expect("need path to output directory").into();
    let concurrency: NonZeroUsize =
        FromStr::from_str(&env::args().nth(4).expect("need concurrency"))
            .expect("concurrency must be a number");

    let src_path = root_path.join("src");
    let library_path = root_path.join("library");
    let compiler_path = root_path.join("compiler");

    let args: Vec<String> = env::args().skip(1).collect();

    let verbose = args.iter().any(|s| *s == "--verbose");
    let bless = args.iter().any(|s| *s == "--bless");

    // let bad = std::sync::Arc::new(AtomicBool::new(false));
    let mut bad = false;
    let current_version: Version = include_str!("../../../version").trim_end().parse().unwrap();

    let all_lang_features = collect_lang_features(&compiler_path, &mut bad);
    assert!(!all_lang_features.is_empty());

    let all_lib_features = features::collect_lib_features(&library_path);
    assert!(!all_lib_features.is_empty());

    let mut num_features = 0;
    let mut unstable_libs_features = HashSet::new();

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
                // if stable_date == current_version {
                // num_just_added_features += 1;
                unstable_libs_features.insert(name.to_owned());
                // }
            }
        }
    };

    let feature_regex = Regex::new(r"^\s*#!\[.*feature\(([a-zA-Z][^)]*)\)]").unwrap();
    walk(
        &compiler_path,
        &mut |path| path.is_file() && path.extension() != Some(OsStr::new("rs")),
        &mut |entry, contents| {
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
    println!(
        "found {} library features used in the compiler",
        unstable_libs_features.len()
    );
    for feature in unstable_libs_features {
        println!("{feature}");
    }

    // scope(|s| {
    //     let mut handles: VecDeque<ScopedJoinHandle<'_, ()>> =
    //         VecDeque::with_capacity(concurrency.get());

    //     macro_rules! check {
    //         ($p:ident $(, $args:expr)* ) => {
    //             while handles.len() >= concurrency.get() {
    //                 handles.pop_front().unwrap().join().unwrap();
    //             }

    //             let handle = s.spawn(|| {
    //                 let mut flag = false;
    //                 $p::check($($args),* , &mut flag);
    //                 if (flag) {
    //                     bad.store(true, Ordering::Relaxed);
    //                 }
    //             });
    //             handles.push_back(handle);
    //         }
    //     }

    // check!(target_specific_tests, &src_path);

    // // Checks that are done on the cargo workspace.
    // check!(deps, &root_path, &cargo);
    // check!(extdeps, &root_path);

    // // Checks over tests.
    // check!(debug_artifacts, &src_path);
    // check!(ui_tests, &src_path);
    // check!(mir_opt_tests, &src_path, bless);

    // // Checks that only make sense for the compiler.
    // check!(errors, &compiler_path);
    // check!(error_codes_check, &[&src_path, &compiler_path]);

    // // Checks that only make sense for the std libs.
    // check!(pal, &library_path);
    // check!(primitive_docs, &library_path);

    // // Checks that need to be done for both the compiler and std libraries.
    // check!(unit_tests, &src_path);
    // check!(unit_tests, &compiler_path);
    // check!(unit_tests, &library_path);

    // if bins::check_filesystem_support(&[&root_path], &output_directory) {
    //     check!(bins, &root_path);
    // }

    // check!(style, &src_path);
    // check!(style, &compiler_path);
    // check!(style, &library_path);

    // check!(edition, &src_path);
    // check!(edition, &compiler_path);
    // check!(edition, &library_path);

    // check!(alphabetical, &src_path);
    // check!(alphabetical, &compiler_path);
    // check!(alphabetical, &library_path);

    // let collected = {
    //     while handles.len() >= concurrency.get() {
    //         handles.pop_front().unwrap().join().unwrap();
    //     }
    //     let mut flag = false;
    //     let r = features::check(&src_path, &compiler_path, &library_path, &mut flag, verbose);
    //     if flag {
    //         bad.store(true, Ordering::Relaxed);
    //     }
    //     r
    // };
    // check!(unstable_book, &src_path, collected);
    // });

    // if bad.load(Ordering::Relaxed) {
    //     eprintln!("some tidy checks failed");
    //     process::exit(1);
    // }
}
