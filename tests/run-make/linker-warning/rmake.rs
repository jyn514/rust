use std::path::Path;

use run_make_support::rfs::remove_file;
use run_make_support::{Rustc, rustc};

fn run_rustc() -> Rustc {
    let mut rustc = rustc();
    rustc.arg("main.rs").output("main").linker("./fake-linker");
    rustc
}

fn main() {
    // first, compile our linker
    rustc().arg("fake-linker.rs").output("fake-linker").run();

    // Make sure we don't show the linker args unless `--verbose` is passed
    run_rustc()
        .link_arg("run_make_error")
        .verbose()
        .run_fail()
        // .assert_stderr_contains_regex("lol no");
        .assert_stderr_contains_regex("fake-linker.*run_make_error");
    run_rustc()
        .link_arg("run_make_error")
        .run_fail()
        .assert_stderr_not_contains_regex("fake-linker.*run_make_error");
}
