// compile-flags: --test
// run-fail
// run-flags: --test-threads=1 --quiet
// check-run-results
// exec-env:RUST_BACKTRACE=0
// normalize-stdout-test "finished in \d+\.\d+s" -> "finished in $$TIME"
// ignore-emscripten no threads support
// needs-unwind

mod test {
    #[test]
    fn foo() {
        panic!();
    }

    #[test]
    fn bar() {}
    #[test]
    fn baz() {}
}
