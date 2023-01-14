#!/bin/sh
echo '{'
while read -r feature; do
    # Commit where this feature was first introduced.
    commit=$(git log --pretty=%H --reverse --pickaxe-regex -S 'feature\s*=\s*"'$feature \
        -- library/ src/lib{core,alloc,std,test,proc_macro,unwind,stdarch,unwind,rtstartup,portable-simd,panic_unwind,panic_abort,backtrace} \
        | head -n1)
    # src/version was first introduced in 1.48. Before that we have to parse `channel.rs`.
    # As a hack, just pretend that any feature introduced earlier was introduced in 1.47; we don't
    # actually care about the exact version, just whether it was used in the compiler on beta or
    # nightly.
    if ! version=$(git show $commit:src/version 2>/dev/null); then
        if ! [ -e src/version ]; then
            # We are *currently* in 1.47 or earlier; no version is reliable.
            # TODO: parse `CFG_RELEASE_NUM` instead.
            echo "error: detecting versions not supported for compiler versions earlier than 1.48"
            exit 1
        fi
        version="1.47.0"
    fi
    echo '"'$feature'": "'$version'",'
done < libs_features.txt
echo '}'