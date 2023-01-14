#!/bin/sh
for version in `seq 66 -1 49`; do
    echo $version
    git checkout 1.$version.0 -- compiler/ library/ src/build_helper
    x t tidy | tee -a features_used_in_compiler_version.txt
done