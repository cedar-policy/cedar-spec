#!/bin/bash
set -ex

CURDIR=$(realpath .)

mkdir -p $DUMP_DIR
source set_env_vars.sh

set -u

# Minimize corpus to remove redundant seeds
cargo fuzz cmin "$FUZZ_TARGET" -s none

run_single_test () {
    # We could use `cargo fuzz run "$FUZZ_TARGET" -s none "$1"`
    # but this adds extra overhead to every test. We accept that overhead
    # the first time (see below), but subsequent times we just directly invoke
    # the executable.
    "./fuzz/target/x86_64-unknown-linux-gnu/release/$FUZZ_TARGET" -artifact_prefix="$CURDIR/fuzz/artifacts/$FUZZ_TARGET" "$1"
}

# Run the first input to make sure everything is built
hash=$(ls "fuzz/corpus/$FUZZ_TARGET" | head -n 1)
DUMP_TEST_DIR=$DUMP_DIR \
DUMP_TEST_NAME=$hash \
cargo fuzz run "$FUZZ_TARGET" -s none "fuzz/corpus/$FUZZ_TARGET/$hash"

for hash in $(ls "fuzz/corpus/$FUZZ_TARGET"); do
    DUMP_TEST_DIR=$DUMP_DIR \
    DUMP_TEST_NAME=$hash \
    run_single_test "fuzz/corpus/$FUZZ_TARGET/$hash"
done