#!/bin/bash
# Copyright Cedar Contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

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