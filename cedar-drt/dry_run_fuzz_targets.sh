#!/bin/bash

# Build all fuzz targets and run them for 10 iterations starting from a fixed
# seed.  Not intended to find bugs in the code under test, just to exercise the
# targets and catch any silly mistakes in their implementation.
#
# If running locally, you might want to `rm -rf ./fuzz/corpus` since the fuzzer
# will first run any existing corpus entries which may take a while,
# particularly since this uses a debug build.

set -e
set -o pipefail

cargo fuzz build -s none --dev
cargo fuzz list | xargs -I{} cargo fuzz run -s none --dev {} -- -seed=1 -runs=10
