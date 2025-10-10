#!/bin/bash

# Build all fuzz targets and run them for 100 iterations starting from a fixed
# seed.  Not intended to find bugs in the code under test, just to exercise the
# targets and catch any silly mistakes in their implementation.

set -e
set -o pipefail

cargo fuzz build -s none
cargo fuzz list | xargs -I{} cargo fuzz run  -s none {} -- -seed=1 -runs=100
