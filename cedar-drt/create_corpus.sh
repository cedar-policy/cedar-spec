#!/bin/bash

FUZZ_TARGET=abac-type-directed
TIMEOUT="15m" # 15m = 900s

# Assumes cedar-drt is already correctly built and configured
rm -rf corpus_tests
source set_env_vars.sh
export FUZZ_TARGET
timeout $TIMEOUT cargo fuzz run -s none $FUZZ_TARGET -j4 -- -rss_limit_mb=8196
./synthesize_tests.sh