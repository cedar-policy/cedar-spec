#!/bin/bash

FUZZ_TARGET="${FUZZ_TARGET:-abac}"
TIMEOUT="${TIMEOUT:-15m}" # 15m = 900s
JOBS="${JOBS:-4}"
DUMP_DIR="${DUMP_DIR:-corpus_tests}"

# Assumes cedar-drt is already correctly built and configured
rm -rf $DUMP_DIR
source set_env_vars.sh
export FUZZ_TARGET
export DUMP_DIR
timeout $TIMEOUT cargo fuzz run -s none $FUZZ_TARGET -j $JOBS -- -rss_limit_mb=8196
./synthesize_tests.sh