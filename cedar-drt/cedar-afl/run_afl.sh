#!/bin/bash
# Runs fuzzing experiment using Tmux

set -e
CONFIG="$1" # one of "random", "libfuzzer"
BENCHMARK="$2"
REP="$3"
TIME="$4"
SEED_CORPUS="$4"

if [ -z "$CONFIG" ]; then
    echo "Please set FUZZ_CONFIG env vars" > /dev/stderr
    exit 1
fi

# git pull
PATH=$PATH:/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin
(cd ../ && ./initialize_corpus.sh convert-policy-json-to-cedar)

RESULTS_DIR="results/$BENCHMARK/$CONFIG/rep_$REP"
mkdir -p $RESULTS_DIR
mkdir -p in
echo "" > in/seed
CORPUS_DIR="in"
CRASHES_DIR=$RESULTS_DIR/crashes

# rm -rf $CORPUS_DIR
# rm -rf $CRASHES_DIR

# mkdir -p $CORPUS_DIR
# mkdir -p $CRASHES_DIR

if [ "$BENCHMARK" == "raw_convert_policy_est_to_cedar"  ]; then
    rm -rf $CORPUS_DIR
    cp -r ../fuzz/corpus/convert-policy-json-to-cedar "$CORPUS_DIR"
fi

source ../set_env_vars.sh
cargo afl build
echo cargo afl fuzz -i in -o $RESULTS_DIR -V $TIME target/debug/$BENCHMARK
cargo afl fuzz -i in -o $RESULTS_DIR -V $TIME target/debug/$BENCHMARK > /dev/null
