#!/bin/bash
# Runs fuzzing experiment using Tmux

set -e
CONFIG="$1" # one of "random", "libfuzzer"
BENCHMARK="$2"
REP="$3"
TIME="$4"
BRANCH="$5"

if [ -z "$CONFIG" ]; then
    echo "USAGE: ./run_bolero.sh CONFIG BENCHMARK REP TIME BRANCH" > /dev/stderr
    exit 1
fi

if [ "$BRANCH" == "vasu/derive_arbitrary_generators"  ]; then
  (cd ../../cedar && git checkout $BRANCH)
else 
  (cd ../../cedar && git checkout vasu/well_typed_generators)
fi

git checkout $BRANCH
git pull origin $BRANCH
PATH=$PATH:/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin

RESULTS_DIR="results/$BENCHMARK/$CONFIG/rep_$REP"
CORPUS_DIR=$RESULTS_DIR/corpus
CRASHES_DIR=$RESULTS_DIR/crashes

rm -rf $CORPUS_DIR
rm -rf $CRASHES_DIR

mkdir -p $CORPUS_DIR
mkdir -p $CRASHES_DIR

if [ "$BENCHMARK" == "raw_convert_policy_est_to_cedar"  ]; then
    rm -rf $CORPUS_DIR
    cp -r ../fuzz/corpus/convert-policy-json-to-cedar "$CORPUS_DIR"
fi

source ../set_env_vars.sh
if [ "$CONFIG" == "random"  ]; then
    echo cargo bolero test $BENCHMARK --engine random -T $TIME 1> $RESULTS_DIR/valid.log
    cargo bolero test $BENCHMARK --engine random -T $TIME 1> $RESULTS_DIR/valid.log
else
    echo cargo bolero test $BENCHMARK --corpus-dir $CORPUS_DIR --crashes-dir $CRASHES_DIR --engine $CONFIG -T $TIME -t 30s --jobs 1 --engine-args="-rss_limit_mb=0 -print_final_stats=1 -ignore_crashes=1 -fork=1"
    cp fuzz-0.log $RESULTS_DIR/fuzz.log
fi
