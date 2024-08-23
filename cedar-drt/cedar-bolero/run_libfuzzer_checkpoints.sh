#!/bin/bash
# Runs fuzzing experiment using Tmux

set -e
CONFIG="$1" # one of "random", "libfuzzer"
BENCHMARK="$2"
REP="$3"
TIME="$4"
BRANCH="$5"

if [ -z "$BRANCH" ]; then
    echo "USAGE: ./run_bolero.sh CONFIG BENCHMARK REP TIME BRANCH" > /dev/stderr
    exit 1
fi

if [ "$BRANCH" == "vasu/derive_arbitrary_generators"  ]; then
  (cd ../../cedar && git checkout $BRANCH)
else 
  (cd ../../cedar && git checkout vasu/well_typed_generators)
fi

git checkout $BRANCH
# git pull
PATH=$PATH:/home/ubuntu/.elan/bin:/home/ubuntu/.cargo/bin

RESULTS_DIR="results/$BENCHMARK/$CONFIG/rep_$REP"
CHECKPOINTS_DIR=$RESULTS_DIR/checkpoints

source ../set_env_vars.sh
./run_experiment_checkpoints.py $TIME $CONFIG $BENCHMARK $CHECKPOINTS_DIR $REP $RESULTS_DIR
