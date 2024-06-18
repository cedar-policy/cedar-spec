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

FUZZ_TARGET="${FUZZ_TARGET:-abac}"
TIMEOUT_MINS="${TIMEOUT:-15}" # 15m = 900s
JOBS="${JOBS:-4}"
DUMP_DIR="${DUMP_DIR:-corpus-tests}"

# Assumes cedar-drt is already correctly built and configured
rm -rf $DUMP_DIR
source set_env_vars.sh
export FUZZ_TARGET
export DUMP_DIR
echo "Running fuzzer for $TIMEOUT_MINS minutes ..."
TIMEOUT=$(( $TIMEOUT_MINS * 60 ))
cargo fuzz run -s none $FUZZ_TARGET -j $JOBS -- -rss_limit_mb=8196 -max_total_time=$TIMEOUT
echo "Fuzzer done!"
# Minimize corpus to remove redundant seeds
echo "Minimizing corpus..."
cargo fuzz cmin "$FUZZ_TARGET" -s none
echo "Minimization done"
./synthesize_tests.sh
