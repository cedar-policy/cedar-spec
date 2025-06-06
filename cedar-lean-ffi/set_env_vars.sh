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

# Set environment variables for Lean
if ! command -v lean &> /dev/null; then
    echo "lean executable could not be found. is lean installed?"
    return 1
else
    export LEAN_LIB_DIR=$(lean --print-libdir)
    if [ -z "$LEAN_LIB_DIR" ]; then
        echo "error: lean --print-libdir returned no output"
        return 1
    fi
    export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}$(lean --print-libdir)
    export DYLD_LIBRARY_PATH=${DYLD_LIBRARY_PATH+$DYLD_LIBRARY_PATH:}$(lean --print-libdir)

    # if the version of GLIBC is too old (< 2.27), then use the version of libm.so packaged with Lean
    # Skip this check on macOS (darwin), which may not have `ldd`
    if [[ "$OSTYPE" != "darwin"* ]]; then
        GLIBC_VERSION=$(ldd --version | awk '/ldd/{print $NF}')
        if awk "BEGIN {exit !($GLIBC_VERSION < 2.27)}"; then
            export LD_PRELOAD=${LD_PRELOAD+$LD_PRELOAD:}$(lean --print-prefix)/lib/glibc/libm.so
        fi
    fi
fi
