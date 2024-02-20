#!/bin/bash

# Set environment variables for Lean
if ! command -v lean &> /dev/null; then
    echo "lean executable could not be found. is lean installed?"
else
    export LEAN_LIB_DIR=$(lean --print-libdir)
    export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}$(lean --print-libdir)
    export DYLD_LIBRARY_PATH=${DYLD_LIBRARY_PATH+$DYLD_LIBRARY_PATH:}$(lean --print-libdir)

    # if the version of GLIBC is too old (< 2.27), then use the verison of libm.so packaged with Lean
    GLIBC_VERSION=`ldd --version | awk '/ldd/{print $NF}'`
    if awk "BEGIN {exit !($GLIBC_VERSION < 2.27)}"; then
        export LD_PRELOAD=${LD_PRELOAD+$LD_PRELOAD:}$(lean --print-prefix)/lib/glibc/libm.so
    fi
fi
