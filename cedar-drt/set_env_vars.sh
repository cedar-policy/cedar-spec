#!/bin/bash

# Set JAVA_HOME
if [ -z "${JAVA_HOME-}" ]; then
    # Idea from https://www.baeldung.com/find-java-home.
    export JAVA_HOME="$(java -XshowSettings:properties -version 2>&1 | sed -ne 's,^ *java\.home = ,,p')"
fi

# Set LD_LIBRARY_PATH and DYLD_LIBRARY_PATH (for macOS)
function add_lib_to_path {
  lib_dirs=($(find "$JAVA_HOME" -name "lib${1}.*" -exec dirname {} \;))
  if [ ${#lib_dirs[@]} = 1 ]; then
      # Accessing an array element in both bash and zsh: https://stackoverflow.com/a/56311706
      lib_dir=${lib_dirs[@]:0:1}
      export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}${lib_dir}
      export DYLD_LIBRARY_PATH=${DYLD_LIBRARY_PATH+$DYLD_LIBRARY_PATH:}${lib_dir}
  else
      echo >&2 "Error: Failed to find lib${1}"
  fi
}
add_lib_to_path jvm
add_lib_to_path jli
unset -f add_lib_to_path

# Set CLASSPATH
if [ -f "$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar" ]; then
    export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt):$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar"
fi

# Set environment variables for Lean
export LEAN_LIB_DIR=$(lean --print-libdir)
export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}$(lean --print-libdir)
export DYLD_LIBRARY_PATH=${DYLD_LIBRARY_PATH+$DYLD_LIBRARY_PATH:}$(lean --print-libdir)
export LD_PRELOAD=${LD_PRELOAD+$LD_PRELOAD:}$(lean --print-prefix)/lib/glibc/libm.so