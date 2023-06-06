#!/bin/bash

# Set JAVA_HOME
if [ -z "${JAVA_HOME-}" ]; then
    # Idea from https://www.baeldung.com/find-java-home.
    export JAVA_HOME="$(java -XshowSettings:properties -version 2>&1 | sed -ne 's,^ *java\.home = ,,p')"
fi

# Set LD_LIBRARY_PATH
libjvm_files=($(find "$JAVA_HOME" -name 'libjvm.*'))
if [ ${#libjvm_files[@]} = 1 ]; then
    export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}$(dirname "$libjvm_files")
else
    echo >&2 'Error: Failed to find libjvm'
fi
unset libjvm_dirs

# Set CLASSPATH
if [ -f "$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar" ]; then
    export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt):$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar"
fi