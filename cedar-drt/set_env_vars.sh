#!/bin/bash

# Set JAVA_HOME
if [ -z "${JAVA_HOME-}" ]; then
    # Idea from https://www.baeldung.com/find-java-home.
    export JAVA_HOME="$(java -XshowSettings:properties -version 2>&1 | sed -ne 's,^ *java\.home = ,,p')"
fi

# Set LD_LIBRARY_PATH
libjvm_dirs=($(find "$JAVA_HOME" -name 'libjvm.*'))
if [ ${#libjvm_dirs[@]} = 1 ]; then
    # Accessing an array element in both bash and zsh: https://stackoverflow.com/a/56311706
    export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}${libjvm_dirs[@]:0:1}
else
    echo >&2 'Error: Failed to find libjvm'
fi
unset libjvm_dirs

# Set CLASSPATH
if [ -f "$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar" ]; then
    export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt):$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar"
fi