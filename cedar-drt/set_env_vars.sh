if [ -z "${JAVA_HOME-}" ]; then
    # Idea from https://www.baeldung.com/find-java-home.
    export JAVA_HOME="$(java -XshowSettings:properties -version 2>&1 | sed -ne 's,^ *java\.home = ,,p')"
fi
# REVIEW: This script previously hard-coded $JAVA_HOME/lib/amd64/server, but my
# current system uses $JAVA_HOME/lib/server. Do we know if all the systems we
# currently target use $JAVA_HOME/lib/server? Do we want to keep this searching
# code to be safe? This change should probably be in a separate PR, but I don't
# want to block the arithmetic overflow work on that right now.
#
# Apparently different systems put libjvm.so in different subdirectories of $JAVA_HOME.
libjvm_dirs=($(find "$JAVA_HOME" -name libjvm.so -printf '%h\n'))
if [ ${#libjvm_dirs[@]} = 1 ]; then
    # Accessing an array element in both bash and zsh: https://stackoverflow.com/a/56311706
    export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}${libjvm_dirs[@]:0:1}
else
    echo >&2 'Error: Failed to find libjvm.so.'
fi
unset libjvm_dirs
export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt):$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar"
