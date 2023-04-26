if [ -z "${JAVA_HOME-}" ]; then
    # Idea from https://www.baeldung.com/find-java-home.
    export JAVA_HOME="$(java -XshowSettings:properties -version 2>&1 | sed -ne 's,^ *java\.home = ,,p')"
fi
export LD_LIBRARY_PATH=${LD_LIBRARY_PATH+$LD_LIBRARY_PATH:}$JAVA_HOME/lib/amd64/server
export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt)"
