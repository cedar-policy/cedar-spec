#!/bin/bash
lib_path=/Users/anmwells/Development/Cedar/cedar-spec/cedar-dafny/build/lib
class_path=/Users/anmwells/Development/Cedar/cedar-spec/cedar-dafny/build/lib/CedarDafny-difftest.jar:/Users/anmwells/Development/Cedar/cedar-spec/cedar-dafny/build/lib/DafnyRuntime.jar:/Users/anmwells/.gradle/caches/modules-2/files-2.1/com.fasterxml.jackson.core/jackson-annotations/2.12.7/2042461b754cd65ab2dd74a9f19f442b54625f19/jackson-annotations-2.12.7.jar:/Users/anmwells/.gradle/caches/modules-2/files-2.1/com.fasterxml.jackson.core/jackson-core/2.12.7/4669a54b799c105572aa8de2a1ae0fe64a17745/jackson-core-2.12.7.jar:/Users/anmwells/.gradle/caches/modules-2/files-2.1/com.fasterxml.jackson.core/jackson-databind/2.12.7.1/48d6674adb5a077f2c04b42795e2e7624997b8b9/jackson-databind-2.12.7.1.jar:/Users/anmwells/Development/Cedar/cedar-spec/cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar
main_class="com.CedarDefinitionalImplementation.Main"

java -Djava.library.path="$lib_path" -cp "$class_path" "$main_class" "$@"
