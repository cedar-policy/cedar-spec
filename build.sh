#!/bin/bash

# Check out the cedar submodule
git submodule update --init

# Set LD_LIBRARY_PATH
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:$JAVA_HOME/lib/server

# Build the formalization and extract Java code
cd cedar-dafny && make compile-difftest
cd ..

# Build the Java wrapper for DRT
cd cedar-dafny-java-wrapper && ./gradlew build dumpClasspath
cd ..

# Build DRT
cd cedar-drt
export CLASSPATH="$(< ../cedar-dafny-java-wrapper/build/runtimeClasspath.txt):$(pwd)/../cedar-dafny-java-wrapper/build/libs/cedar-dafny-java-wrapper.jar"
cargo build
cargo test
cd fuzz && RUSTFLAGS="--cfg=fuzzing" cargo build