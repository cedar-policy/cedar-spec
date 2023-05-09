#!/bin/bash

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