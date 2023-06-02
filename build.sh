#!/bin/bash

# Check out the cedar submodule
git submodule update --init

# Set environment variables
cd cedar-drt && source ./set_env_vars.sh
cd ..

# Build the formalization and extract Java code
cd cedar-dafny && make compile-difftest
cd ..

# Build the Java wrapper for DRT
cd cedar-dafny-java-wrapper && ./gradlew build dumpClasspath
cd ..

# Build DRT
cd cedar-drt
cargo build
cargo test
cd fuzz && RUSTFLAGS="--cfg=fuzzing" cargo build