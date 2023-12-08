#!/bin/bash

set -e

# Check out the cedar submodule
git submodule update --init

# Set environment variables
cd cedar-drt
source set_env_vars.sh
cd ..

# Build the Dafny formalization and extract to Java code
cd cedar-dafny
make compile-difftest
cd ..

# Build the Dafny Java wrapper
cd cedar-dafny-java-wrapper
./gradlew build dumpClasspath
cd ..

# Build the Lean formalization and extract to static C libraries
cd cedar-lean
lake build Cedar:static DiffTest:static Std:static
cd ..

# Build DRT
cd cedar-drt
cargo build

# Run integration tests
source set_env_vars.sh
cargo test -- --nocapture

# Build inner fuzz crate
cd fuzz && RUSTFLAGS="--cfg=fuzzing" cargo build
cargo test
