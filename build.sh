#!/bin/bash

# Check out the cedar submodule
git submodule update --init

# Set environment variables
cd cedar-drt && source ./set_env_vars.sh
cd ..

# Build the Dafny formalization and extract Java code
cd cedar-dafny && make compile-difftest
cd ..

# Build the Dafny Java wrapper
cd cedar-dafny-java-wrapper && ./gradlew build dumpClasspath
cd ..

# Build the Lean formalization and extract to static C libraries
cd cedar-lean && \
lake exe cache get && \
lake build Cedar:static DiffTest:static Std:static Mathlib:static Qq:static Aesop:static ProofWidgets:static
cd ..

# Build DRT
cd cedar-drt
cargo build
cd fuzz && RUSTFLAGS="--cfg=fuzzing" cargo build

# Run integration tests
cargo test -- --nocapture