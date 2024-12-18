#!/bin/bash

set -euo pipefail

# Check out the cedar submodule
git submodule update --init

# Set environment variables
cd cedar-drt
source set_env_vars.sh
cd ..

# Build the Lean formalization and extract to static C libraries
cd cedar-lean
lake build Cedar:static DiffTest:static Std:static
cd ..

# Build DRT
cd cedar-drt
cargo fuzz build
cargo test
