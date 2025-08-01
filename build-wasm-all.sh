#!/bin/bash
set -e

echo "Building cedar-wasm and CedarSymEval for WebAssembly"

# Install required tools
if ! command -v wasm-pack &> /dev/null; then
    echo "Installing wasm-pack..."
    cargo install wasm-pack
fi

# Ensure wasm32 target is installed
rustup target add wasm32-unknown-unknown

# Step 1: Modify CedarSymEval's Cargo.toml to fix Tokio for WASM
echo "Configuring CedarSymEval for WASM..."
cd /workplace/mishiej/CedarSymEval/src/CedarSymEval
# Create a backup of the original Cargo.toml
cp Cargo.toml Cargo.toml.bak
# Update Tokio dependency to remove networking features
sed -i 's/tokio = { version = "1.0", features = \["io-util", "process"\] }/tokio = { version = "1.0", features = \["io-util", "sync", "time", "macros"\], default-features = false }/' Cargo.toml

# Step 1: Build CedarSymEval with WASM support
echo "Building CedarSymEval with WASM support..."
cargo build --target wasm32-unknown-unknown --release --features wasm

# Step 2: Modify cedar-wasm's Cargo.toml to fix Tokio for WASM
echo "Configuring cedar-wasm for WASM..."
cd /workplace/mishiej/cedar-spec/cedar-wasm
# Create a backup of the original Cargo.toml
cp Cargo.toml Cargo.toml.bak
# Update Tokio dependency to remove networking features
sed -i 's/tokio = { version = "1.0", features = \[".*"\] }/tokio = { version = "1.0", features = \["sync", "time", "macros"\], default-features = false }/' Cargo.toml

# Step 2: Build cedar-wasm
echo "Building cedar-wasm..."
wasm-pack build --target web --out-dir pkg

# Restore original Cargo.toml files
echo "Restoring original Cargo.toml files..."
cd /workplace/mishiej/CedarSymEval/src/CedarSymEval
mv Cargo.toml.bak Cargo.toml
cd /workplace/mishiej/cedar-spec/cedar-wasm
mv Cargo.toml.bak Cargo.toml

echo "Build complete! Output is in /workplace/mishiej/cedar-spec/cedar-wasm/pkg/"