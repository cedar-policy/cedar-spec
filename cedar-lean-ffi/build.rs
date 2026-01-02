/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use cargo_metadata::MetadataCommand;
use std::path::{Path, PathBuf};

const CEDAR_LEAN_DIR: &str = "../cedar-lean";
const LEAN_BUILD_DIR: &str = "../cedar-lean/.lake/build/lib";
fn main() {
    let metadata = MetadataCommand::new().exec().unwrap();
    let cedar_proto_include_dir = match metadata
        .packages
        .iter()
        .find(|p| p.name.as_str() == "cedar-policy")
    {
        Some(cedar_policy_pkg) => {
            let package_path = PathBuf::from(&cedar_policy_pkg.manifest_path)
                .parent()
                .unwrap()
                .to_path_buf();
            package_path.join("protobuf_schema")
        }
        None => panic!(
            "Build script requires cedar-policy as a dependency. No matching dependency found"
        ),
    };
    let cedar_proto_include_dir = cedar_proto_include_dir.to_str().unwrap();

    // Get the location of the lean library
    let lean_dir = std::env::var("LEAN_LIB_DIR").expect(
        "`LEAN_LIB_DIR` environment variable is not set! Try running `source set_env_vars.sh`",
    );
    // We'll need to link against some files found here later, and it's nicer to
    // fail quickly with a helpful error message.
    if !Path::new(LEAN_BUILD_DIR).exists() {
        panic!("Lean build directory does not exist! Try running `./build_lean_lib.sh`")
    }

    println!("cargo:rustc-link-search=native={LEAN_BUILD_DIR}");
    println!("cargo:rustc-link-search=native={lean_dir}");
    println!(
        "cargo:rustc-link-search=native={CEDAR_LEAN_DIR}/.lake/packages/batteries/.lake/build/lib"
    );
    println!("cargo:rerun-if-changed={LEAN_BUILD_DIR}");
    println!("cargo:rerun-if-changed={lean_dir}");
    println!("cargo:rerun-if-changed={CEDAR_LEAN_DIR}/.lake/packages/batteries/.lake/build/lib");

    println!("cargo:rerun-if-changed=./protobuf_schema");
    let mut config = prost_build::Config::new();
    config.extern_path(".cedar_policy_core", "::cedar_policy::proto::models");
    config.extern_path(".cedar_policy_validator", "::cedar_policy::proto::models");
    config
        .compile_protos(
            &["./protobuf_schema/Messages.proto"],
            &["./protobuf_schema", cedar_proto_include_dir],
        )
        .unwrap();
}
