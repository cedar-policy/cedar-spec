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

use std::path::Path;
const LEAN_BUILD_DIR: &'static str = "../cedar-lean/.lake/build/lib";
fn main() {
    #[cfg(feature = "lean-impl")]
    {
        let lean_dir = std::env::var("LEAN_LIB_DIR").expect(
            "`LEAN_LIB_DIR` environment variable is not set! Try running `source set_env_vars.sh`",
        );
        // We'll need to link against some files found here later, and it's nicer to
        // fail quickly with a helpful error message.
        if !Path::new(LEAN_BUILD_DIR).exists() {
            panic!("Lean build directory does not exist! Try running `( cd ../cedar-lean && ../cedar-drt/build_lean_lib.sh )`")
        }
        println!("cargo:rustc-link-search=native={LEAN_BUILD_DIR}");
        println!("cargo:rustc-link-search=native={lean_dir}");
        println!(
            "cargo:rustc-link-search=native=../cedar-lean/.lake/packages/batteries/.lake/build/lib"
        );
        println!("cargo:rerun-if-changed={LEAN_BUILD_DIR}");

        let mut config = prost_build::Config::new();
        config.extern_path(".cedar_policy_core", "::cedar_policy_core::ast::proto");
        config.extern_path(".cedar_policy_validator", "::cedar_policy_validator::proto");
        config
            .compile_protos(
                &["./protobuf_schema/Messages.proto"],
                &[
                    "./protobuf_schema",
                    "../cedar/cedar-policy-core/protobuf_schema",
                    "../cedar/cedar-policy-validator/protobuf_schema",
                ],
            )
            .unwrap();
    }
}
