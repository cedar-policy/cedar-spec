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

extern crate prost_build;
use std::env;
fn main() {
    let lean_dir = env::var("LEAN_LIB_DIR").expect(
        "`LEAN_LIB_DIR` environment variable is not set! Try running `source set_env_vars.sh`",
    );
    println!("cargo:rustc-link-search=native=../cedar-lean/.lake/build/lib");
    println!("cargo:rustc-link-search=native={lean_dir}");
    println!(
        "cargo:rustc-link-search=native=../cedar-lean/.lake/packages/batteries/.lake/build/lib"
    );
    println!("cargo:rerun-if-changed=../cedar-lean/.lake/build/lib");

    let mut config = prost_build::Config::new();
    config.extern_path(".cedar_policy_core", "::cedar_policy_core::ast::proto");
    config.extern_path(".cedar_policy_validator", "::cedar_policy_validator::proto");
    config.compile_protos(
        &["./schema/Messages.proto"],
        &["./schema", "../cedar/cedar-policy-core/schema", "../cedar/cedar-policy-validator/schema"]).unwrap();
}
