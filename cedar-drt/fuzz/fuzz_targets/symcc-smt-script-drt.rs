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

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    symcc::{
        SinglePolicyFuzzTargetInput, assert_smtlib_scripts_match, lean_smtlib_of_check_asserts,
        smtlib_of_check_asserts,
    },
};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy_symcc::{CompiledPolicySet, always_allows_asserts};

use std::sync::LazyLock;

static RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
});

// Fuzz target checking that the Rust and Lean implementations produce the same
// SMTLIB scripts for a given set of `Term`s (in this case, `Term`s generated as
// asserts for AlwaysAllows on an arbitrary policy)
fuzz_target!(|input: SinglePolicyFuzzTargetInput| {
    initialize_log();
    if let Ok((schema, policyset)) = input.into_inputs_as_pset() {
        let lean_ffi = CedarLeanFfi::new();
        let lean_schema = lean_ffi.load_lean_schema_object(&schema).unwrap();
        for req_env in schema.request_envs() {
            // We let Rust compile the policies as it's faster than Lean
            if let Ok(cps) = CompiledPolicySet::compile(&policyset, &req_env, &schema) {
                let rust_asserts = always_allows_asserts(&cps);
                assert_smtlib_scripts_match(
                    RUNTIME.block_on(smtlib_of_check_asserts(&rust_asserts)),
                    lean_smtlib_of_check_asserts(
                        &rust_asserts,
                        &lean_ffi,
                        lean_schema.clone(),
                        &req_env,
                    ),
                );
            }
        }
    }
});
