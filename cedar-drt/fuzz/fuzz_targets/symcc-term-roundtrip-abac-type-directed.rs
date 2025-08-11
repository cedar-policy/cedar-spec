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
use cedar_drt::{logger::initialize_log, CedarLeanEngine};

use cedar_drt_inner::fuzz_target;

use cedar_policy::{Policy, PolicySet, Schema};

use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema, settings::ABACSettings,
};

use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use log::debug;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated policy
    pub policy: ABACPolicy,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 3,
    max_width: 3,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;

        Ok(Self { schema, policy })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

// Fuzzing Target to show that Asserts/Term Serialization/Deserialization does not effect the final SMTLib script produced
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let len_engine = CedarLeanEngine::new();
    let lean_ffi = len_engine.get_ffi();
    let mut policyset = PolicySet::new();
    let policy: Policy = input.policy.into();
    policyset.add(policy.clone()).unwrap();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("Policies: {policyset}\n");

    if let Ok(schema) = Schema::try_from(input.schema) {
        for req_env in schema.request_envs() {
            // Compute's SMTLib Script Directly in one-pass from Lean
            match lean_ffi.smtlib_of_check_always_allows(&policyset, &schema, &req_env) {
                Ok(smtlib1) => {
                    // Get intermedaite term representaion of the Asserts / Verification conditions from Lean
                    match lean_ffi.asserts_of_check_always_allows(&policyset, &schema, &req_env) {
                        Ok(Ok(asserts)) => {
                            // Compute SMTLib script from the intermediate Assertions
                            match lean_ffi.smtlib_of_check_asserts(&asserts, &schema, &req_env) {
                                // The smtlib scripts should be identical. Otherwise serialization/deserialization may have altered the assertions
                                Ok(smtlib2) => assert_eq!(smtlib1, smtlib2, "Mismatch between direct smtlib and roundtripped term smtlib for {:?}\nDirect:\n{}\n\nRoundtripped\n{}", req_env, smtlib1, smtlib2),
                                Err(e) => panic!("Rountripped errored when direct smtlib request did not error. Error: {}", e),
                            }
                        }
                        Ok(Err(s)) => panic!("Roundtrip erorred when direct smtlib result did not error. Error: {}", s),
                        Err(e) => panic!("Rountripped errored when direct smtlib request did not error. Error: {}", e),
                    }
                }
                // The policy/schema produced an error in Lean
                Err(e) => {
                    // Check that either the generation of asserts or checking the asserts errors
                    match lean_ffi.asserts_of_check_always_allows(&policyset, &schema, &req_env) {
                        Ok(Ok(asserts)) => {
                            match lean_ffi.smtlib_of_check_asserts(&asserts, &schema, &req_env) {
                                Ok(_) => panic!("Rountripped did not error when direct smtlib request errored. Error: {}", e),
                                Err(_) => (),
                            }
                        }
                        Ok(Err(_)) => (),
                        Err(_) => (),
                    }
                }
            }
        }
    }
});
