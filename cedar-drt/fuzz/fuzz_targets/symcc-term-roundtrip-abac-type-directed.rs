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

use cedar_drt_inner::{fuzz_target, symcc::total_action_request_env_limit};

use cedar_policy::{Policy, PolicySet, Schema};

use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema, schema_gen::SchemaGen,
    settings::ABACSettings,
};

use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use log::debug;
use similar_asserts::assert_eq;
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
    max_depth: 3,
    max_width: 3,
    total_action_request_env_limit: total_action_request_env_limit(),
    ..ABACSettings::type_directed()
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
        ]))
    }
}

// Fuzzing Target to show that Asserts/Term Serialization/Deserialization does not effect the final SMTLib script produced
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let lean_engine = CedarLeanEngine::new();
    let lean_ffi = lean_engine.get_ffi();
    let mut policyset = PolicySet::new();
    let policy: Policy = input.policy.into();
    policyset.add(policy.clone()).unwrap();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("Policies: {policyset}\n");

    if let Ok(schema) = Schema::try_from(input.schema) {
        let lean_schema = lean_ffi.load_lean_schema_object(&schema).unwrap();
        for req_env in schema.request_envs() {
            // Compute's SMTLib Script Directly in one-pass from Lean
            match lean_ffi.smtlib_of_check_always_allows(&policyset, lean_schema.clone(), &req_env)
            {
                Ok(smtlib1) => {
                    // Get intermediate term representation of the Asserts / Verification conditions from Lean
                    match lean_ffi.asserts_of_check_always_allows(&policyset, lean_schema.clone(), &req_env) {
                        Ok(Ok(asserts)) => {
                            // Compute SMTLib script from the intermediate Assertions
                            match lean_ffi.smtlib_of_check_asserts(&asserts, lean_schema.clone(), &req_env) {
                                // The smtlib scripts should be identical. Otherwise serialization/deserialization may have altered the assertions
                                Ok(smtlib2) => assert_eq!(Direct: smtlib1, Roundtripped: smtlib2, "Mismatch between direct smtlib and roundtripped term smtlib for {req_env:?}"),
                                Err(e) => panic!("Roundtripped errored when direct smtlib request did not error. Error: {e}"),
                            }
                        }
                        Ok(Err(s)) => panic!("Roundtrip errored when direct smtlib result did not error. Error: {s}"),
                        Err(e) => panic!("Roundtripped errored when direct smtlib request did not error. Error: {e}"),
                    }
                }
                // The policy/schema produced an error in Lean
                Err(e) => {
                    // Check that either the generation of asserts or checking the asserts errors
                    match lean_ffi.asserts_of_check_always_allows(
                        &policyset,
                        lean_schema.clone(),
                        &req_env,
                    ) {
                        Ok(Ok(asserts)) => {
                            if let Ok(_) = lean_ffi.smtlib_of_check_asserts(
                                &asserts,
                                lean_schema.clone(),
                                &req_env,
                            ) {
                                panic!("Roundtripped did not error when direct smtlib request errored. Error: {e}")
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
