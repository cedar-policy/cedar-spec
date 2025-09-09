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

use cedar_drt::{check_policy_set_equivalence, logger::initialize_log, policy_set_to_text};
use cedar_drt_inner::fuzz_target;

use cedar_policy_generators::{
    policy_set::GeneratedPolicySet, schema::Schema, settings::ABACSettings,
};
use itertools::Itertools;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
struct FuzzTargetInput {
    // the generated policies
    policy_set: GeneratedPolicySet,
}

// settings for this fuzz target
// copy-pasted from abac.rs
const SETTINGS: ABACSettings = ABACSettings {
    match_types: false,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: false,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    per_action_request_env_limit: ABACSettings::default_per_action_request_env_limit(),
    total_action_request_env_limit: ABACSettings::default_total_action_request_env_limit(),
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy_set = GeneratedPolicySet::arbitrary_for_hierarchy(&schema, &hierarchy, u)?;
        Ok(Self { policy_set })
    }

    fn size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

// AST --> text --> CST --> AST
// Prints a policy set to a string and parses it back using the standard AST parser.
// Panics if parsing fails.
fn round_trip_ast(
    policy_set: &cedar_policy_core::ast::PolicySet,
) -> cedar_policy_core::ast::PolicySet {
    // AST --> text
    let text = policy_set_to_text(policy_set);
    // text --> CST --> AST
    cedar_policy_core::parser::parse_policyset(&text).unwrap_or_else(|err| {
        panic!(
            "Failed to round-trip AST:\n{:?}\nPretty printed form:\n{}\nParse error: {:?}\n",
            policy_set, text, err
        )
    })
}

// AST --> text --> CST --> EST --> json --> EST --> AST
// Prints a policy set to a string, parses it back using the EST parser, converts it to JSON,
// and then parses it back to an AST.
// Panics if any step fails.
fn round_trip_est(
    policy_set: &cedar_policy_core::ast::PolicySet,
) -> cedar_policy_core::ast::PolicySet {
    // Convert the ast policy set to Cedar text, removing linked policies
    // AST --> text
    let text = policy_set.all_templates().join("\n");
    // text --> CST
    let cst = cedar_policy_core::parser::text_to_cst::parse_policies(&text)
        .expect("Failed to parse CST from text");
    // CST --> EST
    let est: cedar_policy_core::est::PolicySet =
        cst.try_into().expect("Failed to convert CST to EST");
    // EST --> JSON
    let json = serde_json::to_value(est).unwrap_or_else(|err| {
        panic!(
            "Failed to convert EST to JSON: {:?}\nParse error: {:?}\n",
            policy_set, err
        )
    });
    // JSON --> EST
    let est: cedar_policy_core::est::PolicySet =
        serde_json::from_value(json).expect("Failed to parse EST from JSON");
    // EST --> AST
    est.try_into().expect("Failed to convert EST to AST")
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let p: cedar_policy_core::ast::PolicySet = input.policy_set.into();

    debug!("Running on policy set: {:?}", p);

    // AST --> text --> CST --> AST
    let np = round_trip_ast(&p);
    check_policy_set_equivalence(&p, &np);

    // AST --> text --> CST --> EST --> json --> EST --> AST
    let np = round_trip_est(&p);
    check_policy_set_equivalence(&p, &np);
});
