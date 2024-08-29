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
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};
use serde::Serialize;

/// Input expected by this fuzz target
#[derive(Debug, Clone, Serialize)]
pub struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    /// generated policy
    pub policy: ABACPolicy,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: false,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self { schema, policy })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ])
    }
}

// Non-type-directed fuzzing of (strict) validation.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let def_impl = LeanDefinitionalEngine::new();

    // generate a schema
    if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);

        // generate a policy
        let mut policyset = ast::PolicySet::new();
        let policy: ast::StaticPolicy = input.policy.into();
        policyset.add_static(policy).unwrap();
        debug!("Policies: {policyset}");

        // run the policy through both validators and compare the result
        let (_, total_dur) =
            time_function(|| run_val_test(&def_impl, schema, &policyset, ValidationMode::Strict));
        info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
    }
});
