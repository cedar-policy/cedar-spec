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
    size_hint_utils::size_hint_for_range,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated policy
    pub policy: ABACPolicy,
    /// Level to validate the policy at
    pub level: usize,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        let level = u.int_in_range(0..=SETTINGS.max_depth + 1)?;
        Ok(Self {
            schema,
            policy,
            level,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            size_hint_for_range(0, SETTINGS.max_depth + 1),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    let def_impl = LeanDefinitionalEngine::new();

    if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        let mut policyset = ast::PolicySet::new();
        let policy: ast::StaticPolicy = input.policy.into();
        policyset.add_static(policy).unwrap();

        run_level_val_test(
            &def_impl,
            schema,
            &policyset,
            ValidationMode::Strict,
            input.level as i32,
        );
    }
});
