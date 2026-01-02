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
use cedar_drt::tests::run_level_val_test;
use cedar_drt_inner::fuzz_target;

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Policy, PolicySet, Schema, ValidationMode};

use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema, schema_gen::SchemaGen,
    settings::ABACSettings, size_hint_utils::size_hint_for_range,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated policy
    pub policy: ABACPolicy,
    /// Level to validate the policy at
    pub level: usize,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    enable_additional_attributes: true,
    ..ABACSettings::type_directed()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
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
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            size_hint_for_range(0, SETTINGS.max_depth + 1),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    let def_impl = CedarLeanFfi::new();

    if let Ok(schema) = Schema::try_from(input.schema) {
        let policy = Policy::from(input.policy);
        let mut policyset = PolicySet::new();
        policyset.add(policy).unwrap();

        run_level_val_test(
            &def_impl,
            schema,
            &policyset,
            ValidationMode::Strict,
            input.level as i32,
        );
    }
});
