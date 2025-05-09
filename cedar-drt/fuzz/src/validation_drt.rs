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

use cedar_drt::{
    ast, initialize_log, LeanDefinitionalEngine, ValidationMode, ValidatorSchema, TOTAL_MSG,
};
use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use cedar_testing::cedar_test_impl::time_function;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};

use crate::run_val_test;

/// Input for validation DRT fuzz targets
#[derive(Debug, Clone)]
pub struct FuzzTargetInput<const TYPE_DIRECTED: bool> {
    /// generated schema
    pub schema: Schema,
    /// generated policy
    pub policy: ABACPolicy,
}

impl<const TYPE_DIRECTED: bool> FuzzTargetInput<TYPE_DIRECTED> {
    fn settings() -> ABACSettings {
        ABACSettings {
            match_types: TYPE_DIRECTED,
            enable_extensions: true,
            max_depth: 7,
            max_width: 7,
            enable_additional_attributes: true,
            enable_like: true,
            enable_action_groups_and_attrs: true,
            enable_arbitrary_func_call: true,
            enable_unknowns: false,
            enable_action_in_constraints: true,
        }
    }
}

impl<'a, const TYPE_DIRECTED: bool> Arbitrary<'a> for FuzzTargetInput<TYPE_DIRECTED> {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(Self::settings(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self { schema, policy })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&Self::settings(), depth),
        ]))
    }
}

pub fn fuzz_target<const TYPE_DIRECTED: bool>(input: FuzzTargetInput<TYPE_DIRECTED>) {
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
}
