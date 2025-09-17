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
use cedar_drt_inner::{fuzz_target, schemas};

use cedar_policy::{Authorizer, Entities, Policy, PolicySet, Schema, TestEntityLoader};

use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    err::Error,
    hierarchy::HierarchyGenerator,
    schema,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated entity slice
    pub entities: Entities,
    /// generated policy
    pub policy: ABACPolicy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [ABACRequest; 8],
    /// Number of maximum iterations
    pub iterations: u8,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    per_action_request_env_limit: ABACSettings::default_per_action_request_env_limit(),
    total_action_request_env_limit: ABACSettings::default_total_action_request_env_limit(),
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;

        let requests = [
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
        ];
        let all_entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let cedar_schema = Schema::try_from(schema.clone()).unwrap();
        let entities = schemas::add_actions_to_entities(&cedar_schema, all_entities)?;
        Ok(Self {
            schema,
            entities,
            policy,
            requests,
            iterations: u8::arbitrary(u)?,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
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
            u8::size_hint(depth),
        ]))
    }
}

// This target tests a property that batched evaluation, if succeeds, should
// produce the same authorization decision of normal authorization where the
// the entire in-memory entity store is provided
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();

    if let Ok(schema) = Schema::try_from(input.schema) {
        let policy = Policy::from(input.policy);
        let mut policyset = PolicySet::new();
        policyset.add(policy.clone()).unwrap();
        let mut loader = TestEntityLoader::new(&input.entities);
        log::debug!("policy: {policyset}");

        for req in input.requests {
            let req = req.into();
            log::debug!("req: {req}");
            if let Ok(batched_decision) =
                policyset.is_authorized_batched(&req, &schema, &mut loader, input.iterations.into())
            {
                let authorizer = Authorizer::new();
                assert_eq!(
                    batched_decision,
                    authorizer
                        .is_authorized(&req, &policyset, &input.entities)
                        .decision()
                );
            }
        }
    }
});
