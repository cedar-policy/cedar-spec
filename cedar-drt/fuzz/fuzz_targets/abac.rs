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
use cedar_drt::{
    dump::dump,
    fuzz_target,
    logger::{initialize_log, TOTAL_MSG},
    tests::run_auth_test,
    CedarLeanEngine,
};

use cedar_drt_inner::schemas;

use cedar_policy::{Authorizer, Entities, Policy, PolicyId, PolicySet, Request, SchemaFragment};

use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    err::Error,
    hierarchy::HierarchyGenerator,
    schema::Schema,
    settings::ABACSettings,
};

use cedar_testing::cedar_test_impl::time_function;

use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated hierarchy
    pub entities: Entities,
    /// generated policy
    pub policy: ABACPolicy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [ABACRequest; 8],
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: false,
    enable_extensions: true,
    max_depth: 3,
    max_width: 7,
    enable_additional_attributes: false,
    enable_like: true,
    // ABAC fuzzing restricts the use of action because it is used to generate
    // the corpus tests which will be run on Cedar and CedarCLI.
    // These packages only expose the restricted action behavior.
    enable_action_groups_and_attrs: false,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = Schema::arbitrary(SETTINGS.clone(), u)?;
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

        let cedar_schema = cedar_policy::Schema::try_from(schema.clone()).unwrap();
        let entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let entities = schemas::add_actions_to_entities(&cedar_schema, entities)?;

        Ok(Self {
            schema,
            entities,
            policy,
            requests,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

// Simple fuzzing of ABAC hierarchy/policy/requests without respect to types.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let mut policyset = PolicySet::new();
    let policy = Policy::from(input.policy);
    policyset.add(policy.clone()).unwrap();
    debug!("Policies: {policyset}");
    debug!("Entities: {:?}", input.entities);
    let requests = input
        .requests
        .into_iter()
        .map(Request::from)
        .collect::<Vec<_>>();

    let lean_engine = CedarLeanEngine::new();

    for request in requests.iter().cloned() {
        debug!("Request: {request}");
        let (_, total_dur) =
            time_function(|| run_auth_test(&lean_engine, &request, &policyset, &input.entities));
        info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
    }
    if let Ok(test_name) = std::env::var("DUMP_TEST_NAME") {
        // When the corpus is re-parsed, the policy will be given id "policy0".
        // Recreate the policy set and compute responses here to account for this.
        let mut policyset = PolicySet::new();
        let policy = policy.new_id(PolicyId::new("policy0"));
        policyset.add(policy).unwrap();
        let responses = requests
            .iter()
            .map(|request| {
                let authorizer = Authorizer::new();
                authorizer.is_authorized(request, &policyset, &input.entities)
            })
            .collect::<Vec<_>>();
        let dump_dir = std::env::var("DUMP_TEST_DIR").unwrap_or_else(|_| ".".to_string());
        dump(
            dump_dir,
            &test_name,
            &SchemaFragment::try_from(input.schema).unwrap(),
            &policyset,
            &input.entities,
            std::iter::zip(requests, responses),
        )
        .expect("failed to dump test case");
    }
});
