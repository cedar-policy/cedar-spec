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
use cedar_drt::initialize_log;
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_core::authorizer::Authorizer;
use cedar_policy_core::entities::Entities;
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema::Schema,
    settings::ABACSettings,
};
use cedar_policy_validator::entity_manifest::{compute_entity_manifest, EntityManifestError};
use cedar_policy_validator::ValidatorSchema;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, schema, and 8 associated policies
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated hierarchy
    pub hierarchy: Hierarchy,
    /// the policy which we will see if it validates
    pub policy: ABACPolicy,
    /// the requests to try, if the policy validates.
    /// We try 8 requests per validated policy.
    pub requests: [ABACRequest; 8],
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
        Ok(Self {
            schema,
            hierarchy,
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

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
            let mut policyset = ast::PolicySet::new();
            let policy: ast::StaticPolicy = input.policy.into();
            policyset.add_static(policy.clone()).unwrap();
            let manifest = match compute_entity_manifest(&Validator::new(schema), &policyset) {
                Ok(manifest) => manifest,
                Err(
                    EntityManifestError::UnsupportedCedarFeature(_)
                    | EntityManifestError::Validation(_),
                ) => {
                    return;
                }
                Err(e) => panic!("failed to produce an entity manifest: {e}"),
            };

            let authorizer = Authorizer::new();
            debug!("Policies: {policyset}");
            debug!("Entities: {entities}");
            for abac_request in input.requests.into_iter() {
                let request = ast::Request::from(abac_request);
                debug!("Request: {request}");
                let entity_slice = manifest
                    .slice_entities(&entities, &request)
                    .expect("failed to slice entities");
                debug!("Entity slice: {entity_slice}");
                let ans_original = authorizer.is_authorized(request.clone(), &policyset, &entities);
                let ans_slice = authorizer.is_authorized(request, &policyset, &entity_slice);
                assert_eq!(
                    ans_original.decision, ans_slice.decision,
                    "Authorization decision differed with and without entity slicing!"
                );
            }
        }
    }
});
