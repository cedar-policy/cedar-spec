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
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};

use cedar_policy::{
    compute_entity_manifest, Authorizer, Entities, EntityManifestError, Policy, PolicySet, Request,
    Schema, Validator,
};

use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};
use log::debug;
use std::convert::TryFrom;

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput<true>| {
    initialize_log();
    if let Ok(schema) = Schema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        let mut policyset = PolicySet::new();
        let policy: Policy = input.policy.into();
        policyset.add(policy.clone()).unwrap();
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
        debug!("Entities: {}", input.entities.as_ref());
        for abac_request in input.requests.into_iter() {
            let request = Request::from(abac_request);
            debug!("Request: {request}");
            let entity_slice: Entities = manifest
                .slice_entities(input.entities.as_ref(), request.as_ref())
                .expect("failed to slice entities")
                .into();
            debug!("Entity slice: {}", entity_slice.as_ref());
            let ans_original = authorizer.is_authorized(&request, &policyset, &input.entities);
            let ans_slice = authorizer.is_authorized(&request, &policyset, &entity_slice);
            assert_eq!(
                ans_original.decision(),
                ans_slice.decision(),
                "Authorization decision differed with and without entity slicing!"
            );
        }
    }
});
