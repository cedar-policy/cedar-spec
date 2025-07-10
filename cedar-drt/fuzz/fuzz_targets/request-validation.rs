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
    logger::{initialize_log, TOTAL_MSG},
    tests::run_req_val_test,
    CedarLeanEngine,
};
use cedar_drt_inner::fuzz_target;

use cedar_policy::{Request, Schema};
use cedar_testing::cedar_test_impl::time_function;

use cedar_policy_generators::{
    abac::ABACRequest, hierarchy::Hierarchy, hierarchy::HierarchyGenerator, schema,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated hierarchy
    pub hierarchy: Hierarchy,
    /// the requests to try for this schema and hierarchy. We try 8 requests per
    /// schema/hierarchy
    pub requests: [ABACRequest; 8],
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
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
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
            requests,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

// Non-type-directed fuzzing of (strict) validation.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let def_impl = CedarLeanEngine::new();

    // generate a schema
    if let Ok(schema) = Schema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        let requests = input
            .requests
            .into_iter()
            .map(Request::from)
            .collect::<Vec<_>>();
        for request in requests.iter().cloned() {
            debug!("Request: {request}");
            let (_, total_dur) =
                time_function(|| run_req_val_test(&def_impl, schema.clone(), request));
            info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
        }
    }
});
