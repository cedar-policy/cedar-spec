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

use cedar_policy::{Authorizer, Entities, PolicySet, Schema};
use std::str::FromStr;
use std::sync::LazyLock;

use cedar_policy_generators::{
    abac::ABACRequest,
    err::Error,
    hierarchy::HierarchyGenerator,
    schema,
    schema_gen::{SchemaGen, ValidatorSchema},
    settings::ABACSettings,
};

use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use log::debug;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy and 8 associated requests
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated entity slice
    pub entities: Entities,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [ABACRequest; 8],
}

static SCHEMA: LazyLock<Schema> = LazyLock::new(|| {
    let schema_file =
        std::env::var("CEDAR_SCHEMA_FILE").expect("CEDAR_SCHEMA_FILE environment variable not set");
    let schema_content = std::fs::read_to_string(schema_file).expect("Failed to read schema file");
    Schema::from_str(&schema_content).expect("Failed to parse schema")
});

static POLICY_SET: LazyLock<PolicySet> = LazyLock::new(|| {
    let policy_file =
        std::env::var("CEDAR_POLICY_FILE").expect("CEDAR_POLICY_FILE environment variable not set");
    let policy_content = std::fs::read_to_string(policy_file).expect("Failed to read policy file");
    PolicySet::from_str(&policy_content).expect("Failed to parse policy set")
});

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 3,
    max_width: 3,
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
        let schema: ValidatorSchema = ValidatorSchema::new(SCHEMA.as_ref(), &SETTINGS, u)?;
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
        let entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let entities = schemas::add_actions_to_entities(&SCHEMA, entities)?;
        Ok(Self { entities, requests })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
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

// Type-directed fuzzing of ABAC hierarchy/policy/requests.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();

    let requests = input
        .requests
        .into_iter()
        .map(Into::into)
        .collect::<Vec<_>>();

    let entities = input.entities.into();

    for request in requests.iter() {
        debug!("Request : {request}");

        let authorizer = Authorizer::new();
        authorizer.is_authorized(request, &*POLICY_SET, &entities);
    }
});
