/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
use cedar_policy_core::entities::Entities;
use cedar_policy_generators::abac::{ABACPolicy, ABACRequest, ABACSettings};
use cedar_policy_generators::hierarchy::Hierarchy;
use cedar_policy_generators::schema::Schema;
use cedar_policy_validator::{
    ActionBehavior, ValidationMode, Validator, ValidatorNamespaceDef, ValidatorSchemaFragment,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated hierarchy
    pub hierarchy: Hierarchy,
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
        Ok(Self {
            schema,
            hierarchy,
            policy,
            requests,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            Schema::arbitrary_hierarchy_size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
        ])
    }
}

/// helper function that just tells us whether a policyset passes validation
fn passes_validation(validator: &Validator, policyset: &ast::PolicySet) -> bool {
    validator
        .validate(policyset, ValidationMode::default())
        .validation_passed()
}

// The main fuzz target. This is for simple fuzzing of ABAC
// hierarchy/policy/requests without respect to types
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    if let Ok(entities) = Entities::try_from(input.hierarchy) {
        let mut policyset = ast::PolicySet::new();
        policyset.add_static(input.policy.into()).unwrap();
        debug!("Policies: {policyset}");
        debug!("Entities: {entities}");
        let diff_tester = DifferentialTester::new();
        let queries = input
            .requests
            .into_iter()
            .map(Into::into)
            .collect::<Vec<_>>();
        let mut responses = Vec::with_capacity(queries.len());
        for q in &queries {
            debug!("Q: {q}");
            let (ans, total_dur) =
                time_function(|| diff_tester.run_single_test(q, &policyset, &entities));
            info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
            responses.push(ans);
        }
        if let Ok(test_name) = std::env::var("DUMP_TEST_NAME") {
            // only dump testcases where the policy passes validation
            let passes_validation = {
                if let Ok(schema) = ValidatorNamespaceDef::from_namespace_definition(
                    input.schema.namespace().clone(),
                    input.schema.schemafile().clone(),
                    ActionBehavior::ProhibitAttributes,
                )
                .and_then(|f| {
                    ValidatorSchema::from_schema_fragments([
                        ValidatorSchemaFragment::from_namespaces([f]),
                    ])
                }) {
                    let validator = Validator::new(schema);
                    passes_validation(&validator, &policyset)
                } else {
                    false
                }
            };
            let dump_dir = std::env::var("DUMP_TEST_DIR").unwrap_or_else(|_| ".".to_string());
            dump(
                dump_dir,
                &test_name,
                &input.schema.into(),
                passes_validation,
                &policyset,
                &entities,
                std::iter::zip(queries.iter(), responses.iter()),
            )
            .expect("failed to dump test case");
        }
    }
});
