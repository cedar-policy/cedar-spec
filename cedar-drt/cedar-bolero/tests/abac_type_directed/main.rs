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

use arbitrary::{self, Arbitrary, Unstructured};
use ast::PolicyID;
use bolero::check;
use cedar_bolero_fuzz::{
    drop_some_entities, dump, dump_fuzz_test_case, run_auth_test, run_eval_test, time_function,
    FuzzTestCase, TestCaseFormat,
};
use cedar_drt::utils::expr_to_est;
use cedar_drt::*;
use cedar_policy::{Authorizer, Request};
use cedar_policy_core::{ast::Expr, entities::Entities};
use cedar_policy_generators::abac::{ABACPolicy, ABACRequest};
use cedar_policy_generators::err::Error;
use cedar_policy_generators::hierarchy::{self, Hierarchy, HierarchyGenerator};
use cedar_policy_generators::schema::{arbitrary_schematype_with_bounded_depth, Schema};
use cedar_policy_generators::settings::ABACSettings;
use cedar_policy_validator::SchemaFragment;
use log::{debug, info};
use serde::Serialize;
use serde_json::json;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone, Serialize)]
pub struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    /// generated entity slice
    #[serde(skip)]
    pub entities: Entities,
    /// generated policy
    pub policy: ABACPolicy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    #[serde(skip)]
    pub requests: [ABACRequest; 8],
}

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
    enable_unspecified_apply_spec: true,
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
        let all_entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let entities = drop_some_entities(all_entities, u)?;
        Ok(Self {
            schema,
            entities,
            policy,
            requests,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
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
        ])
    }
}

impl TestCaseFormat for FuzzTargetInput {
    fn to_fuzz_test_case(&self) -> FuzzTestCase {
        // Access the serialized expression
        let est_policy: cedar_policy_core::est::Policy = self.policy.0.clone().into();
        let representation = json!({
            "entities": self.entities,
            "policy": est_policy,
            // Format the requests as strings in a list
            "requests": self.requests.iter().map(|r| format!("{}", r)).collect::<Vec<_>>(),
        });
        FuzzTestCase {
            representation: representation.to_string(),
            ..Default::default()
        }
    }
}

fn main() {
    check!()
        .with_arbitrary::<FuzzTargetInput>()
        .for_each(|input| {
            initialize_log();
            let def_impl = LeanDefinitionalEngine::new();
            let mut policyset = ast::PolicySet::new();
            let policy: ast::StaticPolicy = input.policy.clone().into();
            policyset.add_static(policy.clone()).unwrap();
            debug!("Schema: {}\n", input.schema.schemafile_string());
            debug!("Policies: {policyset}\n");
            debug!("Entities: {}\n", input.entities);

            let requests = input
                .requests
                .clone()
                .into_iter()
                .map(Into::into)
                .collect::<Vec<_>>();

            for request in requests.iter().cloned() {
                debug!("Request : {request}");
                let (rust_res, total_dur) = time_function(|| {
                    run_auth_test(&def_impl, request, &policyset, &input.entities)
                });

                info!("{}{}", TOTAL_MSG, total_dur.as_nanos());

                // additional invariant:
                // type-directed fuzzing should never produce wrong-number-of-arguments errors
                assert_eq!(
                    rust_res
                        .diagnostics
                        .errors
                        .iter()
                        .map(ToString::to_string)
                        .filter(|err| err.contains("wrong number of arguments"))
                        .collect::<Vec<String>>(),
                    Vec::<String>::new()
                );
            }
            if let Ok(_) = std::env::var("DRT_OBSERVABILITY") {
                let obs_out = input.to_fuzz_test_case();
                let dirname = "fuzz/observations";
                let testname = std::env::var("FUZZ_TARGET").unwrap_or("abac-derived".to_string());
                dump_fuzz_test_case(dirname, &testname, &obs_out)
            }
        });
}