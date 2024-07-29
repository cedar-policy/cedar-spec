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

use afl::fuzz;
use arbitrary::{self, Arbitrary, Unstructured};
use ast::PolicyID;
use cedar_afl::{
    dump, dump_fuzz_test_case, run_auth_test, run_eval_test, time_function, FuzzTestCase,
    TestCaseFormat,
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
#[derive(Debug)]
pub struct FuzzTargetInput {
    pub entities: Entities,
    /// generated policy
    pub policy: ast::Policy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [ABACRequest; 8],
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let est_policy: cedar_policy_core::est::Policy = u.arbitrary()?;
        let policy = est_policy
            .try_into_ast_policy(Some(PolicyID::from_string("policy0")))
            .map_err(|e| arbitrary::Error::IncorrectFormat)?;

        Ok(FuzzTargetInput {
            entities: u.arbitrary()?,
            policy: policy,
            requests: u.arbitrary()?,
        })
    }
}

impl TestCaseFormat for FuzzTargetInput {
    fn to_fuzz_test_case(&self) -> FuzzTestCase {
        // Access the serialized expression
        let est_policy: cedar_policy_core::est::Policy = self.policy.clone().into();
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
    fuzz!(|input: FuzzTargetInput| {
        initialize_log();
        let def_impl = LeanDefinitionalEngine::new();
        let policy = input.policy.clone();
        let mut policyset: ast::PolicySet = ast::PolicySet::new();
        let entities = input.entities.clone();
        policyset.add(policy.clone()).unwrap();
        debug!("Policies: {policyset}");
        debug!("Entities: {entities}");
        let requests = input
            .requests
            .clone()
            .into_iter()
            .map(Into::into)
            .collect::<Vec<_>>();

        for request in requests.iter().cloned() {
            debug!("Request: {request}");
            let (_, total_dur) =
                time_function(|| run_auth_test(&def_impl, request, &policyset, &entities));
            info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
        }
        if let Ok(_) = std::env::var("DRT_OBSERVABILITY") {
            let obs_out = input.to_fuzz_test_case();
            let dirname = "fuzz/observations";
            let testname = std::env::var("FUZZ_TARGET").unwrap_or("abac-derived".to_string());
            dump_fuzz_test_case(dirname, &testname, &obs_out)
        }
    });
}
