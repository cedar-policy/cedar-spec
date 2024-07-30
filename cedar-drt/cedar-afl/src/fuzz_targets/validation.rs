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
    dump, dump_fuzz_test_case, run_auth_test, run_eval_test, run_val_test, time_function,
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
use cedar_policy_validator::{RawName, SchemaFragment};
use log::{debug, info};
use serde::Serialize;
use serde_json::json;
use std::convert::TryFrom;

/// Input expected by this fuzz target
#[derive(Debug, Clone, Serialize)]
pub struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    /// generated policy
    pub policy: ABACPolicy,
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
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self { schema, policy })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ])
    }
}

impl TestCaseFormat for FuzzTargetInput {
    fn to_fuzz_test_case(&self) -> FuzzTestCase {
        // Access the serialized expression
        let est_policy: cedar_policy_core::est::Policy = self.policy.0.clone().into();
        let representation = json!({
            "schema": self.schema.schema,
            "policy": est_policy,
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
        let mut obs_out = input.to_fuzz_test_case();

        // generate a schema
        if let Ok(schema) = ValidatorSchema::try_from(input.schema.clone()) {
            debug!("Schema: {:?}", schema);

            let policy = input.policy.clone();
            let mut policyset = ast::PolicySet::new();
            policyset.add_static(policy.into()).unwrap();
            debug!("Policies: {policyset}");

            // run the policy through both validators and compare the result
            let (_, total_dur) = time_function(|| {
                run_val_test(&def_impl, schema, &policyset, ValidationMode::Strict)
            });
            info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
        } else {
            obs_out.status = "invalid".to_string();
            obs_out.status_reason = "schema could not be converted to ValidatorSchema".to_string();
        }
        if let Ok(_) = std::env::var("DRT_OBSERVABILITY") {
            let dirname = "fuzz/observations";
            let testname = std::env::var("FUZZ_TARGET").unwrap_or("validation-derived".to_string());
            dump_fuzz_test_case(dirname, &testname, &obs_out)
        }
    });
}
