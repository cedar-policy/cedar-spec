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
use arbitrary::{Arbitrary, Unstructured};
use ast::Expr;
use cedar_afl::{dump_fuzz_test_case, run_eval_test, FuzzTestCase, TestCaseFormat};
use cedar_drt::*;
use cedar_policy_generators::{abac::ABACRequest, settings::ABACSettings};
use log::debug;
use serde::Serialize;
use serde_json::json;
use utils::expr_to_est;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone, Serialize, Arbitrary)]
pub struct FuzzTargetInput {
    /// generated schema
    // #[serde(skip)]
    // pub schema: Schema,
    /// generated entity slice
    #[serde(skip)]
    pub entities: Entities,
    /// generated expression
    #[serde(serialize_with = "expr_to_est")]
    pub expression: Expr,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    #[serde(skip)]
    pub request: ABACRequest,
}

impl TestCaseFormat for FuzzTargetInput {
    fn to_fuzz_test_case(&self) -> FuzzTestCase {
        // Access the serialized expression
        let representation = json!({
            "entities": self.entities,
            "expression": self.expression,
            "request": format!("{}", &self.request),
        });
        FuzzTestCase {
            representation: representation.to_string(),
            ..Default::default()
        }
    }
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

// Type-directed fuzzing of expression evaluation.
fn main() {
    fuzz!(|input: FuzzTargetInput| {
        let obs_out = input.to_fuzz_test_case();
        initialize_log();
        let def_impl = LeanDefinitionalEngine::new();
        debug!("expr: {}\n", input.expression);
        debug!("Entities: {}\n", input.entities);
        run_eval_test(
            &def_impl,
            input.request.clone().into(),
            &input.expression,
            &input.entities,
            SETTINGS.enable_extensions,
        );
        if let Ok(_) = std::env::var("DRT_OBSERVABILITY") {
            let dirname = "fuzz/observations";
            let testname = std::env::var("FUZZ_TARGET").unwrap_or("eval-derived".to_string());
            dump_fuzz_test_case(dirname, &testname, &obs_out)
        }
    });
}
