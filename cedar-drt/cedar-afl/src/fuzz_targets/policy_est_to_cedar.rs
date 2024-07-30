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
use cedar_afl::{
    check_policy_equivalence, check_policy_est_parse_bugs, dump_fuzz_test_case, FuzzTestCase,
    TestCaseFormat,
};
use cedar_policy_generators::{
    hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use serde::Serialize;
use serde_json::json;
use thiserror::Error;

use cedar_policy_core::{ast::PolicyID, est::FromJsonError};

#[derive(miette::Diagnostic, Error, Debug)]
enum ESTParseError {
    #[error(transparent)]
    JSONToEST(#[from] serde_json::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ESTToAST(#[from] FromJsonError),
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
        let est_policy: cedar_policy_core::est::Policy = policy.into();
        let est_json =
            serde_json::to_string(&est_policy).map_err(|e| arbitrary::Error::IncorrectFormat)?;
        let est_from_str = serde_json::from_str::<cedar_policy_core::est::Policy>(&est_json)
            .map_err(|e| arbitrary::Error::IncorrectFormat)?;
        Ok(Self {
            policy: est_from_str,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ])
    }
}

impl TestCaseFormat for FuzzTargetInput {
    fn to_fuzz_test_case(&self) -> FuzzTestCase {
        // Access the serialized expression
        let representation = json!({
            "policy": self.policy,
        });
        FuzzTestCase {
            representation: representation.to_string(),
            ..Default::default()
        }
    }
}

/// Input expected by this fuzz target:
/// A policy EST
#[derive(Debug, Clone, Serialize)]
pub struct FuzzTargetInput {
    /// generated policy
    pub policy: cedar_policy_core::est::Policy,
}

fn main() {
    fuzz!(|input: FuzzTargetInput| {
        let mut obs_out = input.to_fuzz_test_case();
        if let Ok(ast_from_est) = input
            .clone()
            .policy
            .try_into_ast_template(Some(PolicyID::from_string("policy0")))
            .map_err(ESTParseError::from)
        {
            let ast_from_cedar =
                cedar_policy_core::parser::parse_policy_template(None, &ast_from_est.to_string());

            match ast_from_cedar {
                Ok(ast_from_cedar) => {
                    check_policy_equivalence(&ast_from_est, &ast_from_cedar);
                }

                Err(e) => {
                    obs_out.status = "invalid".to_string();
                    obs_out.status_reason =
                        "policy parsed from est to ast but did not roundtrip ast->text->ast"
                            .to_string();
                    // println!("{:?}", miette::Report::new(e));
                    // panic!(
                    //     "Policy parsed from est to ast but did not roundtrip ast->text->ast"
                    // );
                }
            }
        } else {
            obs_out.status = "invalid".to_string();
            obs_out.status_reason = "est to ast conversion failed".to_string();
        }
        if let Ok(_) = std::env::var("DRT_OBSERVABILITY") {
            let dirname = "fuzz/observations";
            let testname =
                std::env::var("FUZZ_TARGET").unwrap_or("convert-policy-est-to-cedar".to_string());
            dump_fuzz_test_case(dirname, &testname, &obs_out)
        }
    });
}
