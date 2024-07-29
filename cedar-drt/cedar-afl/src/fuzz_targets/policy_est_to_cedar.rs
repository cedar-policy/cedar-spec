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

use std::path::Path;

use afl::fuzz;
use arbitrary::{Arbitrary, Unstructured};
use cedar_afl::{
    check_policy_equivalence, check_policy_est_parse_bugs, dump_fuzz_test_case, FuzzTestCase,
    TestCaseFormat,
};
use serde::Serialize;
use serde_json::{json, Value};
use thiserror::Error;

use cedar_policy_core::{ast::PolicyID, est::FromJsonError};
use std::io::Write;

#[derive(miette::Diagnostic, Error, Debug)]
enum ESTParseError {
    #[error(transparent)]
    JSONToEST(#[from] serde_json::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ESTToAST(#[from] FromJsonError),
}

/// Input expected by this fuzz target:
/// A policy EST
#[derive(Debug, Clone, Serialize)]
pub struct FuzzTargetInput {
    /// generated policy
    pub policy: cedar_policy_core::est::Policy,
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

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let policy: cedar_policy_core::est::Policy = u.arbitrary()?;
        let est_json =
            serde_json::to_string(&policy).map_err(|e| arbitrary::Error::IncorrectFormat)?;
        let est_from_str = serde_json::from_str::<cedar_policy_core::est::Policy>(&est_json)
            .map_err(|e| arbitrary::Error::IncorrectFormat)?;
        Ok(FuzzTargetInput {
            policy: est_from_str,
        })
    }
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
