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
use thiserror::Error;

use cedar_drt_inner::*;
use cedar_policy::ParseErrors;
use cedar_policy_core::{ast::PolicyID, est::FromJsonError};

#[derive(miette::Diagnostic, Error, Debug)]
enum ESTParseError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    CSTToEST(#[from] ParseErrors),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ESTToAST(#[from] FromJsonError),
}

// Given some Cedar source, assert that parsing it directly (parsing to CST,
// then converting CST to AST) gives the same result of parsing via EST (parsing
// to CST, converting CST to EST, and then converting EST to AST).
fuzz_target!(|src: String| {
    if let Ok(cst) = cedar_policy_core::parser::text_to_cst::parse_policy(&src) {
        let mut ast_errors = ParseErrors::new();
        let policy_ast = cst.to_policy_template(PolicyID::from_string("policy0"), &mut ast_errors);
        if let Some(cst_node) = cst.node {
            let policy_est: Result<_, ESTParseError> = cst_node
                .try_into()
                .map_err(|e: ParseErrors| e.into())
                .and_then(|est: cedar_policy_core::est::Policy| {
                    est.try_into_ast_template(Some(PolicyID::from_string("policy0")))
                        .map_err(|e| e.into())
                });

            match (policy_ast, policy_est) {
                (Some(policy_ast), Ok(policy_est)) => {
                    check_policy_equivalence(&policy_ast, &policy_est);
                }

                (None, Ok(_)) => {
                    println!("{:?}", miette::Report::new(ast_errors));
                    panic!("Policy parsed through cst->est->ast but not directly through cst->ast");
                }
                (Some(_), Err(e)) => {
                    println!("{:?}", miette::Report::new(e));
                    panic!("Policy parsed directly through cst->ast but not through cst->est->ast");
                }

                // Both conversion error
                (None, Err(_)) => (),
            }
        }
    }
});
