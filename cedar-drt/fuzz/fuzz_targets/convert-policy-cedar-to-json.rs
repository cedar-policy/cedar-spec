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
use cedar_policy_core::est;
use cedar_policy_core::parser;

#[derive(miette::Diagnostic, Error, Debug)]
enum ESTParseError {
    #[error(transparent)]
    #[diagnostic(transparent)]
    CSTToEST(#[from] parser::err::ParseErrors),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ESTToAST(#[from] est::PolicySetFromJsonError),
}

// Given some Cedar source, assert that parsing it directly (parsing to CST,
// then converting CST to AST) gives the same result of parsing via EST (parsing
// to CST, converting CST to EST, and then converting EST to AST).
fuzz_target!(|src: String| {
    // text -> cst
    if let Ok(cst_node) = cedar_policy_core::parser::text_to_cst::parse_policies(&src) {
        // cst -> ast
        match cst_node.to_policyset() {
            Ok(ast_from_cst) => {
                cst_node
                    .clone()
                    .node
                    .expect("AST construction should fail for missing CST node");
                // cst -> est -> ast
                let ast_from_est_result: Result<_, ESTParseError> = cst_node
                    .try_into()
                    .map_err(|e: parser::err::ParseErrors| e.into())
                    .and_then(|est: est::PolicySet| est.try_into().map_err(ESTParseError::from));
                match ast_from_est_result {
                    Ok(ast_from_est) => {
                        check_policy_set_equivalence(&ast_from_cst, &ast_from_est);
                    }
                    Err(e) => {
                        println!("{:?}", miette::Report::new(e));
                        panic!(
                            "Policy set parsed directly through cst->ast but not through cst->est->ast"
                        );
                    }
                }
            }
            Err(errs) => check_for_internal_errors(errs),
        }
    }
});
