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
use cedar_policy_core::{ast::PolicyID, est::FromJsonError};

#[derive(miette::Diagnostic, Error, Debug)]
enum ESTParseError {
    #[error(transparent)]
    JSONToEST(#[from] serde_json::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ESTToAST(#[from] FromJsonError),
}

fuzz_target!(|est_json_str: String| {
    if let Ok(ast_from_est) = serde_json::from_str::<cedar_policy_core::est::Policy>(&est_json_str)
        .map_err(|e| ESTParseError::from(e))
        .and_then(|est| {
            est.try_into_ast_template(Some(PolicyID::from_string("policy0")))
                .map_err(|e| ESTParseError::from(e))
        })
    {
        let ast_from_cedar =
            cedar_policy_core::parser::parse_policy_template(None, &ast_from_est.to_string());

        match ast_from_cedar {
            Ok(ast_from_cedar) => {
                check_policy_equivalence(&ast_from_est, &ast_from_cedar);
            }

            Err(e) => {
                println!("{:?}", miette::Report::new(e));
                panic!("Policy parsed from est to ast but did not roundtrip ast->text->ast");
            }
        }
    }
});
