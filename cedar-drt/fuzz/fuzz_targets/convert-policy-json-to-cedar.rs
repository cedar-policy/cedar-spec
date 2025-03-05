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
use cedar_drt_inner::*;
use cedar_policy_core::est::PolicySetFromJsonError;
use itertools::Itertools;
use thiserror::Error;

#[derive(miette::Diagnostic, Error, Debug)]
enum ESTParseError {
    #[error(transparent)]
    JSONToEST(#[from] serde_json::error::Error),
    #[error(transparent)]
    #[diagnostic(transparent)]
    ESTToAST(#[from] PolicySetFromJsonError),
}

fuzz_target!(|est_json_str: String| {
    // Attempt to deserialize an est policy set from the specified json string
    // Then, convert the est policy set to an ast policy set
    let ast_from_est_result = serde_json::from_str::<serde_json::Value>(&est_json_str)
        .and_then(|val| serde_json::from_value::<cedar_policy_core::est::PolicySet>(val))
        .map_err(ESTParseError::from)
        .and_then(|est| {
            cedar_policy_core::ast::PolicySet::try_from(est).map_err(ESTParseError::from)
        });
    if let Ok(ast_from_est) = ast_from_est_result {
        // Convert the ast policy set to Cedar text, removing linked policies
        let text = ast_from_est.all_templates().join("\n");
        // Parse an ast policy set from the Cedar text
        let ast_from_cedar = cedar_policy_core::parser::parse_policyset(&text);
        match ast_from_cedar {
            Ok(ast_from_cedar) => {
                check_policy_set_equivalence(&ast_from_est, &ast_from_cedar);
            }

            Err(e) => {
                println!("{:?}", miette::Report::new(e));
                panic!("Policy set parsed from est to ast but did not roundtrip ast->text->ast");
            }
        }
    }
});
