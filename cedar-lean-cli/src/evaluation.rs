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
use crate::err::ExecError;
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Decision, Entities, Expression, PolicySet, Request};

/// Use the lean_ffi to check if the `policyset` allows the given `request`.
pub fn check_is_authorized(
    policyset: &PolicySet,
    entities: &Entities,
    request: &Request,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let auth_response = lean_context.is_authorized(policyset, entities, request)?;
    match auth_response.decision() {
        Decision::Deny if auth_response.determining_policies().len() == 0 => {
            print!("This request was implicitly denied as this request matched no policies")
        }
        Decision::Deny => {
            print!("This request was denies as it matched the following policies:")
        }
        Decision::Allow => {
            print!("This request was allowed as it matched the following policies:")
        }
    }
    for policy in auth_response.determining_policies() {
        print!(" {policy}");
    }
    println!();
    print!("The following policies did not contribute to the decision as they errored during evaluation:");
    for policy in auth_response.erroring_policies() {
        print!(" {policy}");
    }
    println!();
    Ok(())
}

/// Use the lean_ffi to evaluate the input Cedar `Expression` and determine if it equivalent to
/// the provided output Cedar `Expression` (if one was provided); otherwise, print the evaluation of the input.
pub fn evaluate(
    input_expr: &Expression,
    entities: &Entities,
    request: &Request,
    expected_output: Option<&Expression>,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    match expected_output {
        Some(output_expr) => {
            let res = lean_context.check_evaluate(input_expr, entities, request, output_expr)?;
            if res {
                println!("Input expression evaluated to the expected output expression.")
            } else {
                println!("Input expression did not evaluate to the expected output expression.")
            }
            Ok(())
        }
        None => {
            lean_context.print_evaluation(input_expr, entities, request)?;
            Ok(())
        }
    }
}
