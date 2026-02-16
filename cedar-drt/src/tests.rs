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

use cedar_testing::cedar_test_impl::{
    CedarTestImplementation, ErrorComparisonMode, TestResult, TestValidationResult,
    ValidationComparisonMode, time_function,
};

use cedar_policy::{
    AuthorizationError, Authorizer, Entities, Expression, PolicySet, Request, Response, Schema,
    ValidationError, ValidationMode, ValidationResult, Validator, eval_expression, ffi,
};

use libfuzzer_sys::arbitrary::{self, Unstructured};
use log::info;
use miette::miette;
use std::collections::HashSet;

/// Times for cedar-policy authorization and validation.
pub const RUST_AUTH_MSG: &str = "rust_auth (ns) : ";
pub const RUST_VALIDATION_MSG: &str = "rust_validation (ns) : ";
pub const RUST_ENT_VALIDATION_MSG: &str = "rust_entity_validation (ns) : ";
pub const RUST_REQ_VALIDATION_MSG: &str = "rust_request_validation (ns) : ";

pub fn run_eval_test(
    custom_impl: &impl CedarTestImplementation,
    request: &Request,
    expr: &Expression,
    entities: &Entities,
) {
    let expected = eval_expression(request, entities, expr).ok();

    // `custom_impl.interpret()` returns true when the result of evaluating `expr`
    // matches `expected`
    let definitional_res = custom_impl.interpret(request, entities, expr, expected.clone());

    match definitional_res {
        TestResult::Failure(err) => {
            // TODO(#175): Ignore cases where the definitional code returned an error due to
            // an unknown extension function.
            if err.contains("unknown extension function") {
                return;
            }
            // No other errors are expected
            panic!("Unexpected error for {request}\nExpression: {expr}\nError: {err}");
        }
        TestResult::Success(response) => {
            // The definitional interpreter response should be `true`
            assert!(
                response,
                "Incorrect evaluation result for {request}\nExpression: {expr}\nEntities:\n{}\nExpected value:\n{:?}\n",
                entities.as_ref(),
                expected
            )
        }
    }
}

/// Compare the behavior of the authorizer in `cedar-policy` against a custom Cedar
/// implementation. Panics if the two do not agree. Returns the response that
/// the two agree on.
pub fn run_auth_test(
    custom_impl: &impl CedarTestImplementation,
    request: &Request,
    policies: &PolicySet,
    entities: &Entities,
) -> Response {
    let authorizer = Authorizer::new();
    let (rust_res, rust_auth_dur) =
        time_function(|| authorizer.is_authorized(request, policies, entities));
    info!("{}{}", RUST_AUTH_MSG, rust_auth_dur.as_nanos());

    let definitional_res = custom_impl.is_authorized(request, policies, entities);

    match definitional_res {
        TestResult::Failure(err) => {
            // TODO(#175): For now, ignore cases where the Lean code returned an error due to
            // an unknown extension function.
            if err.contains("unknown extension function") {
                rust_res
            } else {
                panic!(
                    "Unexpected error for {request}\nPolicies:\n{}\nEntities:\n{}\nError: {err}",
                    &policies,
                    &entities.as_ref()
                );
            }
        }
        TestResult::Success(definitional_res) => {
            let rust_res_for_comparison: ffi::Response = {
                let errors = match custom_impl.error_comparison_mode() {
                    ErrorComparisonMode::Ignore => HashSet::new(),
                    ErrorComparisonMode::PolicyIds => rust_res
                        .diagnostics()
                        .errors()
                        .cloned()
                        .map(|err| match err {
                            AuthorizationError::PolicyEvaluationError(err) => {
                                ffi::AuthorizationError::new_from_report(
                                    err.policy_id().clone(),
                                    miette!("{}", err.policy_id()),
                                )
                            }
                        })
                        .collect(),
                    ErrorComparisonMode::Full => rust_res
                        .diagnostics()
                        .errors()
                        .cloned()
                        .map(Into::into)
                        .collect(),
                };
                ffi::Response::new(
                    rust_res.decision(),
                    rust_res.diagnostics().reason().cloned().collect(),
                    errors,
                )
            };
            assert_eq!(
                rust_res_for_comparison,
                definitional_res.response,
                "Mismatch for {request}, with error comparison mode {ecmode:?}\nPolicies:\n{policies}\nEntities:\n{es}",
                ecmode = custom_impl.error_comparison_mode(),
                es = entities.as_ref(),
            );
            rust_res
        }
    }
}

/// Compare the behavior of the validator in `cedar-policy` against a custom Cedar
/// implementation. Panics if the two do not agree.
pub fn run_val_test(
    custom_impl: &impl CedarTestImplementation,
    schema: Schema,
    policies: &PolicySet,
    mode: ValidationMode,
) {
    let validator = Validator::new(schema.clone());
    let (rust_res, rust_validation_dur) = time_function(|| validator.validate(policies, mode));
    info!("{}{}", RUST_VALIDATION_MSG, rust_validation_dur.as_nanos());
    let definitional_res = custom_impl.validate(&schema, policies, mode);
    compare_validation_results(
        policies,
        &schema,
        ValidationComparisonMode::AgreeOnAll,
        rust_res,
        definitional_res,
    );
}

pub fn run_level_val_test(
    custom_impl: &impl CedarTestImplementation,
    schema: Schema,
    policies: &PolicySet,
    mode: ValidationMode,
    level: i32,
) {
    let validator = Validator::new(schema.clone());
    let (rust_res, rust_validation_dur) =
        time_function(|| validator.validate_with_level(policies, mode, level as u32));
    info!("{}{}", RUST_VALIDATION_MSG, rust_validation_dur.as_nanos());
    let definitional_res = custom_impl.validate_with_level(&schema, policies, mode, level);
    compare_validation_results(
        policies,
        &schema,
        ValidationComparisonMode::AgreeOnAll,
        rust_res,
        definitional_res,
    );
}

fn compare_validation_results(
    policies: &PolicySet,
    schema: &Schema,
    comparison_mode: ValidationComparisonMode,
    rust_res: ValidationResult,
    definitional_res: TestResult<TestValidationResult>,
) {
    match definitional_res {
        TestResult::Failure(err) => {
            // TODO(#175): For now, ignore cases where the Lean code returned an error due to
            // an unknown extension function.
            if !err.contains("unknown extension function")
                && !err.contains("unknown extension type")
            {
                panic!(
                    "Unexpected error\nPolicies:\n{}\nSchema:\n{:?}\nError: {err}",
                    &policies, schema
                );
            }
        }
        TestResult::Success(definitional_res) => {
            // `InvalidActionApplication` is never reported by Lean
            let rust_passed = rust_res
                .validation_errors()
                .all(|e| matches!(e, ValidationError::InvalidActionApplication(_)));
            if rust_passed {
                // If `cedar-policy` does not return an error, then the spec should not return an error.
                // This implies type soundness of the `cedar-policy` validator since type soundness of the
                // spec is formally proven.
                //
                // In particular, we have proven that if the spec validator does not return an error (B),
                // then there are no authorization-time errors modulo some restrictions (C). So (B) ==> (C).
                // DRT checks that if the `cedar-policy` validator does not return an error (A), then neither
                // does the spec validator (B). So (A) ==> (B). By transitivity then, (A) ==> (C).
                assert!(
                    definitional_res.validation_passed(),
                    "Mismatch for Policies:\n{}\nSchema:\n{:?}\ncedar-policy response: {:?}\nTest engine response: {:?}\n",
                    &policies,
                    schema,
                    miette::Report::new(rust_res),
                    definitional_res,
                );
            } else {
                // If `cedar-policy` returns an error, then only check the spec response
                // if the validation comparison mode is `AgreeOnAll`.
                match comparison_mode {
                    ValidationComparisonMode::AgreeOnAll => {
                        assert!(
                            !definitional_res.validation_passed(),
                            "Mismatch for Policies:\n{}\nSchema:\n{:?}\ncedar-policy response:\n{:?}\nTest engine response: {:?}\n",
                            &policies,
                            schema,
                            miette::Report::new(rust_res),
                            definitional_res,
                        );
                    }
                    ValidationComparisonMode::AgreeOnValid => {} // ignore
                };
            }
        }
    }
}

pub fn run_ent_val_test(
    custom_impl: &impl CedarTestImplementation,
    schema: Schema,
    entities: Entities,
) {
    let (rust_res, rust_auth_dur) =
        time_function(|| Entities::from_entities(entities.iter().cloned(), Some(&schema)));
    info!("{}{}", RUST_ENT_VALIDATION_MSG, rust_auth_dur.as_nanos());
    match custom_impl.validate_entities(&schema, &entities) {
        TestResult::Failure(e) => {
            panic!("failed to execute entity validation: {e}");
        }
        TestResult::Success(definitional_res) => {
            if rust_res.is_ok() {
                assert!(
                    definitional_res.validation_passed(),
                    "Definitional Errors: {:?}\n, Rust output: {:?}",
                    definitional_res.errors,
                    rust_res.unwrap()
                );
            } else {
                assert!(
                    !definitional_res.validation_passed(),
                    "Errors: {:?}",
                    definitional_res.errors
                );
            }
        }
    }
}

pub fn run_req_val_test(
    custom_impl: &impl CedarTestImplementation,
    schema: Schema,
    request: Request,
) {
    let (rust_res, rust_auth_dur) = time_function(|| {
        Request::new(
            request.principal().unwrap().clone(),
            request.action().unwrap().clone(),
            request.resource().unwrap().clone(),
            request.context().unwrap().clone(),
            Some(&schema),
        )
    });
    info!("{}{}", RUST_REQ_VALIDATION_MSG, rust_auth_dur.as_nanos());

    match custom_impl.validate_request(&schema, &request) {
        TestResult::Failure(e) => {
            panic!("failed to execute request validation: {e}");
        }
        TestResult::Success(definitional_res) => {
            if rust_res.is_ok() {
                assert!(
                    definitional_res.validation_passed(),
                    "Definitional Errors: {:?}\n, Rust output: {:?}",
                    definitional_res.errors,
                    rust_res.unwrap()
                );
            } else {
                assert!(
                    !definitional_res.validation_passed(),
                    "Errors: {:?}",
                    definitional_res.errors
                );
            }
        }
    }
}

/// Randomly drop some of the entities from the list so the generator can produce
/// some invalid references.
pub fn drop_some_entities(
    entities: Entities,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<Entities> {
    let should_drop: bool = u.arbitrary()?;
    if should_drop {
        let mut set: Vec<_> = vec![];
        for entity in entities.iter() {
            match u.int_in_range(0..=9)? {
                0 => (),
                _ => {
                    set.push(entity.clone());
                }
            }
        }
        Ok(Entities::from_entities(set, None).expect("Should be valid"))
    } else {
        Ok(entities)
    }
}
