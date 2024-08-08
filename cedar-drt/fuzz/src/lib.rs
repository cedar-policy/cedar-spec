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

mod dump;
mod parsing_utils;
mod prt;

pub use dump::*;
pub use parsing_utils::*;
pub use prt::*;
pub mod schemas;

use cedar_policy::ffi;
use cedar_policy::PolicyId;
use cedar_policy_core::ast;
use cedar_policy_core::authorizer::{AuthorizationError, Authorizer, Response};
use cedar_policy_core::entities::{Entities, NoEntitiesSchema, TCComputation};
use cedar_policy_core::evaluator::Evaluator;
use cedar_policy_core::extensions::Extensions;
pub use cedar_policy_validator::{ValidationMode, Validator, ValidatorSchema};
pub use cedar_testing::cedar_test_impl::{
    time_function, CedarTestImplementation, ErrorComparisonMode, TestResult,
    ValidationComparisonMode,
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

/// Compare the behavior of the partial evaluator in `cedar-policy` against a custom Cedar
/// implementation. Panics if the two do not agree. `expr` is the expression to
/// evaluate and `request` and `entities` are used to populate the evaluator.
pub fn run_pe_test(
    custom_impl: &impl CedarTestImplementation,
    request: ast::Request,
    expr: &ast::Expr,
    entities: &Entities,
    enable_extensions: bool,
) {
    let exts = if enable_extensions {
        Extensions::all_available()
    } else {
        Extensions::none()
    };

    let eval = Evaluator::new(request.clone(), entities, exts);
    use cedar_policy_core::ast::PartialValue;
    use cedar_testing::cedar_test_impl::ExprOrValue;
    use log::debug;
    let expected = match eval.partial_interpret(expr, &std::collections::HashMap::default()) {
        Ok(PartialValue::Value(v)) => Some(ExprOrValue::value(v)),
        Ok(PartialValue::Residual(r)) => Some(ExprOrValue::Expr(r)),
        Err(_) => None,
    };
    debug!("Expected: {expected:?}");

    let definitional_res = custom_impl.partial_evaluate(
        &request,
        entities,
        expr,
        enable_extensions,
        expected.clone(),
    );
    match definitional_res {
        TestResult::Failure(err) => {
            // TODO(#175): Ignore cases where the definitional code returned an error due to
            // an unknown extension function.
            if err.contains("jsonToExtFun: unknown extension function") {
                return;
            }
            // No other errors are expected
            panic!("Unexpected error for {request}\nExpression: {expr}\nError: {err}");
        }
        TestResult::Success(response) => {
            // The definitional interpreter response should be `true`
            assert!(
                response,
                "Incorrect evaluation result for {request}\nExpression: {expr}\nEntities:\n{entities}\nExpected value:\n{:?}\n",
                match expected {
                    None => "error".to_string(),
                    Some(e_or_v) => e_or_v.to_string()
                }
            )
        }
    }
}

/// Compare the behavior of the evaluator in `cedar-policy` against a custom Cedar
/// implementation. Panics if the two do not agree. `expr` is the expression to
/// evaluate and `request` and `entities` are used to populate the evaluator.
pub fn run_eval_test(
    custom_impl: &impl CedarTestImplementation,
    request: ast::Request,
    expr: &ast::Expr,
    entities: &Entities,
    enable_extensions: bool,
) {
    let exts = if enable_extensions {
        Extensions::all_available()
    } else {
        Extensions::none()
    };
    let eval = Evaluator::new(request.clone(), entities, exts);
    let expected = match eval.interpret(expr, &std::collections::HashMap::default()) {
        Ok(v) => Some(v),
        Err(_) => None,
    };

    // `custom_impl.interpret()` returns true when the result of evaluating `expr`
    // matches `expected`
    let definitional_res = custom_impl.interpret(
        &request,
        entities,
        expr,
        enable_extensions,
        expected.clone(),
    );

    match definitional_res {
        TestResult::Failure(err) => {
            // TODO(#175): Ignore cases where the definitional code returned an error due to
            // an unknown extension function.
            if err.contains("jsonToExtFun: unknown extension function") {
                return;
            }
            // No other errors are expected
            panic!("Unexpected error for {request}\nExpression: {expr}\nError: {err}");
        }
        TestResult::Success(response) => {
            // The definitional interpreter response should be `true`
            assert!(
                response,
                "Incorrect evaluation result for {request}\nExpression: {expr}\nEntities:\n{entities}\nExpected value:\n{:?}\n",
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
    request: ast::Request,
    policies: &ast::PolicySet,
    entities: &Entities,
) -> Response {
    let authorizer = Authorizer::new();
    let (rust_res, rust_auth_dur) =
        time_function(|| authorizer.is_authorized(request.clone(), policies, entities));
    info!("{}{}", RUST_AUTH_MSG, rust_auth_dur.as_nanos());

    let definitional_res = custom_impl.is_authorized(&request, policies, entities);

    match definitional_res {
        TestResult::Failure(err) => {
            // TODO(#175): For now, ignore cases where the Lean code returned an error due to
            // an unknown extension function.
            if err.contains("jsonToExtFun: unknown extension function") {
                rust_res
            } else {
                panic!(
                    "Unexpected error for {request}\nPolicies:\n{}\nEntities:\n{}\nError: {err}",
                    &policies, &entities
                );
            }
        }
        TestResult::Success(definitional_res) => {
            let rust_res_for_comparison: ffi::Response = {
                let errors = match custom_impl.error_comparison_mode() {
                    ErrorComparisonMode::Ignore => HashSet::new(),
                    ErrorComparisonMode::PolicyIds => rust_res
                        .diagnostics
                        .errors
                        .iter()
                        .cloned()
                        .map(|err| match err {
                            AuthorizationError::PolicyEvaluationError { id, .. } => {
                                ffi::AuthorizationError::new_from_report(
                                    PolicyId::new(id.clone()),
                                    miette!("{id}"),
                                )
                            }
                        })
                        .collect(),
                    ErrorComparisonMode::Full => rust_res
                        .diagnostics
                        .errors
                        .iter()
                        .cloned()
                        .map(Into::into)
                        .collect(),
                };
                ffi::Response::new(
                    rust_res.decision,
                    rust_res
                        .diagnostics
                        .reason
                        .iter()
                        .map(|id| PolicyId::new(id.clone()))
                        .collect(),
                    errors,
                )
            };
            assert_eq!(
                rust_res_for_comparison, definitional_res.response,
                "Mismatch for {request}\nPolicies:\n{}\nEntities:\n{}",
                &policies, &entities
            );
            rust_res
        }
    }
}

/// Compare the behavior of the validator in `cedar-policy` against a custom Cedar
/// implementation. Panics if the two do not agree.
pub fn run_val_test(
    custom_impl: &impl CedarTestImplementation,
    schema: ValidatorSchema,
    policies: &ast::PolicySet,
    mode: ValidationMode,
) {
    let validator = Validator::new(schema.clone());
    let (rust_res, rust_validation_dur) = time_function(|| validator.validate(policies, mode));
    info!("{}{}", RUST_VALIDATION_MSG, rust_validation_dur.as_nanos());

    let definitional_res = custom_impl.validate(&schema, policies, mode);

    match definitional_res {
        TestResult::Failure(err) => {
            // TODO(#175): For now, ignore cases where the Lean code returned an error due to
            // an unknown extension function.
            if !err.contains("jsonToExtFun: unknown extension function") {
                panic!(
                    "Unexpected error\nPolicies:\n{}\nSchema:\n{:?}\nError: {err}",
                    &policies, schema
                );
            }
        }
        TestResult::Success(definitional_res) => {
            if rust_res.validation_passed() {
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
                    rust_res,
                    definitional_res,
                );
            } else {
                // If `cedar-policy` returns an error, then only check the spec response
                // if the validation comparison mode is `AgreeOnAll`.
                match custom_impl.validation_comparison_mode() {
                    ValidationComparisonMode::AgreeOnAll => {
                        assert!(
                            !definitional_res.validation_passed(),
                            "Mismatch for Policies:\n{}\nSchema:\n{:?}\ncedar-policy response: {:?}\nTest engine response: {:?}\n",
                            &policies,
                            schema,
                            rust_res,
                            definitional_res,
                        );
                    }
                    ValidationComparisonMode::AgreeOnValid => {} // ignore
                };
            }
        }
    }
}

pub fn run_req_val_test(
    custom_impl: &impl CedarTestImplementation,
    schema: ValidatorSchema,
    request: ast::Request,
    extensions: Extensions<'_>,
) {
    let (rust_res, rust_auth_dur) = time_function(|| {
        ast::Request::new_with_unknowns(
            request.principal().clone(),
            request.action().clone(),
            request.resource().clone(),
            request.context().cloned(),
            Some(&schema),
            extensions,
        )
    });
    info!("{}{}", RUST_REQ_VALIDATION_MSG, rust_auth_dur.as_nanos());

    let definitional_res = custom_impl.validate_request(&schema, &request);
    match definitional_res {
        TestResult::Failure(_) => {
            panic!("request validation test: failed to parse");
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

pub fn run_ent_val_test(
    custom_impl: &impl CedarTestImplementation,
    schema: ValidatorSchema,
    entities: Entities,
    extensions: Extensions<'_>,
) {
    let (rust_res, rust_auth_dur) = time_function(|| {
        Entities::from_entities(
            entities.iter().cloned(),
            Some(&cedar_policy_validator::CoreSchema::new(&schema)),
            TCComputation::AssumeAlreadyComputed,
            extensions,
        )
    });
    info!("{}{}", RUST_ENT_VALIDATION_MSG, rust_auth_dur.as_nanos());
    let definitional_res = custom_impl.validate_entities(&schema, entities);
    match definitional_res {
        TestResult::Failure(_) => {
            panic!("entity validation test: failed to parse");
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

#[test]
fn test_run_auth_test() {
    use cedar_drt::LeanDefinitionalEngine;
    use cedar_policy_core::ast::{
        Entity, EntityUID, PolicyID, RequestSchemaAllPass, RestrictedExpr,
    }; 
    use cedar_policy_core::entities::{NoEntitiesSchema, TCComputation};
    use smol_str::SmolStr;

    let def_engine = LeanDefinitionalEngine::new();
    let principal = ast::EntityUIDEntry::Known {
        euid: std::sync::Arc::new(EntityUID::with_eid_and_type("User", "alice").unwrap()),
        loc: None,
    };
    let action = ast::EntityUIDEntry::Known {
        euid: std::sync::Arc::new(EntityUID::with_eid_and_type("Action", "view").unwrap()),
        loc: None,
    };
    let resource = ast::EntityUIDEntry::Known {
        euid: std::sync::Arc::new(EntityUID::with_eid_and_type("Photo", "vacation").unwrap()),
        loc: None,
    };
    let query = ast::Request::new_with_unknowns(
        principal,
        action,
        resource,
        Some(cedar_policy_core::ast::Context::empty()),
        None::<&RequestSchemaAllPass>,
        Extensions::all_available(),
    )
    .unwrap();
    let mut policies = ast::PolicySet::new();

    let policy_string = r#"
    permit(principal,action,resource) when
    {
        if principal has foo then
            principal.foo
        else
            false
    };"#;

    let static_policy = cedar_policy_core::parser::parse_policy(
        Some(PolicyID::from_string("policy0")),
        policy_string,
    )
    .expect("Failed to parse");
    let static_policy: cedar_policy_core::ast::Policy = static_policy.into();
    policies
        .add(static_policy)
        .expect("Adding static policy in Policy form should succeed");

    let alice_attributes: std::collections::HashMap<SmolStr, RestrictedExpr> =
        std::collections::HashMap::from_iter([(
            "foo".into(),
            RestrictedExpr::val(cedar_policy_core::ast::Literal::Bool(true)),
        )]);
    let entity_alice = Entity::new(
        EntityUID::with_eid_and_type("User", "alice").unwrap(),
        alice_attributes,
        std::collections::HashSet::new(),
        &Extensions::all_available(),
    )
    .unwrap();
    let entity_view = Entity::new_with_attr_partial_value(
        EntityUID::with_eid_and_type("Action", "view").unwrap(),
        std::collections::HashMap::new(),
        std::collections::HashSet::new(),
    );
    let entity_vacation = Entity::new_with_attr_partial_value(
        EntityUID::with_eid_and_type("Photo", "vacation").unwrap(),
        std::collections::HashMap::new(),
        std::collections::HashSet::new(),
    );
    let entities = Entities::from_entities(
        vec![entity_alice, entity_view, entity_vacation],
        None::<&NoEntitiesSchema>,
        TCComputation::AssumeAlreadyComputed,
        Extensions::all_available(),
    )
    .unwrap();
    run_auth_test(&def_engine, query, &policies, &entities);
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
        Ok(Entities::from_entities(
            set,
            None::<&NoEntitiesSchema>,
            TCComputation::AssumeAlreadyComputed,
            Extensions::all_available(),
        )
        .expect("Should be valid"))
    } else {
        Ok(entities)
    }
}
