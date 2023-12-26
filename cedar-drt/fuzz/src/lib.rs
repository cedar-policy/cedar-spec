/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
mod prt;

pub use dump::*;
pub use prt::*;

use cedar_drt::{time_function, CedarTestImplementation, RUST_AUTH_MSG, RUST_VALIDATION_MSG};
use cedar_policy::frontend::is_authorized::InterfaceResponse;
use cedar_policy_core::ast;
use cedar_policy_core::authorizer::{Authorizer, Diagnostics, Response};
use cedar_policy_core::entities::{Entities, NoEntitiesSchema, TCComputation};
use cedar_policy_core::evaluator::{EvaluationErrorKind, Evaluator};
use cedar_policy_core::extensions::Extensions;
pub use cedar_policy_validator::{ValidationErrorKind, ValidationMode, Validator, ValidatorSchema};
use libfuzzer_sys::arbitrary::{self, Unstructured};
use log::info;

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
    let eval = Evaluator::new(request.clone(), entities, &exts);
    let expected = match eval.interpret(expr, &std::collections::HashMap::default()) {
        Ok(v) => Some(v),
        Err(e) if matches!(e.error_kind(), EvaluationErrorKind::IntegerOverflow(_)) => {
            // TODO(#172): For now, we ignore tests where `cedar-policy` returns an integer
            // overflow error. Once we migrate to Lean this should be unnecessary.
            return;
        }
        Err(_) => None,
    };

    // `custom_impl.interpret()` returns true when the result of evaluating `expr`
    // matches `expected`
    let definitional_res = custom_impl.interpret(request.clone(), entities, expr, expected.clone());

    // TODO(#175): For now, ignore cases where the definitional code returned an error due to
    // an unknown extension function.
    if let Err(err) = definitional_res.clone() {
        if err.contains("jsonToExtFun: unknown extension function") {
            return;
        }
    }

    // Otherwise, `definitional_res` should be `Ok(true)`
    assert_eq!(
        definitional_res,
        Ok(true),
        "Incorrect evaluation result for {request}\nExpression:\n{expr}\nEntities:\n{entities}\nExpected value:\n{:?}\n",
        expected
    )
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

    // TODO(#172): For now, we ignore tests where `cedar-policy` returns an integer
    // overflow error. Once we migrate to Lean this should be unnecessary.
    if rust_res
        .diagnostics
        .errors
        .iter()
        .any(|e| e.to_string().contains("integer overflow"))
    {
        return rust_res;
    }

    let definitional_res = custom_impl.is_authorized(request.clone(), policies, entities);

    match definitional_res {
        Err(err) => {
            // TODO(#175): For now, ignore cases where the Lean code returned an error due to
            // an unknown extension function.
            if err.contains("jsonToExtFun: unknown extension function") {
                rust_res
            } else {
                panic!(
                "Unexpected parse error for {request}\nPolicies:\n{}\nEntities:\n{}\nError: {err}",
                &policies, &entities
            );
            }
        }
        Ok(definitional_res) => {
            // Otherwise, the definitional engine should return a result that matches `rust_res`.
            let rust_res_for_comparison: cedar_policy::Response = Response {
                diagnostics: Diagnostics {
                    errors: Vec::new(),
                    ..rust_res.clone().diagnostics
                },
                ..rust_res
            }
            .into();
            assert_eq!(
                InterfaceResponse::from(rust_res_for_comparison),
                definitional_res,
                "Mismatch for {request}\nPolicies:\n{}\nEntities:\n{}",
                &policies,
                &entities
            );
            rust_res

            // TODO(#69): Our current definitional engine does not return authorization
            // errors, so those are not checked for equality.
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

    // If `cedar-policy` does not return an error, then the spec should not return an error.
    // This implies type soundness of the `cedar-policy` validator since type soundness of the
    // spec is formally proven.
    //
    // In particular, we have proven that if the spec validator does not return an error (B),
    // then there are no authorization-time errors modulo some restrictions (C). So (B) ==> (C).
    // DRT checks that if the `cedar-policy` validator does not return an error (A), then neither
    // does the spec validator (B). So (A) ==> (B). By transitivity then, (A) ==> (C).

    if rust_res.validation_passed() {
        match definitional_res {
            Err(err) => {
                // TODO(#175): For now, ignore cases where the Lean code returned an error due to
                // an unknown extension function.
                if !err.contains("jsonToExtFun: unknown extension function") {
                    panic!(
                        "Unexpected parse error\nPolicies:\n{}\nSchema:\n{:?}\nError: {err}",
                        &policies, schema
                    );
                }
            }
            Ok(definitional_res) => {
                // The definitional validator may return "impossiblePolicy" due to greater precision.
                // If the definitional validator returns "impossiblePolicy" then the input expression is
                // well-typed, although it is guaranteed to always evaluate to false.
                if definitional_res.validation_errors.contains(&"impossiblePolicy".to_string()) {
                    return;
                }

                // But the definitional validator should not return any other error.
                assert!(
                    definitional_res.validation_passed(),
                    "Mismatch for Policies:\n{}\nSchema:\n{:?}\ncedar-policy response: {:?}\nTest engine response: {:?}\n",
                    &policies,
                    schema,
                    rust_res,
                    definitional_res,
                );

                // TODO(#69): We currently don't check for a relationship between validation errors.
                // E.g., the error reported by the definitional validator should be in the list
                // of errors reported by the production validator, but we don't check this.
            }
        }
    }
}

#[test]
fn test_run_auth_test() {
    use cedar_drt::JavaDefinitionalEngine;
    use cedar_policy_core::ast::{Entity, EntityUID, RequestSchemaAllPass, RestrictedExpr};
    use cedar_policy_core::entities::{NoEntitiesSchema, TCComputation};
    use smol_str::SmolStr;

    let java_def_engine =
        JavaDefinitionalEngine::new().expect("failed to create definitional engine");
    let principal = ast::EntityUIDEntry::Known(std::sync::Arc::new(
        EntityUID::with_eid_and_type("User", "alice").unwrap(),
    ));
    let action = ast::EntityUIDEntry::Known(std::sync::Arc::new(
        EntityUID::with_eid_and_type("Action", "view").unwrap(),
    ));
    let resource = ast::EntityUIDEntry::Known(std::sync::Arc::new(
        EntityUID::with_eid_and_type("Photo", "vacation").unwrap(),
    ));
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

    let static_policy =
        cedar_policy_core::parser::parse_policy(Some("policy0".into()), policy_string)
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
    run_auth_test(&java_def_engine, query, &policies, &entities);
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
