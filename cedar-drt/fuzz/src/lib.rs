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
use cedar_policy_core::entities::Entities;
use cedar_policy_core::evaluator::{EvaluationErrorKind, Evaluator};
use cedar_policy_core::extensions::Extensions;
pub use cedar_policy_validator::{ValidationErrorKind, ValidationMode, Validator, ValidatorSchema};
use log::info;

/// Compare the behavior of the evaluator in cedar-policy against a custom Cedar
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
            // ignore the input if it results in an integer overflow error
            return;
        }
        Err(_) => None,
    };
    // custom_impl.interpret() returns true when the result of evaluating expr
    // matches the expected value v
    assert!(custom_impl.interpret(request, entities, expr, expected))
}

/// Compare the behavior of the authorizer in cedar-policy against a custom Cedar
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

    // For now, we ignore tests where cedar-policy returns an integer
    // overflow error.
    if rust_res
        .diagnostics
        .errors
        .iter()
        .any(|e| e.to_string().contains("integer overflow"))
    {
        return rust_res;
    }

    // Important that we return the cedar-policy response, with its rich errors,
    // in case the caller wants to expect those.
    let ret = rust_res.clone();

    let definitional_res = custom_impl.is_authorized(request.clone(), policies, entities);
    // For now, we expect never to receive errors from the definitional engine,
    // and we otherwise ignore errors in the comparison.
    assert_eq!(
        definitional_res
            .diagnostics()
            .errors()
            .map(ToString::to_string)
            .collect::<Vec<String>>(),
        Vec::<String>::new()
    );

    let rust_res_for_comparison: cedar_policy::Response = Response {
        diagnostics: Diagnostics {
            errors: Vec::new(),
            ..rust_res.diagnostics
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
    ret
}

/// Compare the behavior of the validator in cedar-policy against a custom Cedar
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

    assert!(
        definitional_res.parsing_succeeded(),
        "JSON parsing failed for:\nPolicies:\n{}\nSchema:\n{:?}\ncedar-policy response: {:?}\nTest engine response: {:?}\n",
        &policies,
        schema,
        rust_res,
        definitional_res
    );

    // Temporary fix to ignore a known mismatch between the Dafny and Rust.
    // The issue is that the Rust code will always return an error for an
    // unrecognized entity or action, even if that part of the expression
    // should be excluded from typechecking (e.g., `true || Undefined::"foo"`
    // should be well typed due to short-circuiting).
    if rust_res.validation_errors().any(|e| {
        matches!(
            e.error_kind(),
            ValidationErrorKind::UnrecognizedEntityType(_)
                | ValidationErrorKind::UnrecognizedActionId(_)
        )
    }) {
        return;
    }

    assert_eq!(
        rust_res.validation_passed(),
        definitional_res.validation_passed(),
        "Mismatch for Policies:\n{}\nSchema:\n{:?}\ncedar-policy response: {:?}\nTest engine response: {:?}\n",
        &policies,
        schema,
        rust_res,
        definitional_res,
    );
    // NOTE: We currently don't check for a relationship between validation errors.
    // E.g., the error reported by the definitional validator should be in the list
    // of errors reported by the production validator, but we don't check this.
}

#[test]
fn test_run_auth_test() {
    use cedar_drt::JavaDefinitionalEngine;
    use cedar_policy_core::ast::{Entity, EntityUID, RequestSchemaAllPass, RestrictedExpr};
    use cedar_policy_core::entities::{NoEntitiesSchema, TCComputation};
    use smol_str::SmolStr;

    let java_def_engine =
        JavaDefinitionalEngine::new().expect("failed to create definitional engine");
    let principal = ast::EntityUIDEntry::Concrete(std::sync::Arc::new(
        EntityUID::with_eid_and_type("User", "alice").unwrap(),
    ));
    let action = ast::EntityUIDEntry::Concrete(std::sync::Arc::new(
        EntityUID::with_eid_and_type("Action", "view").unwrap(),
    ));
    let resource = ast::EntityUIDEntry::Concrete(std::sync::Arc::new(
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
        std::collections::HashMap::from_iter([
        ("foo".into(), RestrictedExpr::val(cedar_policy_core::ast::Literal::Bool(true)))
        ]);
    let entity_alice = Entity::new(
        EntityUID::with_eid_and_type("User", "alice").unwrap(),
        alice_attributes,
        std::collections::HashSet::new(),
        &Extensions::all_available(),
    ).unwrap();
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
