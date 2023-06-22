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

#[macro_use]
extern crate cedar_policy_generators;
use cedar_policy_generators::{accum, gen_inner};

mod schema;
pub use schema::*;

mod dump;
pub use dump::*;
mod prt;
pub use prt::*;

use cedar_drt::{
    time_function, DefinitionalEngine, DefinitionalValidator, RUST_AUTH_MSG, RUST_VALIDATION_MSG,
};
use cedar_policy_core::ast;
use cedar_policy_core::ast::PolicySet;
use cedar_policy_core::authorizer::{Authorizer, Diagnostics, Response};
use cedar_policy_core::entities::Entities;
pub use cedar_policy_validator::{ValidationErrorKind, ValidationMode, Validator, ValidatorSchema};
use log::info;

pub struct DifferentialTester<'e> {
    /// Rust engine instance
    authorizer: Authorizer,
    /// Definitional engine instance
    def_engine: DefinitionalEngine<'e>,
    /// Definitional validator instance
    def_validator: DefinitionalValidator<'e>,
}

impl<'e> Default for DifferentialTester<'e> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'e> DifferentialTester<'e> {
    /// Create a new `DifferentialTester`.
    ///
    /// Relatively expensive operation / large object, avoid calling this a lot
    pub fn new() -> Self {
        Self {
            authorizer: Authorizer::new(),
            def_engine: DefinitionalEngine::new().expect("failed to create definitional engine"),
            def_validator: DefinitionalValidator::new()
                .expect("failed to create definitional validator"),
        }
    }

    /// Differentially test the given authorization request.
    /// Panics if the two engines do not agree.
    /// Returns the response which the engines agree on.
    pub fn run_single_test(
        &self,
        q: &ast::Request,
        policies: &PolicySet,
        entities: &Entities,
    ) -> Response {
        let (rust_res, rust_auth_dur) =
            time_function(|| self.authorizer.is_authorized(q, policies, entities));
        info!("{}{}", RUST_AUTH_MSG, rust_auth_dur.as_nanos());

        // For now, we ignore all tests where the Rust side returns an integer
        // overflow error, as the behavior between Rust and Dafny is
        // intentionally different
        if rust_res
            .diagnostics
            .errors
            .iter()
            .any(|e| e.contains("integer overflow"))
        {
            return rust_res;
        }

        // very important that we return the Rust response, with its rich errors,
        // in case the caller wants to expect those. (and not the definitional
        // response, which as of this writing contains less-rich errors)
        let ret = rust_res.clone();

        let definitional_res = self.def_engine.is_authorized(q, policies, entities);
        // for now, we expect never to receive errors from the definitional engine,
        // and we otherwise ignore errors in the comparison
        assert_eq!(definitional_res.diagnostics.errors, Vec::<String>::new());
        let rust_res_for_comparison = Response {
            diagnostics: Diagnostics {
                errors: Vec::new(),
                ..rust_res.diagnostics
            },
            ..rust_res
        };
        assert_eq!(
            rust_res_for_comparison, definitional_res,
            "Mismatch for {q}\nPolicies:\n{}\nEntities:\n{}",
            &policies, &entities
        );
        ret
    }

    /// Differentially test validation on the given policy and schema.
    /// Panics if the two engines do not agree.
    pub fn run_validation(
        &self,
        schema: ValidatorSchema,
        policies: &PolicySet,
        mode: ValidationMode,
    ) {
        let validator = Validator::new(schema.clone());
        let (rust_res, rust_validation_dur) = time_function(|| validator.validate(policies, mode));
        info!("{}{}", RUST_VALIDATION_MSG, rust_validation_dur.as_nanos());

        let definitional_res = self.def_validator.validate(schema.clone(), policies, mode);

        assert!(
            definitional_res.parsing_succeeded(),
            "Dafny json parsing failed for:\nPolicies:\n{}\nSchema:\n{:?}",
            &policies,
            schema
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
            "Mismatch for Policies:\n{}\nSchema:\n{:?}\nRust response: {:?}\nDafny response: {:?}\n",
            &policies,
            schema,
            rust_res,
            definitional_res,
        );
        // NOTE: We currently don't check for a relationship between validation errors.
        // E.g., the error reported by the definitional validator should be in the list
        // of errors reported by the production validator, but we don't check this.
    }
}

#[test]
fn call_def_engine() {
    use cedar_policy_core::ast::{Entity, EntityUID, RestrictedExpr};
    use cedar_policy_core::entities::TCComputation;
    use smol_str::SmolStr;

    let diff_tester = DifferentialTester::new();
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
    );
    let mut policies = PolicySet::new();

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

    let mut alice_attributes: std::collections::HashMap<SmolStr, RestrictedExpr> =
        std::collections::HashMap::new();
    alice_attributes.insert(
        "foo".into(),
        RestrictedExpr::val(cedar_policy_core::ast::Literal::Bool(true)),
    );
    let entity_alice = Entity::new(
        EntityUID::with_eid_and_type("User", "alice").unwrap(),
        alice_attributes,
        std::collections::HashSet::new(),
    );

    let entity_view = Entity::new(
        EntityUID::with_eid_and_type("Action", "view").unwrap(),
        std::collections::HashMap::new(),
        std::collections::HashSet::new(),
    );
    let entity_vacation = Entity::new(
        EntityUID::with_eid_and_type("Photo", "vacation").unwrap(),
        std::collections::HashMap::new(),
        std::collections::HashSet::new(),
    );
    let entities = Entities::from_entities(
        vec![entity_alice, entity_view, entity_vacation],
        TCComputation::AssumeAlreadyComputed,
    )
    .unwrap();
    diff_tester.run_single_test(&query, &policies, &entities);
}
