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

mod abac;
pub use abac::*;
mod rbac;
pub use rbac::*;
mod schema;
pub use schema::*;

mod dump;
pub use dump::*;
mod prt;
pub use prt::*;

pub mod gen;

use std::fmt::Display;

use ast::{
    Effect, EntityUID, Expr, Id, PolicyID, PolicySet, RestrictedExpr, StaticPolicy,
};
use cedar_drt::{
    time_function, DefinitionalEngine, DefinitionalValidator, RUST_AUTH_MSG, RUST_VALIDATION_MSG,
};
use cedar_policy_core::ast;
use cedar_policy_core::ast::{PrincipalConstraint, ResourceConstraint, Template};
use cedar_policy_core::authorizer::{Authorizer, Diagnostics, Response};
use cedar_policy_core::entities::Entities;
use cedar_policy_generators::collections::HashMap;
use cedar_policy_generators::err::Result;
use cedar_policy_generators::hierarchy::Hierarchy;
use cedar_policy_generators::size_hint_utils::size_hint_for_ratio;
pub use cedar_policy_validator::{ValidationErrorKind, ValidationMode, Validator, ValidatorSchema};
use libfuzzer_sys::arbitrary::{self, Unstructured};
use log::info;
use smol_str::SmolStr;

#[derive(Debug, Clone)]
// `GeneratedPolicy` is now a bit of a misnomer: it may have slots depending on
// how it is generated, e.g., the `allow_slots` parameter to
// `RBACPolicy::arbitrary_for_hierarchy`. As of this writing, only the `rbac`
// fuzz target uses slots, so renaming `GeneratedPolicy` to something like
// `GeneratedTemplate` seems unduly disruptive.
pub struct GeneratedPolicy {
    pub id: PolicyID,
    // use String for the impl of Arbitrary
    annotations: HashMap<Id, String>,
    pub effect: Effect,
    principal_constraint: PrincipalOrResourceConstraint,
    action_constraint: ActionConstraint,
    resource_constraint: PrincipalOrResourceConstraint,
    abac_constraints: Expr,
}

impl GeneratedPolicy {
    fn convert_annotations(
        annotations: HashMap<Id, String>,
    ) -> std::collections::BTreeMap<Id, SmolStr> {
        annotations
            .into_iter()
            .map(|(k, v)| (k, v.into()))
            .collect()
    }
}

impl From<GeneratedPolicy> for StaticPolicy {
    fn from(gen: GeneratedPolicy) -> StaticPolicy {
        StaticPolicy::new(
            gen.id,
            GeneratedPolicy::convert_annotations(gen.annotations),
            gen.effect,
            gen.principal_constraint.into(),
            gen.action_constraint.into(),
            gen.resource_constraint.into(),
            gen.abac_constraints,
        )
        .unwrap() // Will panic if the GeneratedPolicy contains a slot.
    }
}

impl From<GeneratedPolicy> for Template {
    fn from(gen: GeneratedPolicy) -> Template {
        Template::new(
            gen.id,
            GeneratedPolicy::convert_annotations(gen.annotations),
            gen.effect,
            gen.principal_constraint.into(),
            gen.action_constraint.into(),
            gen.resource_constraint.into(),
            gen.abac_constraints,
        )
    }
}

impl GeneratedPolicy {
    pub fn has_slots(&self) -> bool {
        self.principal_constraint.has_slot() || self.resource_constraint.has_slot()
    }
    pub fn add_to_policyset(self, policyset: &mut PolicySet) {
        if self.has_slots() {
            policyset.add_template(self.into()).unwrap();
        } else {
            policyset.add_static(self.into()).unwrap();
        }
    }
}

impl Display for GeneratedPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let t: Template = self.clone().into();
        write!(f, "{t}")
    }
}

#[derive(Debug, Clone)]
enum PrincipalOrResourceConstraint {
    NoConstraint,
    Eq(EntityUID),
    EqSlot,
    In(EntityUID),
    InSlot,
}

impl PrincipalOrResourceConstraint {
    fn has_slot(&self) -> bool {
        match self {
            PrincipalOrResourceConstraint::NoConstraint => false,
            PrincipalOrResourceConstraint::Eq(_) => false,
            PrincipalOrResourceConstraint::EqSlot => true,
            PrincipalOrResourceConstraint::In(_) => false,
            PrincipalOrResourceConstraint::InSlot => true,
        }
    }
}

impl From<PrincipalOrResourceConstraint> for PrincipalConstraint {
    fn from(val: PrincipalOrResourceConstraint) -> Self {
        match val {
            PrincipalOrResourceConstraint::NoConstraint => PrincipalConstraint::any(),
            PrincipalOrResourceConstraint::Eq(euid) => PrincipalConstraint::is_eq(euid),
            PrincipalOrResourceConstraint::EqSlot => PrincipalConstraint::is_eq_slot(),
            PrincipalOrResourceConstraint::In(euid) => PrincipalConstraint::is_in(euid),
            PrincipalOrResourceConstraint::InSlot => PrincipalConstraint::is_in_slot(),
        }
    }
}

impl From<PrincipalOrResourceConstraint> for ResourceConstraint {
    fn from(val: PrincipalOrResourceConstraint) -> Self {
        match val {
            PrincipalOrResourceConstraint::NoConstraint => ResourceConstraint::any(),
            PrincipalOrResourceConstraint::Eq(euid) => ResourceConstraint::is_eq(euid),
            PrincipalOrResourceConstraint::EqSlot => ResourceConstraint::is_eq_slot(),
            PrincipalOrResourceConstraint::In(euid) => ResourceConstraint::is_in(euid),
            PrincipalOrResourceConstraint::InSlot => ResourceConstraint::is_in_slot(),
        }
    }
}

impl std::fmt::Display for PrincipalOrResourceConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoConstraint => Ok(()),
            Self::Eq(uid) => write!(f, " == {uid}"),
            // Note: This is not valid Cedar syntax without the slot name, but
            // there's nothing we can do about it since we don't know the slot
            // name here.
            Self::EqSlot => write!(f, " == ?"),
            Self::In(uid) => write!(f, " in {uid}"),
            Self::InSlot => write!(f, " in ?"),
        }
    }
}

impl PrincipalOrResourceConstraint {
    fn arbitrary_for_hierarchy(
        hierarchy: &Hierarchy,
        allow_slots: bool,
        u: &mut Unstructured<'_>,
    ) -> Result<Self> {
        // 20% of the time, NoConstraint; 40%, Eq; 40%, In
        if u.ratio(1, 5)? {
            Ok(Self::NoConstraint)
        } else {
            // choose Eq or In
            let use_eq = u.ratio(1, 2)?;
            // If slots are allowed, then generate a slot 50% of the time.
            if allow_slots && u.ratio(1, 2)? {
                if use_eq {
                    Ok(Self::EqSlot)
                } else {
                    Ok(Self::InSlot)
                }
            } else {
                let uid = hierarchy.arbitrary_uid(u)?;
                if use_eq {
                    Ok(Self::Eq(uid))
                } else {
                    Ok(Self::In(uid))
                }
            }
        }
    }

    /// size hint for arbitrary_for_hierarchy()
    fn arbitrary_size_hint(allow_slots: bool, depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(1, 5),
            arbitrary::size_hint::or(
                // NoConstraint case
                (0, Some(0)),
                // Eq or In case
                arbitrary::size_hint::and(
                    size_hint_for_ratio(1, 2), // choose Eq or In
                    if allow_slots {
                        arbitrary::size_hint::and(
                            // Decide whether to generate a slot.
                            size_hint_for_ratio(1, 2),
                            arbitrary::size_hint::or(
                                // Slot: don't need a UID.
                                (0, Some(0)),
                                // No slot: need a UID.
                                Hierarchy::arbitrary_uid_size_hint(depth),
                            ),
                        )
                    } else {
                        // Slot not allowed: need a UID.
                        Hierarchy::arbitrary_uid_size_hint(depth)
                    },
                ),
            ),
        )
    }
}

#[derive(Debug, Clone)]
enum ActionConstraint {
    NoConstraint,
    Eq(EntityUID),
    In(EntityUID),
    InList(Vec<EntityUID>),
}

impl std::fmt::Display for ActionConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoConstraint => Ok(()),
            Self::Eq(uid) => write!(f, " == {uid}"),
            Self::In(uid) => write!(f, " in {uid}"),
            Self::InList(vec) => {
                write!(f, " in [")?;
                for (i, uid) in vec.iter().enumerate() {
                    write!(f, "{uid}")?;
                    if i < vec.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, "]")?;
                Ok(())
            }
        }
    }
}

impl From<ActionConstraint> for ast::ActionConstraint {
    fn from(constraint: ActionConstraint) -> ast::ActionConstraint {
        match constraint {
            ActionConstraint::NoConstraint => ast::ActionConstraint::any(),
            ActionConstraint::Eq(euid) => ast::ActionConstraint::is_eq(euid),
            ActionConstraint::In(euid) => ast::ActionConstraint::is_in(vec![euid]),
            ActionConstraint::InList(euids) => ast::ActionConstraint::is_in(euids),
        }
    }
}

impl ActionConstraint {
    fn arbitrary_for_hierarchy(
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
        max_list_length: Option<u32>,
    ) -> Result<Self> {
        // 10% of the time, NoConstraint; 30%, Eq; 30%, In; 30%, InList
        if u.ratio(1, 10)? {
            Ok(Self::NoConstraint)
        } else if u.ratio(1, 3)? {
            Ok(Self::Eq(hierarchy.arbitrary_uid(u)?))
        } else if u.ratio(1, 2)? {
            Ok(Self::In(hierarchy.arbitrary_uid(u)?))
        } else {
            let mut uids = vec![];
            u.arbitrary_loop(Some(0), max_list_length, |u| {
                uids.push(hierarchy.arbitrary_uid(u)?);
                Ok(std::ops::ControlFlow::Continue(()))
            })?;
            Ok(Self::InList(uids))
        }
    }

    /// size hint for arbitrary_for_hierarchy()
    fn arbitrary_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(1, 10),
            arbitrary::size_hint::or(
                // NoConstraint case
                (0, Some(0)),
                // other case
                arbitrary::size_hint::and(
                    size_hint_for_ratio(1, 3),
                    arbitrary::size_hint::or(
                        // Eq case
                        Hierarchy::arbitrary_uid_size_hint(depth),
                        // other case
                        arbitrary::size_hint::and(
                            size_hint_for_ratio(1, 2),
                            arbitrary::size_hint::or(
                                // In case
                                Hierarchy::arbitrary_uid_size_hint(depth),
                                // other case. not sure how to account for arbitrary_loop() and many arbitrary_uid() calls; this seems safe
                                (1, None),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }
}

#[derive(Debug, Clone)]
pub struct GeneratedLinkedPolicy {
    pub id: PolicyID,
    template_id: PolicyID,
    principal: Option<EntityUID>,
    resource: Option<EntityUID>,
}

impl GeneratedLinkedPolicy {
    fn arbitrary_slot_value<'a>(
        prc: &PrincipalOrResourceConstraint,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'a>,
    ) -> Result<Option<EntityUID>> {
        if prc.has_slot() {
            Ok(Some(hierarchy.arbitrary_uid(u)?))
        } else {
            Ok(None)
        }
    }
    pub fn arbitrary<'a>(
        id: PolicyID,
        template: &GeneratedPolicy,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'a>,
    ) -> Result<Self> {
        Ok(Self {
            id,
            template_id: template.id.clone(),
            principal: Self::arbitrary_slot_value(&template.principal_constraint, hierarchy, u)?,
            resource: Self::arbitrary_slot_value(&template.resource_constraint, hierarchy, u)?,
        })
    }
    pub fn add_to_policyset(self, policyset: &mut PolicySet) {
        let mut vals = HashMap::new();
        if let Some(principal_uid) = self.principal {
            vals.insert(ast::SlotId::principal(), principal_uid);
        }
        if let Some(resource_uid) = self.resource {
            vals.insert(ast::SlotId::resource(), resource_uid);
        }
        policyset
            .link(self.template_id, self.id, vals.into())
            .unwrap();
    }
}

#[derive(Debug, Clone)]
pub struct Request {
    principal: EntityUID,
    action: EntityUID,
    resource: EntityUID,
    context: HashMap<SmolStr, RestrictedExpr>,
}

impl std::fmt::Display for Request {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(
            f,
            "(principal : {}, action: {}, resource: {})",
            self.principal, self.action, self.resource
        )?;
        writeln!(f, "With context: {{")?;
        for (attr, val) in self.context.iter() {
            writeln!(f, "{attr} : {val},")?;
        }
        write!(f, "}}")
    }
}

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
    use cedar_policy_core::ast::Entity;
    use cedar_policy_core::entities::TCComputation;

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
