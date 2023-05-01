mod abac;
pub use abac::*;
mod rbac;
pub use rbac::*;
mod schema;
pub use schema::*;

mod dump;
pub use dump::*;
mod err;
pub use err::*;

mod collections;
mod prt;
pub use collections::*;

pub use prt::*;

use std::fmt::Display;

use crate::collections::HashMap;
pub use cedar_policy_validator::{ValidationErrorKind, ValidationMode, Validator, ValidatorSchema};
use ast::{
    Effect, Entity, EntityUID, Expr, Id, Name, PolicyID, PolicySet, RestrictedExpr, StaticPolicy,
};
use cedar_drt::{
    time_function, DefinitionalEngine, DefinitionalValidator, RUST_AUTH_MSG, RUST_VALIDATION_MSG,
};
use cedar_policy_core::ast;
use cedar_policy_core::ast::{PrincipalConstraint, ResourceConstraint};
use cedar_policy_core::authorizer::{Answer, Authorizer, Diagnostics};
use cedar_policy_core::entities::{Entities, TCComputation};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::info;
use smol_str::SmolStr;

#[derive(Debug, Clone)]
pub struct Hierarchy {
    /// maps EntityUID to the corresponding Entity
    entities: HashMap<EntityUID, Entity>,
    /// Vec of UIDs in the hierarchy, which we keep in sync with the `entities`
    /// HashMap.
    /// The reason we have this separately is that is allows us to do
    /// arbitrary_uid() fast.
    uids: Vec<EntityUID>,
    /// Map of entity typename to UID, for all UIDs in the hierarchy.
    /// We keep this in sync with the `entities` HashMap too.
    /// This is to make arbitrary_uid_with_type() fast.
    uids_by_type: HashMap<Name, Vec<EntityUID>>,
}

impl Hierarchy {
    /// generate an arbitrary uid based on the hierarchy
    pub fn arbitrary_uid(&self, u: &mut Unstructured<'_>) -> Result<EntityUID> {
        // UID that exists or doesn't. 90% of the time pick one that exists
        if u.ratio::<u8>(9, 10)? {
            let uid = u
                .choose(&self.uids)
                .map_err(|e| while_doing("getting an arbitrary uid", e))?;
            Ok(uid.clone())
        } else {
            // Note: may generate an unspecified entity
            u.arbitrary().map_err(Into::into)
        }
    }
    /// size hint for arbitrary_uid()
    pub fn arbitrary_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(9, 10),
            arbitrary::size_hint::or(
                // exists case
                size_hint_for_choose(None),
                // not-exists case
                <EntityUID as Arbitrary>::size_hint(depth),
            ),
        )
    }

    /// generate an arbitrary uid based on the hierarchy, with the given typename
    pub fn arbitrary_uid_with_type(
        &self,
        typename: &Name,
        u: &mut Unstructured<'_>,
    ) -> Result<EntityUID> {
        // UID that exists or doesn't. 90% of the time pick one that exists
        if u.ratio::<u8>(9, 10)? {
            let uid = u.choose(self.uids_by_type.get(typename).ok_or(Error::EmptyChoose {
                doing_what: "getting an existing uid with given type",
            })?)?;
            Ok(uid.clone())
        } else {
            Ok(EntityUID::from_components(typename.clone(), u.arbitrary()?))
        }
    }
    pub fn arbitrary_uid_with_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(9, 10),
            arbitrary::size_hint::or(
                size_hint_for_choose(None),
                <ast::Eid as Arbitrary>::size_hint(depth),
            ),
        )
    }

    /// Get an Entity object by UID
    pub fn entity(&self, uid: &EntityUID) -> Option<&Entity> {
        self.entities.get(uid)
    }

    /// Get an Entity object by UID, mutable
    pub fn entity_mut(&mut self, uid: &EntityUID) -> Option<&mut Entity> {
        self.entities.get_mut(uid)
    }

    /// How many entities (UIDs) are in the hierarchy
    pub fn num_uids(&self) -> usize {
        self.uids.len()
    }

    /// Consume the Hierarchy and create an iterator over its Entity objects
    fn into_entities(self) -> impl Iterator<Item = Entity> {
        self.entities.into_values()
    }
}

impl TryFrom<Hierarchy> for Entities {
    type Error = String;
    fn try_from(h: Hierarchy) -> std::result::Result<Entities, String> {
        Entities::from_entities(h.into_entities().map(Into::into), TCComputation::ComputeNow)
            .map_err(|e| e.to_string())
    }
}

#[derive(Debug, Clone)]
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

impl From<GeneratedPolicy> for StaticPolicy {
    fn from(gen: GeneratedPolicy) -> StaticPolicy {
        StaticPolicy::new(
            gen.id,
            gen.annotations
                .into_iter()
                .map(|(k, v)| (k, v.into()))
                .collect(),
            gen.effect,
            gen.principal_constraint.into(),
            gen.action_constraint.into(),
            gen.resource_constraint.into(),
            gen.abac_constraints,
        )
        .unwrap()
    }
}

impl Display for GeneratedPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let i: StaticPolicy = self.clone().into();
        write!(f, "{i}")
    }
}

#[derive(Debug, Clone)]
enum PrincipalOrResourceConstraint {
    NoConstraint,
    Eq(EntityUID),
    In(EntityUID),
}

impl From<PrincipalOrResourceConstraint> for PrincipalConstraint {
    fn from(val: PrincipalOrResourceConstraint) -> Self {
        match val {
            PrincipalOrResourceConstraint::NoConstraint => PrincipalConstraint::any(),
            PrincipalOrResourceConstraint::Eq(euid) => PrincipalConstraint::is_eq(euid),
            PrincipalOrResourceConstraint::In(euid) => PrincipalConstraint::is_in(euid),
        }
    }
}

impl From<PrincipalOrResourceConstraint> for ResourceConstraint {
    fn from(val: PrincipalOrResourceConstraint) -> Self {
        match val {
            PrincipalOrResourceConstraint::NoConstraint => ResourceConstraint::any(),
            PrincipalOrResourceConstraint::Eq(euid) => ResourceConstraint::is_eq(euid),
            PrincipalOrResourceConstraint::In(euid) => ResourceConstraint::is_in(euid),
        }
    }
}

impl std::fmt::Display for PrincipalOrResourceConstraint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoConstraint => Ok(()),
            Self::Eq(uid) => write!(f, " == {uid}"),
            Self::In(uid) => write!(f, " in {uid}"),
        }
    }
}

impl PrincipalOrResourceConstraint {
    fn arbitrary_for_hierarchy(hierarchy: &Hierarchy, u: &mut Unstructured<'_>) -> Result<Self> {
        // 20% of the time, NoConstraint; 40%, Eq; 40%, In
        if u.ratio(1, 5)? {
            Ok(Self::NoConstraint)
        } else {
            let uid = hierarchy.arbitrary_uid(u)?;
            // choose Eq or In
            if u.ratio(1, 2)? {
                Ok(Self::Eq(uid))
            } else {
                Ok(Self::In(uid))
            }
        }
    }

    /// size hint for arbitrary_for_hierarchy()
    fn arbitrary_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_ratio(1, 5),
            arbitrary::size_hint::or(
                // NoConstraint case
                (0, Some(0)),
                // Eq or In case
                arbitrary::size_hint::and(
                    Hierarchy::arbitrary_uid_size_hint(depth),
                    size_hint_for_ratio(1, 2),
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

/// get a size hint for a call to ratio::<T>() with these parameters
fn size_hint_for_ratio<T: arbitrary::unstructured::Int>(_a: T, _b: T) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for ratio()
    size_hint_for_nonzero_range::<T>()
}

/// get a size hint for a call to int_in_range::<T>() with the parameter a..=b
fn size_hint_for_range<T: arbitrary::unstructured::Int>(a: T, b: T) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for int_in_range()
    if a >= b {
        (0, Some(0))
    } else {
        size_hint_for_nonzero_range::<T>()
    }
}

/// get a size hint for a call to int_in_range::<T>(a..=b) where we assume a < b
/// given this assumption, a and b don't matter for the calculation
fn size_hint_for_nonzero_range<T: arbitrary::unstructured::Int>() -> (usize, Option<usize>) {
    (1, Some(std::mem::size_of::<T>()))
}

/// get a size hint for a call to choose(). More precise estimate available if
/// you have an upper bound on how many things you're choosing from
fn size_hint_for_choose(max_num_choices: Option<usize>) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for choose()
    match max_num_choices {
        Some(max_num_choices) => size_hint_for_range::<usize>(0, max_num_choices - 1),
        None => (1, None), // hard to know upper bound here
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
    /// Returns the answer which the engines agree on.
    pub fn run_single_test(
        &self,
        q: &ast::Request,
        policies: &PolicySet,
        entities: &Entities,
    ) -> Answer {
        let (rust_ans, rust_auth_dur) =
            time_function(|| self.authorizer.is_authorized(q, policies, entities));
        info!("{}{}", RUST_AUTH_MSG, rust_auth_dur.as_nanos());

        // TODO: remove this
        // For now, we ignore all tests where the Rust side returns an integer
        // overflow error, as the behavior between Rust and Dafny is
        // intentionally different
        if rust_ans
            .diagnostics
            .errors
            .iter()
            .any(|e| e.contains("integer overflow"))
        {
            return rust_ans;
        }

        // very important that we return the Rust answer, with its rich errors,
        // in case the caller wants to expect those. (and not the definitional
        // answer, which as of this writing contains less-rich errors)
        let ret = rust_ans.clone();

        let definitional_ans = self.def_engine.is_authorized(q, policies, entities);
        // for now, we expect never to receive errors from the definitional engine,
        // and we otherwise ignore errors in the comparison
        assert_eq!(definitional_ans.diagnostics.errors, Vec::<String>::new());
        let rust_ans_for_comparison = Answer {
            diagnostics: Diagnostics {
                errors: Vec::new(),
                ..rust_ans.diagnostics
            },
            ..rust_ans
        };
        assert_eq!(
            rust_ans_for_comparison, definitional_ans,
            "Mismatch for {q}\nPolicies:\n{}\nEntities:\n{}",
            &policies, &entities
        );
        ret
    }

    /// Differentially test validation on the given policy and schema.
    /// Panics if the two engines do not agree.
    pub fn run_validation(&self, schema: ValidatorSchema, policies: &PolicySet) {
        let validator = Validator::new(schema.clone());
        let (rust_ans, rust_validation_dur) =
            time_function(|| validator.validate(policies, ValidationMode::Permissive));
        info!("{}{}", RUST_VALIDATION_MSG, rust_validation_dur.as_nanos());

        let definitional_ans = self.def_validator.validate(schema.clone(), policies);

        assert!(
            definitional_ans.parsing_succeeded(),
            "Dafny json parsing failed for:\nPolicies:\n{}\nSchema:\n{:?}",
            &policies,
            schema
        );

        // Temporary hack to avoid a known mismatch between the Dafny and Rust.
        // The issue is that the Rust code will always return an error for an
        // unrecognized entity or action, even if that part of the expression
        // should be excluded from typechecking (e.g., `true || Undefined::"foo"`
        // should be well typed due to short-circuiting).
        if rust_ans.validation_errors().any(|e| {
            matches!(
                e.error_kind(),
                ValidationErrorKind::UnrecognizedEntityType(_)
                    | ValidationErrorKind::UnrecognizedActionId(_)
            )
        }) {
            return;
        }

        assert_eq!(
            rust_ans.validation_passed(),
            definitional_ans.validation_passed(),
            "Mismatch for Policies:\n{}\nSchema:\n{:?}\nRust response: {:?}\nDafny response: {:?}\n",
            &policies,
            schema,
            rust_ans,
            definitional_ans,
        );

        // TODO: check for a relationship between validation errors.
        // E.g., the error reported by the definitional validator should be in
        // the list of errors reported by the production validator.
    }
}
