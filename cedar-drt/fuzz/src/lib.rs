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
use ast::{
    Effect, Entity, EntityUID, Expr, Id, Name, PolicyID, PolicySet, RestrictedExpr, StaticPolicy,
};
use cedar_drt::{
    time_function, DefinitionalEngine, DefinitionalValidator, RUST_AUTH_MSG, RUST_VALIDATION_MSG,
};
use cedar_policy_core::ast;
use cedar_policy_core::ast::{PrincipalConstraint, ResourceConstraint, Template};
use cedar_policy_core::authorizer::{Authorizer, Diagnostics, Response};
use cedar_policy_core::entities::{Entities, TCComputation};
pub use cedar_policy_validator::{ValidationErrorKind, ValidationMode, Validator, ValidatorSchema};
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

        // TODO: remove this
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
    }
}
