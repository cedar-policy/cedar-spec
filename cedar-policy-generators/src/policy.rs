use crate::collections::HashMap;
use crate::err::Result;
use crate::hierarchy::Hierarchy;
use crate::size_hint_utils::size_hint_for_ratio;
use arbitrary::{Arbitrary, Unstructured};
use cedar_policy_core::ast::{
    Annotation, Annotations, AnyId, Effect, EntityUID, Expr, Name, Policy, PolicyID, PolicySet,
    StaticPolicy, Template,
};
use cedar_policy_core::{ast, est};
use serde::Serialize;
use smol_str::SmolStr;
use std::fmt::Display;

/// Data structure representing a generated policy (or template)
#[derive(Debug, Clone, Serialize)]
// `GeneratedPolicy` is now a bit of a misnomer: it may have slots depending on
// how it is generated, e.g., the `allow_slots` parameter to
// `arbitrary_for_hierarchy()`. But as of this writing, it feels like renaming
// `GeneratedPolicy` to something like `GeneratedTemplate` seems unduly
// disruptive.
#[serde(into = "est::Policy")]
pub struct GeneratedPolicy {
    id: PolicyID,
    annotations: HashMap<AnyId, SmolStr>,
    effect: Effect,
    principal_constraint: PrincipalOrResourceConstraint,
    action_constraint: ActionConstraint,
    resource_constraint: PrincipalOrResourceConstraint,
    abac_constraints: Expr,
}

impl From<GeneratedPolicy> for est::Policy {
    fn from(gp: GeneratedPolicy) -> est::Policy {
        let sp: StaticPolicy = gp.into();
        let p: Policy = sp.into();
        p.into()
    }
}

impl GeneratedPolicy {
    /// Create a new `GeneratedPolicy` with these fields
    pub fn new(
        id: PolicyID,
        annotations: impl IntoIterator<Item = (AnyId, SmolStr)>,
        effect: Effect,
        principal_constraint: PrincipalOrResourceConstraint,
        action_constraint: ActionConstraint,
        resource_constraint: PrincipalOrResourceConstraint,
        abac_constraints: Expr,
    ) -> Self {
        Self {
            id,
            annotations: annotations.into_iter().collect(),
            effect,
            principal_constraint,
            action_constraint,
            resource_constraint,
            abac_constraints,
        }
    }

    /// Generate an arbitrary `GeneratedPolicy`
    pub fn arbitrary_for_hierarchy(
        fixed_id_opt: Option<PolicyID>,
        hierarchy: &Hierarchy,
        allow_slots: bool,
        abac_constraints: Expr,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        let id = if let Some(fixed_id) = fixed_id_opt {
            fixed_id
        } else {
            u.arbitrary()?
        };
        let annotations = u.arbitrary()?;
        let effect = u.arbitrary()?;
        let principal_constraint =
            PrincipalOrResourceConstraint::arbitrary_for_hierarchy(hierarchy, allow_slots, u)?;
        let action_constraint = ActionConstraint::arbitrary_for_hierarchy(hierarchy, u, Some(3))?;
        let resource_constraint =
            PrincipalOrResourceConstraint::arbitrary_for_hierarchy(hierarchy, allow_slots, u)?;
        Ok(Self {
            id,
            annotations,
            effect,
            principal_constraint,
            action_constraint,
            resource_constraint,
            abac_constraints,
        })
    }

    /// size_hint for `arbitrary_for_hierarchy()`
    pub fn arbitrary_for_hierarchy_size_hint(
        have_fixed_id: bool,
        allow_slots: bool,
        depth: usize,
    ) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            if have_fixed_id {
                (0, Some(0))
            } else {
                <PolicyID as Arbitrary>::size_hint(depth)
            },
            <Effect as Arbitrary>::size_hint(depth),
            PrincipalOrResourceConstraint::arbitrary_size_hint(allow_slots, depth),
            ActionConstraint::arbitrary_size_hint(depth),
            PrincipalOrResourceConstraint::arbitrary_size_hint(allow_slots, depth),
        ])
    }
    /// Does the policy have (a nonzero number of) slots
    pub fn has_slots(&self) -> bool {
        self.principal_constraint.has_slot() || self.resource_constraint.has_slot()
    }

    /// Add the policy to the given `PolicySet`
    pub fn add_to_policyset(self, policyset: &mut PolicySet) {
        if self.has_slots() {
            policyset.add_template(self.into()).unwrap();
        } else {
            policyset.add_static(self.into()).unwrap();
        }
    }
}

fn convert_annotations(annotations: HashMap<AnyId, SmolStr>) -> Annotations {
    annotations
        .into_iter()
        .map(|(k, v)| (k, Annotation { val: v, loc: None }))
        .collect()
}

impl From<GeneratedPolicy> for StaticPolicy {
    fn from(gen: GeneratedPolicy) -> StaticPolicy {
        StaticPolicy::new(
            gen.id,
            None,
            convert_annotations(gen.annotations),
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
            None,
            convert_annotations(gen.annotations),
            gen.effect,
            gen.principal_constraint.into(),
            gen.action_constraint.into(),
            gen.resource_constraint.into(),
            gen.abac_constraints,
        )
    }
}

impl From<GeneratedPolicy> for String {
    fn from(g: GeneratedPolicy) -> String {
        let t = Template::from(g);
        t.to_string()
    }
}

impl Display for GeneratedPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let t: Template = self.clone().into();
        write!(f, "{t}")
    }
}

/// Represents the principal or resource constraint of the policy scope
#[derive(Debug, Clone)]
pub enum PrincipalOrResourceConstraint {
    /// No constraint, eg, `principal,` or `resource,`
    NoConstraint,
    /// Eg `principal == User::"123"`
    Eq(EntityUID),
    /// Eg `principal == ?principal`
    EqSlot,
    /// Eg `principal in Group::"123"`
    In(EntityUID),
    /// Eg `principal in ?principal`
    InSlot,
    /// Eg `principal is User`
    IsType(Name),
    /// Eg `principal is User in Group::"123"`
    IsTypeIn(Name, EntityUID),
    /// Eg `principal is User in ?principal`
    IsTypeInSlot(Name),
}

impl PrincipalOrResourceConstraint {
    fn has_slot(&self) -> bool {
        match self {
            PrincipalOrResourceConstraint::NoConstraint => false,
            PrincipalOrResourceConstraint::Eq(_) => false,
            PrincipalOrResourceConstraint::EqSlot => true,
            PrincipalOrResourceConstraint::In(_) => false,
            PrincipalOrResourceConstraint::InSlot => true,
            PrincipalOrResourceConstraint::IsType(_) => false,
            PrincipalOrResourceConstraint::IsTypeIn(_, _) => false,
            PrincipalOrResourceConstraint::IsTypeInSlot(_) => true,
        }
    }
}

impl From<PrincipalOrResourceConstraint> for ast::PrincipalConstraint {
    fn from(val: PrincipalOrResourceConstraint) -> Self {
        match val {
            PrincipalOrResourceConstraint::NoConstraint => ast::PrincipalConstraint::any(),
            PrincipalOrResourceConstraint::Eq(euid) => ast::PrincipalConstraint::is_eq(euid),
            PrincipalOrResourceConstraint::EqSlot => ast::PrincipalConstraint::is_eq_slot(),
            PrincipalOrResourceConstraint::In(euid) => ast::PrincipalConstraint::is_in(euid),
            PrincipalOrResourceConstraint::InSlot => ast::PrincipalConstraint::is_in_slot(),
            PrincipalOrResourceConstraint::IsType(ty) => {
                ast::PrincipalConstraint::is_entity_type(ty)
            }
            PrincipalOrResourceConstraint::IsTypeIn(ty, euid) => {
                ast::PrincipalConstraint::is_entity_type_in(ty, euid)
            }
            PrincipalOrResourceConstraint::IsTypeInSlot(ty) => {
                ast::PrincipalConstraint::is_entity_type_in_slot(ty)
            }
        }
    }
}

impl From<PrincipalOrResourceConstraint> for ast::ResourceConstraint {
    fn from(val: PrincipalOrResourceConstraint) -> Self {
        match val {
            PrincipalOrResourceConstraint::NoConstraint => ast::ResourceConstraint::any(),
            PrincipalOrResourceConstraint::Eq(euid) => ast::ResourceConstraint::is_eq(euid),
            PrincipalOrResourceConstraint::EqSlot => ast::ResourceConstraint::is_eq_slot(),
            PrincipalOrResourceConstraint::In(euid) => ast::ResourceConstraint::is_in(euid),
            PrincipalOrResourceConstraint::InSlot => ast::ResourceConstraint::is_in_slot(),
            PrincipalOrResourceConstraint::IsType(ty) => {
                ast::ResourceConstraint::is_entity_type(ty)
            }
            PrincipalOrResourceConstraint::IsTypeIn(ty, euid) => {
                ast::ResourceConstraint::is_entity_type_in(ty, euid)
            }
            PrincipalOrResourceConstraint::IsTypeInSlot(ty) => {
                ast::ResourceConstraint::is_entity_type_in_slot(ty)
            }
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
            Self::IsType(ty) => write!(f, " is {ty}"),
            Self::IsTypeIn(ty, euid) => write!(f, " is {ty} in {euid}"),
            Self::IsTypeInSlot(ty) => write!(f, "is {ty} in ?"),
        }
    }
}

impl PrincipalOrResourceConstraint {
    fn arbitrary_for_hierarchy(
        hierarchy: &Hierarchy,
        allow_slots: bool,
        u: &mut Unstructured<'_>,
    ) -> Result<Self> {
        // 20% of the time, NoConstraint
        if u.ratio(1, 5)? {
            Ok(Self::NoConstraint)
        } else {
            // If slots are allowed, then generate a slot 50% of the time.
            if allow_slots && u.ratio(1, 2)? {
                // 40% Eq, 40% In or IsIn.
                // Don't generate `Is` on its own because it can't have a slot.
                gen!(u,
                    2 => Ok(Self::EqSlot),
                    1 => Ok(Self::InSlot),
                    1 => Ok(Self::IsTypeInSlot(hierarchy.arbitrary_entity_type(u)?))
                )
            } else {
                // 32% Eq, 16% In, 16% Is, 16% IsIn
                let uid = hierarchy.arbitrary_uid(u, None)?;
                gen!(u,
                    2 => Ok(Self::Eq(uid)),
                    1 => Ok(Self::In(uid)),
                    1 => Ok(Self::IsType(hierarchy.arbitrary_entity_type(u)?)),
                    1 => Ok(Self::IsTypeIn(hierarchy.arbitrary_entity_type(u)?, uid))
                )
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

/// Represents the action constraint of the policy scope
#[derive(Debug, Clone)]
pub enum ActionConstraint {
    /// No constraint, eg, `action,`
    NoConstraint,
    /// Eg `action == Action::"view"`
    Eq(EntityUID),
    /// Eg `action in Action::"ReadOnly"`
    In(EntityUID),
    /// Eg `action in [Action::"view", Action::"edit"]`
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
            Ok(Self::Eq(hierarchy.arbitrary_uid(u, None)?))
        } else if u.ratio(1, 2)? {
            Ok(Self::In(hierarchy.arbitrary_uid(u, None)?))
        } else {
            let mut uids = vec![];
            u.arbitrary_loop(Some(0), max_list_length, |u| {
                uids.push(hierarchy.arbitrary_uid(u, None)?);
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

/// Data structure representing a generated linked policy
#[derive(Debug, Clone, Serialize)]
pub struct GeneratedLinkedPolicy {
    /// ID of the linked policy
    pub id: PolicyID,
    /// ID of the template it's linked to
    template_id: PolicyID,
    principal: Option<EntityUID>,
    resource: Option<EntityUID>,
}

impl GeneratedLinkedPolicy {
    fn arbitrary_slot_value(
        prc: &PrincipalOrResourceConstraint,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<Option<EntityUID>> {
        if prc.has_slot() {
            Ok(Some(hierarchy.arbitrary_uid(u, None)?))
        } else {
            Ok(None)
        }
    }

    /// Generate an arbitrary `GeneratedLinkedPolicy` from the given template
    pub fn arbitrary(
        id: PolicyID,
        template: &GeneratedPolicy,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<Self> {
        Ok(Self {
            id,
            template_id: template.id.clone(),
            principal: Self::arbitrary_slot_value(&template.principal_constraint, hierarchy, u)?,
            resource: Self::arbitrary_slot_value(&template.resource_constraint, hierarchy, u)?,
        })
    }

    /// Add this `GeneratedLinkedPolicy` to the given `PolicySet`
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
