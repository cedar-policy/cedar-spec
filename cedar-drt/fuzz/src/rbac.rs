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

use ast::{Effect, Entity, EntityUID, Expr, Name, PolicyID, Request, StaticPolicy};
use cedar_policy_core::ast;
use cedar_policy_core::entities::Entities;
use cedar_policy_generators::collections::{HashMap, HashSet};
use cedar_policy_generators::hierarchy::Hierarchy;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use std::ops::{Deref, DerefMut};

#[derive(Debug, Clone)]
pub struct RBACHierarchy(pub Hierarchy);

impl RBACHierarchy {
    pub fn into_json(self) -> String {
        let mut s = String::new();
        s.push('[');
        let num_entities = self.0.num_entities();
        for (i, entity) in self.0.into_entities().enumerate() {
            s.push_str(&RBACEntity(entity).into_json());
            if i < num_entities - 1 {
                s.push_str(", ");
            }
        }
        s.push(']');
        s
    }
}

impl Deref for RBACHierarchy {
    type Target = Hierarchy;
    fn deref(&self) -> &Hierarchy {
        &self.0
    }
}

impl DerefMut for RBACHierarchy {
    fn deref_mut(&mut self) -> &mut Hierarchy {
        &mut self.0
    }
}

impl std::fmt::Display for RBACHierarchy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        for (i, entity) in self.0.entities().enumerate() {
            write!(f, "{}", RBACEntity(entity.clone()))?;
            if i < self.0.num_entities() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, "]")?;
        Ok(())
    }
}

impl From<RBACHierarchy> for Hierarchy {
    fn from(rbac: RBACHierarchy) -> Hierarchy {
        rbac.0
    }
}

impl TryFrom<RBACHierarchy> for Entities {
    type Error = String;
    fn try_from(rbac: RBACHierarchy) -> Result<Entities, String> {
        rbac.0.try_into()
    }
}

impl<'a> Arbitrary<'a> for RBACHierarchy {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        // first generate the pool of names. we generate a set (so there are no
        // duplicates), but then convert it to a Vec (because we want them
        // ordered, even though we want the order to be arbitrary)
        let uids: HashSet<EntityUID> = u.arbitrary()?;
        let uids: Vec<EntityUID> = uids
            .into_iter()
            // drop generated Unspecified entities
            .filter(|uid| matches!((*uid).entity_type(), ast::EntityType::Concrete(_)))
            .collect();
        let mut uids_by_type: HashMap<Name, Vec<EntityUID>> = HashMap::new();
        for (uid, ty) in uids
            .into_iter()
            .map(|uid| (uid.clone(), uid.components().0))
        {
            // all entities in `uids` will be `Concrete`
            if let ast::EntityType::Concrete(name) = ty {
                uids_by_type.entry(name).or_default().push(uid)
            }
        }
        let hierarchy_no_attrs = Hierarchy::from_uids_by_type(uids_by_type);
        // now generate the RBACEntity objects, given these uids
        let entities = hierarchy_no_attrs
            .entities()
            .map(|e| e.uid())
            .map(|uid| RBACEntity::arbitrary_for_pool(uid, hierarchy_no_attrs.uids(), u))
            .collect::<arbitrary::Result<Vec<RBACEntity>>>()?
            .into_iter()
            .map(|entity| (entity.uid(), entity.into()))
            .collect();
        Ok(Self(hierarchy_no_attrs.replace_entities(entities)))
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            <HashSet<EntityUID> as Arbitrary>::size_hint(depth),
            // actually we make many calls to RBACEntity::arbitrary_for_pool(), but not sure how to say that
            RBACEntity::arbitrary_size_hint(depth),
        )
    }
}

#[derive(Debug, Clone)]
pub struct RBACEntity(pub Entity);

impl Deref for RBACEntity {
    type Target = Entity;
    fn deref(&self) -> &Entity {
        &self.0
    }
}

impl DerefMut for RBACEntity {
    fn deref_mut(&mut self) -> &mut Entity {
        &mut self.0
    }
}

impl RBACEntity {
    fn into_json(self) -> String {
        let escaped_name = format!("{}", self.uid()).escape_debug().to_string();
        let mut parents_json = String::new();
        parents_json.push('[');
        let num_parents = self.ancestors().count();
        for (i, parent) in self.ancestors().enumerate() {
            let escaped_parent = format!("{parent}").escape_debug().to_string();
            parents_json.push_str(&format!(r#""{escaped_parent}""#));
            if i < num_parents - 1 {
                parents_json.push_str(", ");
            }
        }
        parents_json.push(']');
        format!(
            r#"{{
            "uid": "{}",
            "attrs": {{}},
            "parents": {}
        }}"#,
            escaped_name, parents_json
        )
    }
}

impl std::fmt::Display for RBACEntity {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.clone().into_json())
    }
}

impl From<RBACEntity> for Entity {
    fn from(rbac: RBACEntity) -> Entity {
        rbac.0
    }
}

impl RBACEntity {
    /// Generate an arbitrary RBACEntity with the name `uid` and parents taken
    /// from the `pool` (which should contain `uid` somewhere)
    fn arbitrary_for_pool(
        uid: EntityUID,
        pool: &[EntityUID],
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        let mut parents = HashSet::new();
        // for each uid in the pool, flip a weighted coin to decide whether
        // to add it as a parent. We only consider uids appearing after the
        // given one in the pool; this ensures we get a DAG (no cycles)
        // without loss of generality
        let this_idx = pool
            .iter()
            .position(|x| x == &uid)
            .expect("uid should be in the pool");
        for pool_uid in &pool[(this_idx + 1)..] {
            if u.ratio(1, 3)? {
                parents.insert(pool_uid.clone());
            }
        }
        // assert there is no self-edge
        assert!(!parents.contains(&uid));
        Ok(Self(Entity::new(
            uid,
            HashMap::new().into(),
            parents.into(),
        )))
    }

    /// size hint for arbitrary_for_pool()
    fn arbitrary_size_hint(_depth: usize) -> (usize, Option<usize>) {
        // there's 0 or more of these calls, but we'll hint it as minimum one
        // with no maximum
        let (min, _max) = super::size_hint_for_ratio(1, 3);
        (min, None)
    }
}

#[derive(Debug, Clone)]
pub struct RBACPolicy(pub super::GeneratedPolicy);

impl Deref for RBACPolicy {
    type Target = super::GeneratedPolicy;
    fn deref(&self) -> &super::GeneratedPolicy {
        &self.0
    }
}

impl DerefMut for RBACPolicy {
    fn deref_mut(&mut self) -> &mut super::GeneratedPolicy {
        &mut self.0
    }
}

impl From<RBACPolicy> for StaticPolicy {
    fn from(rbac: RBACPolicy) -> StaticPolicy {
        rbac.0.into()
    }
}

impl RBACPolicy {
    pub fn arbitrary_for_hierarchy(
        fixed_id_opt: Option<PolicyID>,
        hierarchy: &Hierarchy,
        allow_slots: bool,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        let id = if let Some(fixed_id) = fixed_id_opt {
            fixed_id
        } else {
            u.arbitrary()?
        };
        let annotations = u.arbitrary()?;
        let effect = u.arbitrary()?;
        let principal_constraint = super::PrincipalOrResourceConstraint::arbitrary_for_hierarchy(
            hierarchy,
            allow_slots,
            u,
        )?;
        let action_constraint =
            super::ActionConstraint::arbitrary_for_hierarchy(hierarchy, u, Some(3))?;
        let resource_constraint = super::PrincipalOrResourceConstraint::arbitrary_for_hierarchy(
            hierarchy,
            allow_slots,
            u,
        )?;
        Ok(Self(super::GeneratedPolicy {
            id,
            annotations,
            effect,
            principal_constraint,
            action_constraint,
            resource_constraint,
            abac_constraints: Expr::val(true),
        }))
    }

    /// size hint for arbitrary_for_hierarchy()
    pub fn arbitrary_size_hint(
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
            super::PrincipalOrResourceConstraint::arbitrary_size_hint(allow_slots, depth),
            super::ActionConstraint::arbitrary_size_hint(depth),
            super::PrincipalOrResourceConstraint::arbitrary_size_hint(allow_slots, depth),
        ])
    }
}

impl std::fmt::Display for RBACPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            r#"
        {}(
            principal{},
            action{},
            resource{}
        );
        "#,
            self.0.effect,
            self.0.principal_constraint,
            self.0.action_constraint,
            self.0.resource_constraint
        )
    }
}

#[derive(Debug, Clone)]
pub struct RBACRequest(pub super::Request);

impl Deref for RBACRequest {
    type Target = super::Request;
    fn deref(&self) -> &super::Request {
        &self.0
    }
}

impl DerefMut for RBACRequest {
    fn deref_mut(&mut self) -> &mut super::Request {
        &mut self.0
    }
}

impl From<RBACRequest> for Request {
    fn from(rbac: RBACRequest) -> Request {
        Request::new(
            rbac.0.principal,
            rbac.0.action,
            rbac.0.resource,
            ast::Context::empty(),
        )
    }
}

impl std::fmt::Display for RBACRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "principal: {}, action: {}, resource: {}",
            self.0.principal, self.0.action, self.0.resource
        )
    }
}

impl RBACRequest {
    pub fn arbitrary_for_hierarchy(
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        Ok(Self(super::Request {
            principal: hierarchy.arbitrary_uid(u)?,
            action: hierarchy.arbitrary_uid(u)?,
            resource: hierarchy.arbitrary_uid(u)?,
            context: HashMap::new(),
        }))
    }

    /// size hint for arbitrary_for_hierarchy()
    pub fn arbitrary_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Hierarchy::arbitrary_uid_size_hint(depth),
            Hierarchy::arbitrary_uid_size_hint(depth),
            Hierarchy::arbitrary_uid_size_hint(depth),
        ])
    }
}
