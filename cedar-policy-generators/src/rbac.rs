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

use crate::hierarchy::Hierarchy;
use crate::policy::GeneratedPolicy;
use crate::request::Request;
use arbitrary::{self, Unstructured};
use ast::{Entity, Expr, PolicyID, StaticPolicy, Template};
use cedar_policy_core::ast;
use cedar_policy_core::entities::Entities;
use indexmap::IndexMap;
use serde::Serialize;
use std::ops::{Deref, DerefMut};

/// Represents an RBAC hierarchy, ie, with no attributes
#[derive(Debug, Clone)]
pub struct RBACHierarchy(pub Hierarchy);

impl RBACHierarchy {
    /// Express the hierarchy as json
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

#[cfg(feature = "cedar-policy")]
impl TryFrom<RBACHierarchy> for cedar_policy::Entities {
    type Error = String;
    fn try_from(rbac: RBACHierarchy) -> Result<cedar_policy::Entities, String> {
        Entities::try_from(rbac).map(Into::into)
    }
}

/// Represents an RBAC entity, ie, without attributes
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

#[cfg(feature = "cedar-policy")]
impl From<RBACEntity> for cedar_policy::Entity {
    fn from(rbac: RBACEntity) -> cedar_policy::Entity {
        Entity::from(rbac).into()
    }
}

/// Represents an RBAC policy, ie, with no `when` or `unless` clauses
#[derive(Debug, Clone, Serialize)]
#[serde(transparent)]
pub struct RBACPolicy(pub GeneratedPolicy);

impl Deref for RBACPolicy {
    type Target = GeneratedPolicy;
    fn deref(&self) -> &GeneratedPolicy {
        &self.0
    }
}

impl DerefMut for RBACPolicy {
    fn deref_mut(&mut self) -> &mut GeneratedPolicy {
        &mut self.0
    }
}

impl From<RBACPolicy> for StaticPolicy {
    fn from(rbac: RBACPolicy) -> StaticPolicy {
        rbac.0.into()
    }
}

impl From<RBACPolicy> for Template {
    fn from(rbac: RBACPolicy) -> Template {
        rbac.0.into()
    }
}

#[cfg(feature = "cedar-policy")]
impl From<RBACPolicy> for cedar_policy::Policy {
    fn from(rbac: RBACPolicy) -> cedar_policy::Policy {
        StaticPolicy::from(rbac).into()
    }
}

#[cfg(feature = "cedar-policy")]
impl From<RBACPolicy> for cedar_policy::Template {
    fn from(rbac: RBACPolicy) -> cedar_policy::Template {
        Template::from(rbac).into()
    }
}

impl RBACPolicy {
    /// Generate an arbitrary RBAC policy
    pub fn arbitrary_for_hierarchy(
        fixed_id_opt: Option<PolicyID>,
        hierarchy: &Hierarchy,
        allow_slots: bool,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        Ok(Self(GeneratedPolicy::arbitrary_for_hierarchy(
            fixed_id_opt,
            None,
            hierarchy,
            allow_slots,
            Expr::val(true),
            u,
        )?))
    }

    /// size hint for arbitrary_for_hierarchy()
    pub fn arbitrary_size_hint(
        have_fixed_id: bool,
        allow_slots: bool,
        depth: usize,
    ) -> (usize, Option<usize>) {
        GeneratedPolicy::arbitrary_for_hierarchy_size_hint(have_fixed_id, allow_slots, depth)
    }
}

impl std::fmt::Display for RBACPolicy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// an RBAC authorization request (that is, one with an empty context)
#[derive(Debug, Clone)]
pub struct RBACRequest(pub Request);

impl Deref for RBACRequest {
    type Target = Request;
    fn deref(&self) -> &Request {
        &self.0
    }
}

impl DerefMut for RBACRequest {
    fn deref_mut(&mut self) -> &mut Request {
        &mut self.0
    }
}

impl From<RBACRequest> for ast::Request {
    fn from(rbac: RBACRequest) -> ast::Request {
        rbac.0.into()
    }
}

#[cfg(feature = "cedar-policy")]
impl From<RBACRequest> for cedar_policy::Request {
    fn from(rbac: RBACRequest) -> cedar_policy::Request {
        ast::Request::from(rbac).into()
    }
}

impl std::fmt::Display for RBACRequest {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl RBACRequest {
    /// Generate an arbitrary RBAC request
    pub fn arbitrary_for_hierarchy(
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        Ok(Self(Request::arbitrary_for_hierarchy(
            hierarchy,
            IndexMap::new(),
            u,
        )?))
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
