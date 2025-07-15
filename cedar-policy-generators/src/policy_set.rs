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
use crate::schema::Schema;
use arbitrary::Unstructured;
use cedar_policy_core::ast;
use cedar_policy_core::ast::PolicyID;
use serde::Serialize;
use std::collections::HashSet;
use std::fmt::Display;

/// Minimum (inclusive) number of policies to attempt to generate for a [`GeneratedPolicySet`].
const MIN_LENGTH: usize = 1;
/// Maximum (inclusive) number of policies to attempt to generate for a [`GeneratedPolicySet`].
const MAX_LENGTH: usize = 6;

/// Data structure representing a set of generated templates and static policies.
#[derive(Debug, Clone, Serialize)]
pub struct GeneratedPolicySet(Vec<GeneratedPolicy>);

impl GeneratedPolicySet {
    /// Generate an arbitrary [`GeneratedPolicySet`]
    pub fn arbitrary_for_hierarchy(
        schema: &Schema,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        let mut ids: HashSet<PolicyID> = HashSet::new();
        let len = u.int_in_range(MIN_LENGTH..=MAX_LENGTH)?;
        let mut policies: Vec<GeneratedPolicy> = Vec::with_capacity(len);
        for _ in 0..len {
            let id: PolicyID = u.arbitrary()?;
            // Skip duplicate IDs
            if ids.insert(id.clone()) {
                let abac_constraints = schema.arbitrary_abac_constraints(hierarchy, u)?;
                let policy = GeneratedPolicy::arbitrary_for_hierarchy(
                    Some(id),
                    Some(schema),
                    hierarchy,
                    true,
                    abac_constraints,
                    u,
                )?;
                policies.push(policy);
            }
        }
        Ok(Self(policies))
    }

    /// size_hint for [`Self::arbitrary_for_hierarchy()`]
    pub fn arbitrary_for_hierarchy_size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None)
    }
}

impl From<GeneratedPolicySet> for ast::PolicySet {
    fn from(generated: GeneratedPolicySet) -> Self {
        let mut p_set = ast::PolicySet::new();
        for policy in generated.0 {
            policy.add_to_policyset(&mut p_set);
        }
        p_set
    }
}

#[cfg(feature = "cedar-policy")]
impl TryFrom<GeneratedPolicySet> for cedar_policy::PolicySet {
    type Error = cedar_policy::PolicySetError;
    fn try_from(generated: GeneratedPolicySet) -> Result<Self, Self::Error> {
        ast::PolicySet::from(generated).try_into()
    }
}

impl Display for GeneratedPolicySet {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.0.iter();
        if let Some(arg) = iter.next() {
            write!(f, "{}", arg)?;
            for policy in iter {
                write!(f, "\n{}", policy)?
            }
        }
        Ok(())
    }
}
