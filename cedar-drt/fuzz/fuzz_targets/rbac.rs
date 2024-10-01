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

#![no_main]
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_core::entities::Entities;
use cedar_policy_core::extensions::Extensions;
use cedar_policy_generators::err::Result;
use cedar_policy_generators::hierarchy::{
    AttributesMode, EntityUIDGenMode, HierarchyGenerator, HierarchyGeneratorMode,
};
use cedar_policy_generators::policy::GeneratedLinkedPolicy;
use cedar_policy_generators::rbac::{RBACHierarchy, RBACPolicy, RBACRequest};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::info;
use serde::Serialize;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An RBAC hierarchy, policy set, and 8 associated requests
#[derive(Debug, Clone, Serialize)]
pub struct FuzzTargetInput {
    /// the hierarchy
    #[serde(skip)]
    pub hierarchy: RBACHierarchy,
    /// The policy set is made up of groups, each of which consists of either a
    /// single static policy or a template with one or more linked policies.
    ///
    /// We generate up to 2 groups with up to 4 linked policies each. We think
    /// the engine is unlikely to have bugs that are only triggered by policy
    /// sets larger than that.
    pub policy_groups: Vec<PolicyGroup>,
    /// the requests to try for this hierarchy and policy set. We try 8 requests
    /// per policy set / hierarchy
    #[serde(skip)]
    pub requests: [RBACRequest; 8],
}

#[derive(Debug, Clone, Serialize)]
pub enum PolicyGroup {
    StaticPolicy(RBACPolicy),
    TemplateWithLinks {
        template: RBACPolicy,
        links: Vec<GeneratedLinkedPolicy>,
    },
}

impl std::fmt::Display for FuzzTargetInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "policy groups: {:?}", &self.policy_groups)?;
        writeln!(f, "hierarchy: {}", &self.hierarchy)?;
        writeln!(f, "request: {}", &self.requests[0])?;
        writeln!(f, "request: {}", &self.requests[1])?;
        writeln!(f, "request: {}", &self.requests[2])?;
        writeln!(f, "request: {}", &self.requests[3])?;
        writeln!(f, "request: {}", &self.requests[4])?;
        writeln!(f, "request: {}", &self.requests[5])?;
        writeln!(f, "request: {}", &self.requests[6])?;
        writeln!(f, "request: {}", &self.requests[7])?;
        Ok(())
    }
}

fn arbitrary_vec<'a, T>(
    u: &mut Unstructured<'a>,
    min: Option<u32>,
    max: Option<u32>,
    mut f: impl FnMut(usize, &mut Unstructured<'a>) -> Result<T>,
) -> Result<Vec<T>> {
    let mut v: Vec<T> = vec![];
    u.arbitrary_loop(min, max, |u| {
        v.push(f(v.len(), u)?);
        Ok(std::ops::ControlFlow::Continue(()))
    })?;
    Ok(v)
}
fn arbitrary_vec_size_hint(_depth: usize) -> (usize, Option<usize>) {
    (0, None)
}

impl PolicyGroup {
    fn arbitrary_for_hierarchy(
        pg_idx: usize,
        hierarchy: &RBACHierarchy,
        u: &mut Unstructured<'_>,
    ) -> arbitrary::Result<Self> {
        // A policy ID collision would cause a DRT failure. The easiest way to
        // prevent that is to generate the policy IDs following a fixed pattern
        // rather than arbitrarily. We don't think the authorizer is likely to
        // have bugs triggered by specific policy IDs, so the loss of coverage
        // is unimportant.
        let policy = RBACPolicy::arbitrary_for_hierarchy(
            Some(ast::PolicyID::from_string(format!("p{}", pg_idx))),
            hierarchy,
            true,
            u,
        )?;
        if policy.has_slots() {
            let links = arbitrary_vec(u, Some(1), Some(4), |l_idx, u| {
                GeneratedLinkedPolicy::arbitrary(
                    ast::PolicyID::from_string(format!("t{}_l{}", pg_idx, l_idx)),
                    &policy,
                    hierarchy,
                    u,
                )
            })?;
            Ok(Self::TemplateWithLinks {
                template: policy,
                links,
            })
        } else {
            Ok(Self::StaticPolicy(policy))
        }
    }
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let hierarchy = RBACHierarchy(
            HierarchyGenerator {
                mode: HierarchyGeneratorMode::Arbitrary {
                    attributes_mode: AttributesMode::NoAttributesOrTags,
                },
                uid_gen_mode: EntityUIDGenMode::default(),
                num_entities: cedar_policy_generators::hierarchy::NumEntities::RangePerEntityType(
                    0..=4,
                ),
                u,
                extensions: Extensions::all_available(),
            }
            .generate()?,
        );
        let policy_groups: Vec<PolicyGroup> = arbitrary_vec(u, Some(1), Some(2), |idx, u| {
            Ok(PolicyGroup::arbitrary_for_hierarchy(idx, &hierarchy, u)?)
        })?;
        let requests = [
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
            RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?,
        ];
        Ok(Self {
            hierarchy,
            policy_groups,
            requests,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            HierarchyGenerator::size_hint(depth),
            arbitrary_vec_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
        ])
    }
}

// Fuzzing a single, pure-RBAC policy, with associated pure-RBAC hierarchy and
// pure-RBAC requests.
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let def_impl = LeanDefinitionalEngine::new();
    if let Ok(entities) = Entities::try_from(input.hierarchy) {
        let mut policyset = ast::PolicySet::new();
        for pg in input.policy_groups {
            match pg {
                PolicyGroup::StaticPolicy(p) => {
                    p.0.add_to_policyset(&mut policyset);
                }
                PolicyGroup::TemplateWithLinks { template, links } => {
                    template.0.add_to_policyset(&mut policyset);
                    for link in links {
                        link.add_to_policyset(&mut policyset);
                    }
                }
            };
        }
        for rbac_request in input.requests.into_iter() {
            let request = ast::Request::from(rbac_request);
            let (_, dur) =
                time_function(|| run_auth_test(&def_impl, request, &policyset, &entities));
            info!("{}{}", TOTAL_MSG, dur.as_nanos());
        }
    }
});
