#![no_main]
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_core::authorizer::{Authorizer, Decision};
use cedar_policy_core::entities::Entities;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target:
/// An RBAC hierarchy, policy set, and 8 associated requests
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// the hierarchy for the policy
    pub hierarchy: RBACHierarchy,
    /// the policies, which will be pure RBAC
    pub policies: Vec<RBACPolicy>,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [RBACRequest; 8],
}

impl std::fmt::Display for FuzzTargetInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "policies:")?;
        for policy in &self.policies {
            writeln!(f, "{policy}")?;
        }
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

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let hierarchy: RBACHierarchy = u.arbitrary()?;
        let mut policies = Vec::with_capacity(4);
        u.arbitrary_loop(Some(1), None, |u| {
            policies.push(RBACPolicy::arbitrary_for_hierarchy(&hierarchy, u)?);
            Ok(std::ops::ControlFlow::Continue(()))
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
            policies,
            requests,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <RBACHierarchy as Arbitrary>::size_hint(depth),
            // we hint for a single RBACPolicy, which is wrong, but it's just a hint
            RBACPolicy::arbitrary_size_hint(depth),
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

fuzz_target!(|input: FuzzTargetInput| {
    if let Ok(entities) = Entities::try_from(input.hierarchy) {
        let authorizer = Authorizer::new();
        let queries = input
            .requests
            .into_iter()
            .map(ast::Request::from)
            .collect::<Vec<_>>();

        // first we set all the policies to Forbid, and test we always get Deny
        let mut policyset = ast::PolicySet::new();
        for mut policy in input.policies.clone() {
            policy.0.effect = ast::Effect::Forbid;
            policyset.add_static(policy.into()).unwrap();
        }
        for q in &queries {
            let ans = authorizer.is_authorized(q, &policyset, &entities);
            assert_eq!(ans.decision, Decision::Deny);
        }

        // then we set all the policies to Permit, and test we never get an
        // explicit Deny; that is, every Deny has no `reasons`.
        let mut policyset = ast::PolicySet::new();
        for mut policy in input.policies {
            policy.0.effect = ast::Effect::Permit;
            policyset.add_static(policy.into()).unwrap();
        }
        for q in &queries {
            let ans = authorizer.is_authorized(q, &policyset, &entities);
            if ans.decision == Decision::Deny {
                assert!(ans.diagnostics.reason.is_empty());
            }
        }
    }
});
