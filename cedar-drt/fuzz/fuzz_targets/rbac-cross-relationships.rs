#![no_main]
use cedar_drt_inner::*;
use cedar_policy_core::ast::{self, EntityUIDEntry};
use cedar_policy_core::authorizer::Authorizer;
use cedar_policy_core::entities::Entities;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An RBAC hierarchy, policy, and 1 associated request
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// the hierarchy for the policy
    pub hierarchy: RBACHierarchy,
    /// the policy, which will be pure RBAC
    pub policy: RBACPolicy,
    /// the request
    pub request: RBACRequest,
}

impl std::fmt::Display for FuzzTargetInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "policy: {}", &self.policy)?;
        writeln!(f, "hierarchy: {}", &self.hierarchy)?;
        writeln!(f, "request: {}", &self.request)?;
        Ok(())
    }
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let hierarchy: RBACHierarchy = u.arbitrary()?;
        let policy = RBACPolicy::arbitrary_for_hierarchy(&hierarchy, u)?;
        let request = RBACRequest::arbitrary_for_hierarchy(&hierarchy, u)?;
        Ok(Self {
            hierarchy,
            policy,
            request,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <RBACHierarchy as Arbitrary>::size_hint(depth),
            RBACPolicy::arbitrary_size_hint(depth),
            RBACRequest::arbitrary_size_hint(depth),
        ])
    }
}

// This is a PBT fuzz target for testing properties about the hierarchy.
//
// The goal of this fuzz target is to justify the main fuzzer using entirely
// separate entity-name pools (or even hierarchy graphs) for principals,
// actions, and resources.
//
// It does this by asserting that hierarchy relationships (eg, parent
// relationships) between the `principal` and the `resource` of the request (or
// likewise, between either of those and the `action`) don't matter.  And
// likewise, hierarchy relationships between the entities in the `principal`
// and `resource` clauses of the policy don't matter. Etc.
fuzz_target!(|input: FuzzTargetInput| {
    match test_property(input.clone()) {
        Ok(()) => {}
        Err(e) => {
            println!("{input}");
            panic!("property failed to hold: {}", e);
        }
    }
});

/// Assert that hierarchy relationships (eg, parent relationships) between the
/// `principal` and the `resource` of the request (or likewise, between either
/// of those and the `action`) don't matter.  And likewise, hierarchy
/// relationships between the entities in the `principal` and `resource` clauses
/// of the policy don't matter. Etc.
///
/// Returns an `Err` if the property fails to hold.
///
/// NOTE: as of 5-5-22, this property is not expected to hold, and the fuzzer
/// easily finds counterexamples
fn test_property(input: FuzzTargetInput) -> std::result::Result<(), String> {
    if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
        let authorizer = Authorizer::new();
        let mut policyset = ast::PolicySet::new();
        policyset.add_static(input.policy.into()).unwrap();

        let q = ast::Request::from(input.request.clone());
        let orig_ans = authorizer.is_authorized(&q, &policyset, &entities);

        // making the `resource` of the request the parent of the
        // `principal` of the request shouldn't change the answer
        // (assuming both entities exist)
        let mut mod_hierarchy = input.hierarchy.clone();
        let q = ast::Request::from(input.request.clone());

        if let (EntityUIDEntry::Concrete(principal_euid), EntityUIDEntry::Concrete(resource_euid)) =
            (q.principal(), q.resource())
        {
            if mod_hierarchy.0.entity(resource_euid).is_some() {
                if let Some(principal) = mod_hierarchy.0.entity_mut(principal_euid) {
                    principal.add_ancestor(resource_euid.as_ref().clone());
                }
            }
        }

        let entities = Entities::try_from(mod_hierarchy)
            .map_err(|e| format!("failed to parse hierarchy after modification: {e}"))?;
        let new_ans = authorizer.is_authorized(&q, &policyset, &entities);
        if orig_ans != new_ans {
            return Err(format!("Answer changed when making the request resource the parent of the request principal.\norig answer: {:?}\nnew answer: {:?}", orig_ans, new_ans));
        }

        // making the `principal` of the request the parent of the
        // `resource` of the request shouldn't change the answer
        // (assuming both entities exist)
        let mut mod_hierarchy = input.hierarchy.clone();
        let q = ast::Request::from(input.request);

        if let (EntityUIDEntry::Concrete(principal_euid), EntityUIDEntry::Concrete(resource_euid)) =
            (q.principal(), q.resource())
        {
            if mod_hierarchy.0.entity(principal_euid).is_some() {
                if let Some(resource) = mod_hierarchy.0.entity_mut(resource_euid) {
                    resource.add_ancestor(principal_euid.as_ref().clone());
                }
            }
        }

        let entities = Entities::try_from(mod_hierarchy)
            .map_err(|e| format!("failed to parse hierarchy after modification: {e}"))?;
        let new_ans = authorizer.is_authorized(&q, &policyset, &entities);
        if orig_ans != new_ans {
            return Err(format!("Answer changed when making the request principal the parent of the request resource.\norig answer: {:?}\nnew answer: {:?}", orig_ans, new_ans));
        }
    }
    Ok(())
}
