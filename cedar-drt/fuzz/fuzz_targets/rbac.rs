#![no_main]
use cedar_policy_core::ast;
use cedar_policy_core::entities::Entities;
use cedar_drt::*;
use cedar_drt_inner::*;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::info;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An RBAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// the hierarchy for the policy
    pub hierarchy: RBACHierarchy,
    /// the policy, which will be pure RBAC
    pub policy: RBACPolicy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [RBACRequest; 8],
}

impl std::fmt::Display for FuzzTargetInput {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "policy: {}", &self.policy)?;
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
        let policy = RBACPolicy::arbitrary_for_hierarchy(&hierarchy, u)?;
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
            policy,
            requests,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <RBACHierarchy as Arbitrary>::size_hint(depth),
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

// The main fuzz target. This is for fuzzing a single, pure-RBAC policy, with
// associated pure-RBAC hierarchy and pure-RBAC requests
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    /*
    let mut logfile = std::fs::OpenOptions::new()
        .write(true)
        .append(true)
        .open("fuzz/generated_inputs.txt")
        .unwrap();
    writeln!(logfile, "{input}\n").unwrap();
    */
    if let Ok(entities) = Entities::try_from(input.hierarchy) {
        let mut policyset = ast::PolicySet::new();
        policyset.add_static(input.policy.into()).unwrap();
        let diff_tester = DifferentialTester::new();
        for r in input.requests.into_iter() {
            let q = ast::Request::from(r);
            let (_, dur) = time_function(|| diff_tester.run_single_test(&q, &policyset, &entities));
            info!("{}{}", TOTAL_MSG, dur.as_nanos());
        }
    }
});
