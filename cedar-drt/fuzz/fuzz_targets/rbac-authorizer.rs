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
use cedar_drt::{tests::run_auth_test, CedarLeanEngine};
use cedar_drt_inner::fuzz_target;

use cedar_policy::{Context, Entities, Policy, PolicySet, Request};
use cedar_policy_core::ast;

use libfuzzer_sys::arbitrary::{self, Arbitrary};
#[cfg(feature = "prt")]
use libfuzzer_sys::arbitrary::Unstructured;

#[derive(Arbitrary, Debug)]
pub struct AuthorizerInputAbstractEvaluator {
    /// Set of AbstractPolicy objects
    policies: Vec<AbstractPolicy>,
}

#[derive(Arbitrary, Debug, PartialEq, Eq, Clone)]
enum AbstractPolicy {
    /// Permit policy that evaluates 'true'
    PermitTrue,
    /// Permit policy that evaluates 'false'
    PermitFalse,
    /// Permit policy that errors
    PermitError,
    /// Forbid policy that evaluates 'true'
    ForbidTrue,
    /// Forbid policy that evaluates 'false'
    ForbidFalse,
    /// Forbid policy that evaluates 'error'
    ForbidError,
}

mod concrete_policies {
    use cedar_policy_core::{ast, parser};
    use std::sync::LazyLock;

    pub static PERMIT_TRUE: LazyLock<ast::StaticPolicy> = LazyLock::new(|| {
        parser::parse_policy(None, "permit(principal, action, resource);")
            .expect("should be a valid policy")
    });

    pub static PERMIT_FALSE: LazyLock<ast::StaticPolicy> = LazyLock::new(|| {
        parser::parse_policy(None, "permit(principal, action, resource) when { 1 == 0 };")
            .expect("should be a valid policy")
    });

    pub static PERMIT_ERROR: LazyLock<ast::StaticPolicy> = LazyLock::new(|| {
        parser::parse_policy(
            None,
            "permit(principal, action, resource) when { 1 < \"hello\" };",
        )
        .expect("should be a valid policy")
    });

    pub static FORBID_TRUE: LazyLock<ast::StaticPolicy> = LazyLock::new(|| {
        parser::parse_policy(None, "forbid(principal, action, resource);")
            .expect("should be a valid policy")
    });

    pub static FORBID_FALSE: LazyLock<ast::StaticPolicy> = LazyLock::new(|| {
        parser::parse_policy(None, "forbid(principal, action, resource) when { 1 == 0 };")
            .expect("should be a valid policy")
    });

    pub static FORBID_ERROR: LazyLock<ast::StaticPolicy> = LazyLock::new(|| {
        parser::parse_policy(
            None,
            "forbid(principal, action, resource) when { 1 < \"hello\" };",
        )
        .expect("should be a valid policy")
    });
}

impl AbstractPolicy {
    /// Convert the `AbstractPolicy` into a `Policy` with the given `id`
    fn into_policy(self, id: ast::PolicyID) -> ast::StaticPolicy {
        match self {
            AbstractPolicy::PermitTrue => concrete_policies::PERMIT_TRUE.new_id(id),
            AbstractPolicy::PermitFalse => concrete_policies::PERMIT_FALSE.new_id(id),
            AbstractPolicy::PermitError => concrete_policies::PERMIT_ERROR.new_id(id),
            AbstractPolicy::ForbidTrue => concrete_policies::FORBID_TRUE.new_id(id),
            AbstractPolicy::ForbidFalse => concrete_policies::FORBID_FALSE.new_id(id),
            AbstractPolicy::ForbidError => concrete_policies::FORBID_ERROR.new_id(id),
        }
    }
}

// This fuzz target is for differential-testing the `is_authorized()`
// functionality _assuming the correctness of the evaluator_.  We use only
// trivial policies and requests, and focus on how the authorizer combines the
// results.
fuzz_target!(|input: AuthorizerInputAbstractEvaluator| {
    let policies = input
        .policies
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, p)| p.into_policy(ast::PolicyID::from_string(format!("policy{i}"))));
    let mut policyset = PolicySet::new();
    for policy in policies {
        let policy = Policy::from(policy);
        policyset.add(policy).unwrap();
    }
    assert_eq!(policyset.policies().count(), input.policies.len());
    let entities = Entities::empty();
    let request = Request::new(
        "User::\"alice\"".parse().expect("should be valid"),
        "Action::\"read\"".parse().expect("should be valid"),
        "Resource::\"foo\"".parse().expect("should be valid"),
        Context::empty(),
        None,
    )
    .expect("we aren't doing request validation here, so new() can't fail");

    let lean_engine = CedarLeanEngine::new();

    // Check agreement with definitional engine. Note that run_auth_test returns
    // the result of the call to is_authorized.
    let res = run_auth_test(&lean_engine, &request, &policyset, &entities);

    // Check the following property: there should be an error reported iff we
    // had either PermitError or ForbidError
    let should_error = input
        .policies
        .iter()
        .any(|p| p == &AbstractPolicy::PermitError || p == &AbstractPolicy::ForbidError);
    if should_error {
        assert!(!res.diagnostics().errors().collect::<Vec<_>>().is_empty());
    } else {
        // doing the assertion this way, rather than assert!(.is_empty()), gives
        // us a better assertion-failure message (showing what items were
        // present on the LHS)
        assert_eq!(
            res.diagnostics()
                .errors()
                .map(ToString::to_string)
                .collect::<Vec<String>>(),
            Vec::<String>::new()
        );
    }
});
