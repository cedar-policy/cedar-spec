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

#![no_main]
use cedar_drt::ast::PolicyID;
use cedar_drt::*;
use cedar_drt_inner::fuzz_target;
use cedar_policy_core::ast;
use cedar_policy_core::authorizer::{Authorizer, Diagnostics, Response};
use cedar_policy_core::entities::Entities;
use libfuzzer_sys::arbitrary::{self, Arbitrary};

#[derive(Arbitrary, Debug)]
struct AuthorizerInputAbstractEvaluator {
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
    fn into_policy(self, id: PolicyID) -> ast::StaticPolicy {
        match self {
            AbstractPolicy::PermitTrue => concrete_policies::PERMIT_TRUE.clone().new_id(id),
            AbstractPolicy::PermitFalse => concrete_policies::PERMIT_FALSE.clone().new_id(id),
            AbstractPolicy::PermitError => concrete_policies::PERMIT_ERROR.clone().new_id(id),
            AbstractPolicy::ForbidTrue => concrete_policies::FORBID_TRUE.clone().new_id(id),
            AbstractPolicy::ForbidFalse => concrete_policies::FORBID_FALSE.clone().new_id(id),
            AbstractPolicy::ForbidError => concrete_policies::FORBID_ERROR.clone().new_id(id),
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
        .map(|(i, p)| p.into_policy(PolicyID::from_string(format!("policy{i}"))));
    let mut policyset = ast::PolicySet::new();
    for policy in policies {
        policyset.add_static(policy).unwrap();
    }
    assert_eq!(policyset.policies().count(), input.policies.len());
    let entities = Entities::new();
    let authorizer = Authorizer::new();
    let q = ast::Request::new(
        "User::\"alice\"".parse().expect("should be valid"),
        "Action::\"read\"".parse().expect("should be valid"),
        "Resource::\"foo\"".parse().expect("should be valid"),
        ast::Context::empty(),
    );
    let rust_res = authorizer.is_authorized(&q, &policyset, &entities);

    // check property: there should be an error reported iff we had either PermitError or ForbidError
    let should_error = input
        .policies
        .iter()
        .any(|p| p == &AbstractPolicy::PermitError || p == &AbstractPolicy::ForbidError);
    if should_error {
        assert!(!rust_res.diagnostics.errors.is_empty());
    } else {
        // doing the assertion this way, rather than assert!(.is_empty()), gives
        // us a better assertion-failure message (showing what items were
        // present on the LHS)
        assert_eq!(
            rust_res
                .diagnostics
                .errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>(),
            Vec::<String>::new()
        );
    }

    // check agreement with definitional engine
    // for now, we expect never to receive errors from the definitional engine,
    // and we otherwise ignore errors in the comparison
    let definitional_engine =
        DefinitionalEngine::new().expect("failed to create definitional engine");
    let definitional_res = definitional_engine.is_authorized(&q, &policyset, &entities);
    assert_eq!(
        definitional_res
            .diagnostics()
            .errors()
            .map(|e| e.to_string())
            .collect::<Vec<String>>(),
        Vec::<String>::new()
    );
    let rust_res_for_comparison: cedar_policy::Response = Response {
        diagnostics: Diagnostics {
            errors: Vec::new(),
            ..rust_res.diagnostics
        },
        ..rust_res
    }
    .into();
    assert_eq!(
        rust_res_for_comparison, definitional_res,
        "Mismatch for {q}\nPolicies:\n{}\nEntities:\n{}",
        &policyset, &entities
    );
});
