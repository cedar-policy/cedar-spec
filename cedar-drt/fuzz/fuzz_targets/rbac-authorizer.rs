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
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_core::entities::Entities;
use cedar_policy_core::parser;
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

impl AbstractPolicy {
    /// Convert the `AbstractPolicy` into a `Policy` with the given `id`
    fn into_policy(self, id: String) -> ast::StaticPolicy {
        match self {
            AbstractPolicy::PermitTrue => {
                parser::parse_policy(Some(id), "permit(principal, action, resource);")
                    .expect("should be a valid policy")
            }
            AbstractPolicy::PermitFalse => parser::parse_policy(
                Some(id),
                "permit(principal, action, resource) when { 1 == 0 };",
            )
            .expect("should be a valid policy"),
            AbstractPolicy::PermitError => parser::parse_policy(
                Some(id),
                "permit(principal, action, resource) when { 1 < \"hello\" };",
            )
            .expect("should be a valid policy"),
            AbstractPolicy::ForbidTrue => {
                parser::parse_policy(Some(id), "forbid(principal, action, resource);")
                    .expect("should be a valid policy")
            }
            AbstractPolicy::ForbidFalse => parser::parse_policy(
                Some(id),
                "forbid(principal, action, resource) when { 1 == 0 };",
            )
            .expect("should be a valid policy"),
            AbstractPolicy::ForbidError => parser::parse_policy(
                Some(id),
                "forbid(principal, action, resource) when { 1 < \"hello\" };",
            )
            .expect("should be a valid policy"),
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
        .map(|(i, p)| p.into_policy(format!("policy{i}")));
    let mut policyset = ast::PolicySet::new();
    for policy in policies {
        policyset.add_static(policy).unwrap();
    }
    assert_eq!(policyset.policies().count(), input.policies.len());
    let entities = Entities::new();
    let request = ast::Request::new(
        "User::\"alice\"".parse().expect("should be valid"),
        "Action::\"read\"".parse().expect("should be valid"),
        "Resource::\"foo\"".parse().expect("should be valid"),
        ast::Context::empty(),
    );

    // Check agreement with definitional engine. Note that run_auth_test returns
    // the result of the call to is_authorized.
    let java_def_engine =
        JavaDefinitionalEngine::new().expect("failed to create definitional engine");
    let res = run_auth_test(&java_def_engine, &request, &policyset, &entities);

    // Check the following property: there should be an error reported iff we
    // had either PermitError or ForbidError
    let should_error = input
        .policies
        .iter()
        .any(|p| p == &AbstractPolicy::PermitError || p == &AbstractPolicy::ForbidError);
    if should_error {
        assert!(!res.diagnostics.errors.is_empty());
    } else {
        // doing the assertion this way, rather than assert!(.is_empty()), gives
        // us a better assertion-failure message (showing what items were
        // present on the LHS)
        assert_eq!(
            res.diagnostics
                .errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<String>>(),
            Vec::<String>::new()
        );
    }
});
