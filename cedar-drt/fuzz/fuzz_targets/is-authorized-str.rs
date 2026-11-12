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

//! Structured `is-authorized-str` target. Generates an ABAC policy/hierarchy/
//! requests, serializes them to the three strings the Lean `isAuthorizedStr`
//! FFI takes (policy text, entities JSON, request JSON), runs the Rust
//! authorizer as the reference, and asserts Rust and Lean agree exactly
//! (decision + determining + erroring policies). Fails on any difference,
//! including accept/reject divergence.

use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target, is_authorized_str};

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Authorizer, PolicySet, Request};
use std::str::FromStr;

fuzz_target!(|input: FuzzTargetInput<false>| {
    let policyset = input.policy.0.clone().into_policy_set();
    let entities = input.entities;
    let requests = input
        .requests
        .into_iter()
        .map(Request::from)
        .collect::<Vec<_>>();

    let lean_engine = CedarLeanFfi::new();
    let authorizer = Authorizer::new();

    for request in requests.iter() {
        let Some((policy_text, entities_json, request_json)) =
            is_authorized_str::serialize_inputs(&policyset, &entities, request)
        else {
            // Skip requests whose components can't be serialized (e.g. unknown
            // principal/action/resource); these targets don't exercise them.
            continue;
        };

        // Authorize on the Rust side over the *reparsed* policy text, not the
        // original policy set. Cedar policy source text does not preserve the
        // original policy IDs (the parser assigns fresh ones like `policy0`), so
        // authorizing the original set would compare determining/erroring policy
        // IDs that can never match Lean's, which parses the same text. Reparsing
        // makes both sides consume identical bytes and assign identical IDs.
        let reparsed = PolicySet::from_str(&policy_text)
            .expect("policy text we just serialized should reparse");
        let rust_response = authorizer.is_authorized(request, &reparsed, &entities);

        is_authorized_str::assert_agree(
            &lean_engine,
            &policy_text,
            &entities_json,
            &request_json,
            &rust_response,
        );
    }
});
