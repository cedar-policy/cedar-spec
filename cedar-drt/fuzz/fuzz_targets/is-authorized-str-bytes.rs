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

//! Bytes `is-authorized-str` target. Takes three arbitrary strings (policy
//! text, entities JSON, request JSON) and feeds identical bytes to the Rust
//! public API and the Lean `isAuthorizedStr` FFI. Both parse the three strings
//! independently (schema-free). Fails on any difference:
//!
//!   - accept/reject divergence: if one side parses all three strings and the
//!     other rejects them, that is a failure (the ingestion paths disagree on
//!     what a valid input is);
//!   - when both accept: decision + determining + erroring policies must match.
//!
//! Coverage-guided mutation starting from a valid corpus keeps many inputs
//! "almost valid," so this exercises both the parse-disagreement surface and
//! the authorization path on perturbed-but-valid inputs.

use cedar_drt_inner::{fuzz_target, is_authorized_str};

use cedar_lean_ffi::CedarLeanFfi;

fuzz_target!(|input: (String, String, String)| {
    let (policy_text, entities_json, request_json) = input;

    let lean_engine = CedarLeanFfi::new();

    let rust_result =
        is_authorized_str::rust_authorize_from_strings(&policy_text, &entities_json, &request_json);
    let lean_result =
        lean_engine.is_authorized_str(&policy_text, &entities_json, &request_json);

    match (rust_result, lean_result) {
        (Some(rust_response), Ok(lean_response)) => {
            // Both accepted: decisions and policy sets must match.
            assert_eq!(
                rust_response.decision(),
                lean_response.decision(),
                "Decision mismatch.\nPolicies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}"
            );
            let rust_determining: std::collections::HashSet<_> =
                rust_response.diagnostics().reason().cloned().collect();
            assert_eq!(
                &rust_determining,
                lean_response.determining_policies(),
                "Determining-policy mismatch.\nPolicies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}"
            );
            let rust_erroring: std::collections::HashSet<_> = rust_response
                .diagnostics()
                .errors()
                .map(|e| match e {
                    cedar_policy::AuthorizationError::PolicyEvaluationError(err) => {
                        err.policy_id().clone()
                    }
                })
                .collect();
            assert_eq!(
                &rust_erroring,
                lean_response.erroring_policies(),
                "Erroring-policy mismatch.\nPolicies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}"
            );
        }
        (Some(_), Err(lean_err)) => {
            panic!(
                "Rust accepted input but Lean rejected it.\n\
                 Policies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}\n\
                 Lean error: {lean_err}"
            );
        }
        (None, Ok(_)) => {
            panic!(
                "Lean accepted input but Rust rejected it.\n\
                 Policies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}"
            );
        }
        (None, Err(_)) => {
            // Both rejected. Agreement on rejection is the pass case; we do not
            // require the error messages themselves to match.
        }
    }
});
