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

//! Shared harness for the `is-authorized-str` fuzz targets, which drive the
//! Lean `isAuthorizedStr` FFI export. Every input enters Lean as a string: the
//! policies as Cedar source text, and the entities and request as Cedar JSON.
//! Lean parses/deserializes all three itself (verified policy parser +
//! `Lean.Data.Json`-based readers) and authorizes.
//!
//! Both targets fail on *any* difference between Rust and Lean, including
//! accept/reject divergence: if one side parses the three strings and the other
//! rejects them, that is a test failure, since it means the two ingestion paths
//! disagree on what a valid input is.

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{
    Authorizer, Context, Entities, EntityUid, PolicySet, Request, Response,
};
use serde_json::json;

/// Build the request JSON that Lean's request reader expects:
/// `{ "principal": <EntityUidJson>, "action": ..., "resource": ..., "context": {..} }`.
///
/// Returns `None` if any request component is "unknown" (partial-eval requests),
/// which these targets do not exercise.
pub fn request_to_json(request: &Request) -> Option<serde_json::Value> {
    let principal = request.principal()?.to_json_value().ok()?;
    let action = request.action()?.to_json_value().ok()?;
    let resource = request.resource()?.to_json_value().ok()?;
    let context = request.context()?.to_json_value().ok()?;
    Some(json!({
        "principal": principal,
        "action": action,
        "resource": resource,
        "context": context,
    }))
}

/// Turn a `cedar_policy::EntityUid` JSON value into the string form.
fn to_string_pretty(v: &serde_json::Value) -> String {
    v.to_string()
}

/// Run the Rust authorizer and the Lean `isAuthorizedStr` FFI over the same
/// three strings and assert they agree exactly (decision + determining policies
/// + erroring policies). Panics on any difference.
///
/// `rust_response` is the reference `Response` computed by the Rust authorizer
/// over the *structured* inputs (before serialization). Passing it in lets the
/// structured target reuse the authorization it already ran.
pub fn assert_agree(
    lean_engine: &CedarLeanFfi,
    policy_text: &str,
    entities_json: &str,
    request_json: &str,
    rust_response: &Response,
) {
    let lean_response = lean_engine
        .is_authorized_str(policy_text, entities_json, request_json)
        .unwrap_or_else(|err| {
            panic!(
                "Lean rejected input that Rust accepted.\n\
                 Policies:\n{policy_text}\n\
                 Entities:\n{entities_json}\n\
                 Request:\n{request_json}\n\
                 Lean error: {err}"
            )
        });

    // Decision.
    assert_eq!(
        rust_response.decision(),
        lean_response.decision(),
        "Decision mismatch.\nPolicies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}"
    );

    // Determining policies.
    let rust_determining: std::collections::HashSet<_> =
        rust_response.diagnostics().reason().cloned().collect();
    assert_eq!(
        &rust_determining,
        lean_response.determining_policies(),
        "Determining-policy mismatch.\nPolicies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}"
    );

    // Erroring policies.
    let rust_erroring: std::collections::HashSet<_> = rust_response
        .diagnostics()
        .errors()
        .map(|e| match e {
            cedar_policy::AuthorizationError::PolicyEvaluationError(err) => err.policy_id().clone(),
        })
        .collect();
    assert_eq!(
        &rust_erroring,
        lean_response.erroring_policies(),
        "Erroring-policy mismatch.\nPolicies:\n{policy_text}\nEntities:\n{entities_json}\nRequest:\n{request_json}"
    );
}

/// The Rust reference path for the *bytes* target: parse the three arbitrary
/// strings via the public API exactly as the Lean side does (three independent
/// parses, schema-free), returning the authorization `Response` iff all three
/// parse. Returns `None` if any of the three strings is rejected.
///
/// This mirrors what `isAuthorizedStr` does on the Lean side so that both sides
/// consume identical bytes and the accept/reject comparison is meaningful.
pub fn rust_authorize_from_strings(
    policy_text: &str,
    entities_json: &str,
    request_json: &str,
) -> Option<Response> {
    let policies = PolicySet::from_str(policy_text).ok()?;
    let entities = Entities::from_json_str(entities_json, None).ok()?;
    let request = request_from_json_str(request_json)?;
    let authorizer = Authorizer::new();
    Some(authorizer.is_authorized(&request, &policies, &entities))
}

/// Parse a request from the `{principal, action, resource, context}` JSON shape,
/// schema-free, using the public API. Returns `None` on any parse error.
fn request_from_json_str(request_json: &str) -> Option<Request> {
    let v: serde_json::Value = serde_json::from_str(request_json).ok()?;
    let obj = v.as_object()?;
    let principal = EntityUid::from_json(obj.get("principal")?.clone()).ok()?;
    let action = EntityUid::from_json(obj.get("action")?.clone()).ok()?;
    let resource = EntityUid::from_json(obj.get("resource")?.clone()).ok()?;
    let context = match obj.get("context") {
        Some(c) => Context::from_json_value(c.clone(), None).ok()?,
        None => Context::empty(),
    };
    Request::new(principal, action, resource, context, None).ok()
}

use std::str::FromStr;

/// Serialize a structured ABAC input to the three strings the Lean FFI takes:
/// policy source text, entities JSON, and request JSON.
pub fn serialize_inputs(
    policyset: &PolicySet,
    entities: &Entities,
    request: &Request,
) -> Option<(String, String, String)> {
    let policy_text = policyset.to_string();
    let entities_json = entities.to_json_value().ok()?.to_string();
    let request_json = to_string_pretty(&request_to_json(request)?);
    Some((policy_text, entities_json, request_json))
}
