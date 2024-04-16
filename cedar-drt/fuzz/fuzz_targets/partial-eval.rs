/*
 * Copyright Cedar Contributors. All Rights Reserved.
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
use cedar_policy_core::ast::Policy;
use cedar_policy_core::ast::PolicyID;
use cedar_policy_core::ast::PolicySet;
use cedar_policy_core::ast::Value;
use cedar_policy_core::authorizer::AuthorizationError;
use cedar_policy_core::authorizer::{Authorizer, PartialResponse, Response};
use cedar_policy_core::entities::Entities;
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    err::Error,
    hierarchy::HierarchyGenerator,
    schema::Schema,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use serde::Serialize;
use smol_str::SmolStr;
use std::collections::HashMap;
use std::collections::HashSet;
use std::convert::TryFrom;
use std::sync::Arc;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone, Serialize)]
struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    /// generated entity slice
    #[serde(skip)]
    pub entities: Entities,
    /// generated policy
    pub policy: ABACPolicy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    #[serde(skip)]
    pub requests: [ABACRequest; 8],
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 3,
    max_width: 3,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: true,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;

        let requests = [
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
        ];
        let all_entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let entities = drop_some_entities(all_entities, u)?;
        Ok(Self {
            schema,
            entities,
            policy,
            requests,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
        ])
    }
}

/// Check if two `Response`s are equivalent.
/// They are equivalent iff:
///   1) They decision is the same
///   2) If one decision has any errors, the other decision
///      must have at least one error.
///      (The error contents and number of errors do not need to be equal)
fn responses_equiv(a1: Response, a2: Response) -> bool {
    (a1.decision == a2.decision)
        && (a1.diagnostics.errors.is_empty() == a2.diagnostics.errors.is_empty())
}

/// Substitute all policies in the set according to the mapping
fn substitute_set(p: &PolicySet, mapping: &HashMap<SmolStr, Value>) -> PolicySet {
    let mut new_set = PolicySet::default();
    for policy in p.policies() {
        new_set
            .add(substitute_policy(policy, mapping))
            .expect("Failed to add substituted policy to set");
    }

    new_set
}

/// Substitute the condition clause of this policy according to the mapping
fn substitute_policy(p: &Policy, mapping: &HashMap<SmolStr, Value>) -> Policy {
    let condition = p.condition().substitute(mapping);
    Policy::from_when_clause_annos(
        p.effect(),
        Arc::new(condition),
        p.id().clone(),
        p.annotations_arc().clone(),
    )
}

fn get_id(e: &AuthorizationError) -> &PolicyID {
    match e {
        AuthorizationError::PolicyEvaluationError { id, .. } => id,
    }
}

/// Check if a partial response is consistent with a concrete response
fn partial_response_correctness(partial: &PartialResponse, concrete: &Response) {
    let actually_errored: HashSet<_> = concrete.diagnostics.errors.iter().map(get_id).collect();
    let partial_errored: HashSet<_> = partial.definitely_errored().collect();
    // Ensure the errors in the concrete response are a superset of errors in the partial
    // response
    assert!(actually_errored.is_superset(&partial_errored));
    let determining = &concrete.diagnostics.reason;
    // Ensure that `may_be_determining` produces an over approximation of policies in the
    // reasons set
    let over_approx = partial
        .may_be_determining()
        .cloned()
        .collect::<HashSet<_>>();
    assert!(over_approx.is_superset(&determining));
    // Ensure that `must_be_determining` produces an under approximation of policies in the
    // reasons set
    let under_approx = partial
        .must_be_determining()
        .cloned()
        .collect::<HashSet<_>>();
    assert!(determining.is_superset(&under_approx));
}

// The main fuzz target. This is for type-directed fuzzing of ABAC
// hierarchy/policy/requests
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let mut policyset = ast::PolicySet::new();
    policyset.add_static(input.policy.into()).unwrap();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("Policies: {policyset}\n");
    let mapping = input
        .schema
        .unknown_pool
        .mapping()
        .map(|(k, v)| (SmolStr::from(k), v))
        .collect();

    if policyset.policies().all(|p| !p.condition().is_unknown()) {
        return; // Don't waste time testing a policy w/ no unknowns
    }

    for q in input.requests.into_iter().map(ast::Request::from) {
        let auth = Authorizer::new();
        let ans = auth.is_authorized_core(q.clone(), &policyset, &input.entities);

        if let Some(_decision) = ans.decision() {
            // Concrete evaluation should also succeed w/out any substitutions
            let concrete_res = auth.is_authorized(q, &policyset, &input.entities);
            assert!(responses_equiv(ans.into(), concrete_res));
        } else {
            // If we are not able to reach a concrete decision:
            // First we ensure that if we substitute the residuals and evaluate, we get a concrete
            // answer consistent with the partial response
            let concrete_response = ans
                .reauthorize(&mapping, &auth, q.clone(), &input.entities)
                .unwrap();
            assert!(
                concrete_response.decision().is_some(),
                "Substituting all `unknown`s should give a decision"
            );
            let concrete: Response = concrete_response.into();
            partial_response_correctness(&ans, &concrete);

            // Then we check if we substitute the original policies and evaluate, we get a concrete
            // answer consistent with the partial answer
            let substituted_start = substitute_set(&policyset, &mapping);
            let final_answer = auth.is_authorized(q.clone(), &substituted_start, &input.entities);
            partial_response_correctness(&ans, &final_answer);

            // Then check that those two concrete responses are equivalent
            assert!(responses_equiv(concrete, final_answer));
        }
    }
});
