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
use crate::authorizer::{Response, ResponseKind};
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_core::ast::Policy;
use cedar_policy_core::ast::PolicySet;
use cedar_policy_core::authorizer::Authorizer;
use cedar_policy_core::entities::{Entities, TCComputation};
pub use cedar_policy_core::*;
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    err::Error,
    schema::Schema,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use smol_str::SmolStr;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// generated entity slice
    pub entities: Entities,
    /// generated policy
    pub policy: ABACPolicy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
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
            Schema::arbitrary_hierarchy_size_hint(depth),
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

fn drop_some_entities(entities: Entities, u: &mut Unstructured<'_>) -> arbitrary::Result<Entities> {
    let should_drop: bool = u.arbitrary()?;
    if should_drop {
        let mut set: Vec<_> = vec![];
        for entity in entities.iter() {
            match u.int_in_range(0..=9)? {
                0 => (),
                _ => {
                    set.push(entity.clone());
                }
            }
        }
        Ok(
            Entities::from_entities(set.into_iter(), TCComputation::AssumeAlreadyComputed)
                .expect("Should be valid"),
        )
    } else {
        Ok(entities)
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

    for q in input.requests.into_iter().map(Into::into) {
        let auth = Authorizer::new();
        let ans = auth.is_authorized_core(&q, &policyset, &input.entities);

        match ans {
            ResponseKind::FullyEvaluated(ans) => {
                // Concrete evaluation should also succeed w/out any substitutions
                let concrete_res = auth.is_authorized(&q, &policyset, &input.entities);
                assert!(responses_equiv(ans, concrete_res));
            }
            ResponseKind::Partial(residual_set) => {
                let mut subst_set = PolicySet::new();
                for policy in residual_set.residuals.policies().map(|p: &Policy| {
                    let subst = p.condition().substitute(&mapping).unwrap();
                    Policy::from_when_clause(p.effect(), subst, p.id().clone())
                }) {
                    subst_set.add(policy).unwrap();
                }
                let final_res = auth.is_authorized(&q, &subst_set, &input.entities);

                let mut concrete_set = PolicySet::new();
                for policy in policyset.policies().map(|p: &Policy| {
                    let subst = p.condition().substitute(&mapping).unwrap();
                    Policy::from_when_clause(p.effect(), subst, p.id().clone())
                }) {
                    concrete_set.add(policy).unwrap();
                }
                let concrete_res = auth.is_authorized(&q, &concrete_set, &input.entities);
                assert!(responses_equiv(concrete_res, final_res));
            }
        };
    }
});
