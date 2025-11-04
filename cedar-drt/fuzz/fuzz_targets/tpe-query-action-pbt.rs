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
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{abac, fuzz_target, tpe::entities_to_partial_entities};
use cedar_policy::{
    ActionQueryRequest, Decision, EntityId, PartialEntities, PartialEntityUid, PolicySet, Request,
    ValidationMode, Validator,
};
use cedar_policy_generators::abac::ABACRequest;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use std::collections::HashMap;
use std::convert::TryFrom;

#[derive(Debug, Clone)]
struct FuzzTargetInput {
    pub abac_input: abac::FuzzTargetInput<true>,
    pub partial_requests: [ActionQueryRequest; 8],
    pub partial_entities: PartialEntities,
}

fn make_action_query_request(
    req: &ABACRequest,
    schema: cedar_policy::Schema,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<ActionQueryRequest> {
    Ok(ActionQueryRequest::new(
        PartialEntityUid::new(
            req.principal.entity_type().clone().into(),
            if u.ratio(1, 4)? {
                None
            } else {
                Some(EntityId::new(req.principal.eid().as_ref()))
            },
        ),
        PartialEntityUid::new(
            req.resource.entity_type().clone().into(),
            if u.ratio(1, 4)? {
                None
            } else {
                Some(EntityId::new(req.resource.eid().as_ref()))
            },
        ),
        if u.ratio(1, 4)? {
            None
        } else {
            Some(req.context.clone().into())
        },
        schema,
    )
    .unwrap())
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let abac_input = abac::FuzzTargetInput::<true>::arbitrary(u)?;
        let cedar_schema: cedar_policy::Schema = abac_input
            .schema
            .clone()
            .try_into()
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let partial_requests = abac_input
            .requests
            .iter()
            .map(|req| make_action_query_request(req, cedar_schema.clone(), u))
            .collect::<arbitrary::Result<Vec<_>>>()?
            .try_into()
            .unwrap();
        let partial_entities =
            entities_to_partial_entities(abac_input.entities.iter(), u, &cedar_schema)?;
        Ok(Self {
            abac_input,
            partial_requests,
            partial_entities,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        abac::FuzzTargetInput::<true>::try_size_hint(depth)
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();

    let mut policyset = PolicySet::new();
    policyset.add(input.abac_input.policy.into()).unwrap();

    let cedar_schema = cedar_policy::Schema::try_from(input.abac_input.schema.clone()).unwrap();

    let validator = Validator::new(cedar_schema);
    if !validator
        .validate(&policyset, ValidationMode::Strict)
        .validation_passed()
    {
        // Even with type-directed generation, policies might not be well typed.
        // This would cause `query_principal` to return an error.
        return;
    }

    let auth = cedar_policy::Authorizer::new();
    for (request, action_request) in input
        .abac_input
        .requests
        .into_iter()
        .zip(input.partial_requests)
    {
        let request: Request = request.into();
        let resp = auth.is_authorized(&request, &policyset, &input.abac_input.entities);

        let actions: HashMap<_, _> = policyset
            .query_action(&action_request, &input.partial_entities)
            .unwrap()
            .collect();
        match actions.get(request.action().unwrap()) {
            Some(Some(Decision::Allow)) => {
                assert_eq!(
                    resp.decision(),
                    Decision::Allow,
                    "action in query as `Some(Decisions::Allow)` action must allow\n{request:#?}"
                )
            }
            None => {
                assert_eq!(
                    resp.decision(),
                    Decision::Deny,
                    "action not in query must deny\n{request:#?}"
                )
            }
            Some(None) => (),
            Some(Some(Decision::Deny)) => panic!(
                "did not expect `Decision::Deny` in action query result (for action `{}`)",
                request.action().unwrap()
            ),
        }
    }
});
