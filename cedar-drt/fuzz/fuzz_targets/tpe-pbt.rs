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
    Authorizer, Entities, EntityId, PartialEntities, PartialEntityUid, PartialRequest, Policy,
    PolicySet, Request, Schema, Validator,
};
use cedar_policy_core::ast::RequestSchema;
use cedar_policy_core::extensions::Extensions;
use cedar_policy_generators::abac::ABACRequest;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, schema, and 8 associated policies
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    pub abac_input: abac::FuzzTargetInput<true>,
    pub partial_requests: [PartialRequest; 8],
    pub partial_entities: PartialEntities,
}

fn make_partial_request(
    req: &ABACRequest,
    u: &mut Unstructured<'_>,
    schema: &Schema,
) -> arbitrary::Result<PartialRequest> {
    PartialRequest::new(
        PartialEntityUid::new(
            req.principal.entity_type().clone().into(),
            if u.ratio(1, 4)? {
                None
            } else {
                Some(EntityId::new(req.principal.eid()))
            },
        ),
        req.action.clone().into(),
        PartialEntityUid::new(
            req.resource.entity_type().clone().into(),
            if u.ratio(1, 4)? {
                None
            } else {
                Some(EntityId::new(req.resource.eid()))
            },
        ),
        None,
        schema,
    )
    .map_err(|_| arbitrary::Error::IncorrectFormat)
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let abac_input = abac::FuzzTargetInput::<true>::arbitrary(u)?;
        let schema: cedar_policy::Schema = abac_input
            .schema
            .clone()
            .try_into()
            .map_err(|_| arbitrary::Error::IncorrectFormat)?;
        let partial_requests = abac_input
            .requests
            .iter()
            .map(|req| make_partial_request(req, u, &schema))
            .collect::<arbitrary::Result<Vec<_>>>()?
            .try_into()
            .unwrap();
        let partial_entities =
            entities_to_partial_entities(abac_input.entities.iter(), u, &schema)?;
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

/// helper function that just tells us whether a policyset passes validation
fn passes_policy_validation(validator: &Validator, pset: &PolicySet) -> bool {
    validator
        .validate(pset, cedar_policy::ValidationMode::Strict)
        .validation_passed()
}

fn passes_request_validation(validator: &Validator, request: &Request) -> bool {
    validator
        .schema()
        .as_ref()
        .validate_request(request.as_ref(), Extensions::all_available())
        .is_ok()
}

fn test_weak_equiv(
    residual: &PolicySet,
    e: &PolicySet,
    req: &Request,
    entities: &Entities,
) -> bool {
    debug!("request: {req}");
    debug!("expr: {e}");
    debug!("residual: {residual}");
    let authorizer = Authorizer::new();
    let concrete_res = authorizer.is_authorized(req, e, entities);
    let reeval_res = authorizer.is_authorized(req, residual, entities);
    debug!("concrete evaluation result: {concrete_res:?}");
    debug!("re-evaluation result: {reeval_res:?}");
    concrete_res.decision() == reeval_res.decision()
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.abac_input.schema.schemafile_string();
    if let Ok(schema) = Schema::try_from(input.abac_input.schema) {
        debug!("Schema: {schemafile_string}");
        let validator = Validator::new(schema.clone());
        let mut policyset = PolicySet::new();
        let policy: Policy = input.abac_input.policy.into();
        policyset.add(policy.clone()).unwrap();
        let passes_strict = passes_policy_validation(&validator, &policyset);
        if passes_strict {
            let partial_entities = input.partial_entities;
            for (request, partial_request) in input
                .abac_input
                .requests
                .into_iter()
                .zip(input.partial_requests)
            {
                let request: Request = request.into();
                if passes_request_validation(&validator, &request) {
                    let response = policyset
                        .tpe(&partial_request, &partial_entities, &schema)
                        .expect("tpe failed");
                    assert!(test_weak_equiv(
                        &PolicySet::from_policies(response.residual_policies()).unwrap(),
                        &policyset,
                        &request,
                        &input.abac_input.entities
                    ));
                }
            }
        }
    }
});
