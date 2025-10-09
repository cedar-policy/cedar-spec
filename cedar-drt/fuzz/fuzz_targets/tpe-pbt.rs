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
use cedar_drt_inner::{abac, fuzz_target};
use cedar_policy::{Entities, Entity, EntityUid};
use cedar_policy_core::{
    ast::{self, Expr, Request, RequestSchema, Value},
    evaluator::Evaluator,
    extensions::Extensions,
    tpe::{
        entities::{PartialEntities, PartialEntity},
        is_authorized,
        request::{PartialEntityUID, PartialRequest},
    },
    validator::{CoreSchema, ValidationMode, Validator, ValidatorSchema},
};
use cedar_policy_generators::abac::ABACRequest;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use ref_cast::RefCast;
use std::collections::{BTreeMap, HashMap, HashSet};
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
) -> arbitrary::Result<PartialRequest> {
    Ok(PartialRequest::new_unchecked(
        PartialEntityUID {
            ty: req.principal.entity_type().clone(),
            eid: if u.ratio(1, 4)? {
                None
            } else {
                Some(req.principal.eid().clone())
            },
        },
        PartialEntityUID {
            ty: req.resource.entity_type().clone(),
            eid: if u.ratio(1, 4)? {
                None
            } else {
                Some(req.resource.eid().clone())
            },
        },
        req.action.clone(),
        None,
    ))
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let abac_input = abac::FuzzTargetInput::<true>::arbitrary(u)?;
        let partial_requests = abac_input
            .requests
            .iter()
            .map(|req| make_partial_request(req, u))
            .collect::<arbitrary::Result<Vec<_>>>()?
            .try_into()
            .unwrap();
        let partial_entities = entities_to_partial_entities(abac_input.entities.iter(), u)?;
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
fn passes_policy_validation(validator: &Validator, policyset: &ast::PolicySet) -> bool {
    validator
        .validate(policyset, ValidationMode::Strict)
        .validation_passed()
}

fn passes_request_validation(schema: &ValidatorSchema, request: &ast::Request) -> bool {
    let core_schema = CoreSchema::new(schema);
    core_schema
        .validate_request(request, Extensions::all_available())
        .is_ok()
}

fn entity_to_partial_entity(
    entity: &Entity,
    u: &mut Unstructured<'_>,
    leafs: &HashSet<EntityUid>,
) -> arbitrary::Result<PartialEntity> {
    Ok(PartialEntity {
        uid: entity.as_ref().uid().clone(),
        attrs: if u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().attrs().map(
                |(k, v)| (k.clone(), Value::try_from(v.clone()).unwrap()),
            )))
        },
        ancestors: if leafs.contains(&entity.uid()) {
            if u.ratio(1, 4)? {
                None
            } else {
                Some(HashSet::from_iter(entity.as_ref().ancestors().cloned()))
            }
        } else {
            Some(HashSet::from_iter(entity.as_ref().ancestors().cloned()))
        },
        tags: if u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().tags().map(|(k, v)| {
                (k.clone(), Value::try_from(v.clone()).unwrap())
            })))
        },
    })
}

fn entities_to_partial_entities<'a>(
    entities: impl Iterator<Item = &'a Entity>,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<PartialEntities> {
    let entities: HashSet<Entity> = HashSet::from_iter(entities.cloned());
    let mut leafs: HashSet<_> = entities.iter().map(|e| e.uid().clone()).collect();
    for e in &entities {
        for a in e.as_ref().ancestors() {
            leafs.remove(RefCast::ref_cast(a));
        }
    }
    Ok(PartialEntities::from_entities_unchecked(
        entities
            .iter()
            .map(|e| {
                Ok((
                    e.uid().as_ref().clone(),
                    entity_to_partial_entity(e, u, &leafs)?,
                ))
            })
            .collect::<arbitrary::Result<Vec<(ast::EntityUID, PartialEntity)>>>()?
            .into_iter(),
    ))
}

fn test_weak_equiv(residual: &Expr, e: &Expr, req: &Request, entities: &Entities) -> bool {
    let eval = Evaluator::new(req.clone(), entities.as_ref(), Extensions::all_available());
    let slots = HashMap::new();

    debug!("request: {req}");
    debug!("expr: {e}");
    debug!("residual: {residual}");
    let concrete_res = eval.interpret(e, &slots);
    let reeval_res = eval.interpret(&residual, &slots);
    debug!("concrete evaluation result: {concrete_res:?}");
    debug!("re-evaluation result: {reeval_res:?}");
    concrete_res.ok() == reeval_res.ok()
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.abac_input.schema.schemafile_string();
    if let Ok(schema) = ValidatorSchema::try_from(input.abac_input.schema) {
        debug!("Schema: {schemafile_string}");
        let validator = Validator::new(schema.clone());
        let mut policyset = ast::PolicySet::new();
        let policy: ast::StaticPolicy = input.abac_input.policy.into();
        policyset.add_static(policy.clone()).unwrap();
        let passes_strict = passes_policy_validation(&validator, &policyset);
        if passes_strict {
            for e in input.partial_entities.entities() {
                e.validate(&schema).expect("entities should be valid");
            }
            let mut partial_entities = input.partial_entities;
            partial_entities
                .compute_tc()
                .expect("tc computation failed");
            let expr = policy.condition();
            for (request, partial_request) in input
                .abac_input
                .requests
                .into_iter()
                .zip(input.partial_requests)
            {
                let request: ast::Request = request.into();
                if passes_request_validation(&schema, &request) {
                    let response =
                        is_authorized(&policyset, &partial_request, &partial_entities, &schema)
                            .expect("tpe failed");
                    assert!(test_weak_equiv(
                        &response.residual_policies()[0].condition(),
                        &expr,
                        &request,
                        &input.abac_input.entities
                    ));
                }
            }
        }
    }
});
