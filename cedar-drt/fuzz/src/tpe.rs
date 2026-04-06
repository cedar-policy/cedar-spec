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

//! Test utilities for type-directed partial evaluation fuzz targets

use cedar_policy::{
    Entity, EntityId, EntityUid, PartialEntities, PartialEntity, PartialEntityUid, PartialRequest,
    PolicySet, Request, Schema, Validator,
};
use cedar_policy_core::ast::{self, Value};
use cedar_policy_generators::abac::ABACRequest;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use ref_cast::RefCast;
use std::collections::{BTreeMap, HashSet};
use std::convert::TryFrom;

use crate::abac;

fn entity_to_partial_entity(
    entity: &Entity,
    u: &mut Unstructured<'_>,
    leafs: &HashSet<EntityUid>,
    schema: &Schema,
) -> arbitrary::Result<PartialEntity> {
    let is_action = entity.uid().type_name().as_ref().is_action();
    PartialEntity::new(
        entity.as_ref().uid().clone().into(),
        if !is_action && u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().attrs().map(
                |(k, v)| {
                    (
                        k.clone(),
                        ast::RestrictedExpr::from(Value::try_from(v.clone()).unwrap()).into(),
                    )
                },
            )))
        },
        // We can only mark ancestors of leaf nodes to unknown
        if !is_action && leafs.contains(&entity.uid()) {
            if u.ratio(1, 4)? {
                None
            } else {
                Some(HashSet::from_iter(
                    entity.as_ref().ancestors().cloned().map(Into::into),
                ))
            }
        } else {
            Some(HashSet::from_iter(
                entity.as_ref().ancestors().cloned().map(Into::into),
            ))
        },
        if !is_action && u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().tags().map(|(k, v)| {
                (
                    k.clone(),
                    ast::RestrictedExpr::from(Value::try_from(v.clone()).unwrap()).into(),
                )
            })))
        },
        schema,
    )
    .map_err(|_| arbitrary::Error::IncorrectFormat)
}

/// Constructs a `PartialEntities` given some concrete entities, using `u` to
/// arbitrarily choose some data to delete, making it unknown in subsequent
/// partial evaluation.
pub fn entities_to_partial_entities<'a>(
    entities: impl Iterator<Item = &'a Entity>,
    u: &mut Unstructured<'_>,
    schema: &Schema,
) -> arbitrary::Result<PartialEntities> {
    let entities: HashSet<Entity> = HashSet::from_iter(entities.cloned());
    let mut leafs: HashSet<_> = entities.iter().map(|e| e.uid().clone()).collect();
    for e in &entities {
        for a in e.as_ref().ancestors() {
            leafs.remove(RefCast::ref_cast(a));
        }
    }
    PartialEntities::from_partial_entities(
        entities
            .iter()
            .map(|e| entity_to_partial_entity(e, u, &leafs, schema))
            .collect::<arbitrary::Result<Vec<PartialEntity>>>()?,
        schema,
    )
    .map_err(|_| arbitrary::Error::IncorrectFormat)
}

/// Input for TPE fuzz targets: an ABAC hierarchy, schema, and 8 associated partial requests.
#[derive(Debug, Clone)]
pub struct TpeFuzzTargetInput {
    pub abac_input: abac::FuzzTargetInput<true>,
    pub partial_requests: [PartialRequest; 8],
    pub partial_entities: PartialEntities,
}

/// Construct a partial request from a concrete request, randomly dropping eids.
pub fn make_partial_request(
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

impl<'a> Arbitrary<'a> for TpeFuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let abac_input = abac::FuzzTargetInput::<true>::arbitrary(u)?;
        let schema: Schema = abac_input
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

/// Whether a policyset passes strict validation.
pub fn passes_validation(validator: &Validator, pset: &PolicySet) -> bool {
    validator
        .validate(pset, cedar_policy::ValidationMode::Strict)
        .validation_passed()
}

/// Whether a request passes validation against the validator's schema.
pub fn passes_request_validation(validator: &Validator, request: &Request) -> bool {
    Request::new(
        request.principal().unwrap().clone(),
        request.action().unwrap().clone(),
        request.resource().unwrap().clone(),
        request.context().unwrap().clone(),
        Some(validator.schema()),
    )
    .is_ok()
}
