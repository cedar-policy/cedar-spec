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

use cedar_policy::{Entity, EntityUid};
use cedar_policy_core::{
    ast::{self, Value},
    tpe::entities::{PartialEntities, PartialEntity},
};
use libfuzzer_sys::arbitrary::{self, Unstructured};
use ref_cast::RefCast;
use std::collections::{BTreeMap, HashSet};
use std::convert::TryFrom;

pub fn entity_to_partial_entity(
    entity: &Entity,
    u: &mut Unstructured<'_>,
    leafs: &HashSet<EntityUid>,
) -> arbitrary::Result<PartialEntity> {
    let is_action = entity.uid().type_name().as_ref().is_action();
    Ok(PartialEntity {
        uid: entity.as_ref().uid().clone(),
        attrs: if !is_action && u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().attrs().map(
                |(k, v)| (k.clone(), Value::try_from(v.clone()).unwrap()),
            )))
        },
        ancestors: if !is_action && leafs.contains(&entity.uid()) {
            if u.ratio(1, 4)? {
                None
            } else {
                Some(HashSet::from_iter(entity.as_ref().ancestors().cloned()))
            }
        } else {
            Some(HashSet::from_iter(entity.as_ref().ancestors().cloned()))
        },
        tags: if !is_action && u.ratio(1, 4)? {
            None
        } else {
            Some(BTreeMap::from_iter(entity.as_ref().tags().map(|(k, v)| {
                (k.clone(), Value::try_from(v.clone()).unwrap())
            })))
        },
    })
}

/// Constructs a `PartialEntities` given some concrete entities, using `u` to
/// arbitrarily choose some data to delete, making it unknown in subsequent
/// partial evaluation.
pub fn entities_to_partial_entities<'a>(
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
    Ok(
        cedar_policy_core::tpe::entities::PartialEntities::from_entities_unchecked(
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
        )
        .into(),
    )
}
