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

//! If we serialize any valid concrete entities to JSON, then the original
//! entities must be consistent with the partial entities obtained from parsing
//! the JSON as partial entities.

#![no_main]
use cedar_drt_inner::roundtrip_entities::assert_entities_to_json;
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};
use cedar_policy::tpe_err::{EntitiesError, EntityValidationError};
use cedar_policy::{Entities, PartialEntities, Schema};
use cedar_policy_core::{entities as core_entities, extensions::Extensions};
use std::convert::TryFrom;

fuzz_target!(|input: FuzzTargetInput<true>| {
    let Ok(schema) = Schema::try_from(input.schema) else {
        return;
    };
    // Serialize only the non-action entities to JSON. Action entities are
    // rejected by the partial-entity parser.
    let non_actions: Entities = core_entities::Entities::from_entities(
        input
            .entities
            .as_ref()
            .iter()
            .filter(|e| !e.uid().is_action())
            .cloned(),
        None::<&core_entities::NoEntitiesSchema>,
        core_entities::TCComputation::AssumeAlreadyComputed,
        &Extensions::all_available(),
    )
    .unwrap()
    .into();
    let Some(json) = assert_entities_to_json(&non_actions) else {
        return;
    };

    // Parsing should succeed, but the generated entities are not always valid
    // against the schema (e.g. enumerated types with invalid eids).
    let partial = match PartialEntities::from_json_value(json, &schema) {
        Ok(partial) => partial,
        Err(EntitiesError::Validation(EntityValidationError::Concrete(_))) => return,
        Err(e) => panic!("parsing concrete entity JSON failed with an unexpected error: {e}"),
    };

    partial.as_ref().check_consistency(input.entities.as_ref()).unwrap_or_else(|e| {
        panic!(
            "Partial entities parsed from concrete entity JSON should be consistent with them: {e}"
        )
    });
});
