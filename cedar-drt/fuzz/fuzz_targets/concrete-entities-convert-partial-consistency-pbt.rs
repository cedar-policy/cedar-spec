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

//! All valid concrete entities must be consistent with themselves converted to
//! partial entities with [`PartialEntities::from_concrete`].

#![no_main]
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};
use cedar_policy::{
    PartialEntities, Schema,
    tpe_err::{EntitiesError, EntityValidationError},
};
use std::convert::TryFrom;

fuzz_target!(|input: FuzzTargetInput<true>| {
    let Ok(schema) = Schema::try_from(input.schema) else {
        return;
    };
    // Converting to partial entities should succeed, but here the entities aren't always valid.
    let partial = match PartialEntities::from_concrete(input.entities.clone(), &schema) {
        Ok(partial) => partial,
        Err(EntitiesError::Validation(EntityValidationError::Concrete(_))) => return,
        Err(e) => {
            panic!("from_concrete failed on concrete entities with an unexpected error: {e}")
        }
    };

    partial.as_ref().check_consistency(input.entities.as_ref()).unwrap_or_else(|e| {
        panic!(
            "Partial entities derived from concrete entities should be consistent with them: {e}"
        )
    });
});
