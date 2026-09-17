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

//! DRT fuzz target checking that Rust and Lean agree on whether partial entities
//! are valid for a schema.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    tpe::{
        arbitrary_schema_and_entities, entity_to_unchecked_partial_entity,
        schema_and_entities_size_hint, test_partial_entity_validation_equiv,
    },
};

use cedar_lean_ffi::{CedarLeanFfi, UncheckedPartialEntity};
use cedar_policy::Schema;

use cedar_policy_generators::settings::ABACSettings;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// partial entities derived from a generated hierarchy, which is not
    /// necessarily valid for `schema`
    pub entities: Vec<UncheckedPartialEntity>,
}

/// `enable_additional_attributes` makes the generated entities not always valid
const SETTINGS: ABACSettings = ABACSettings {
    enable_additional_attributes: true,
    ..ABACSettings::undirected()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let (schema, entities) = arbitrary_schema_and_entities(SETTINGS.clone(), u)?;
        // `Entities::iter` order is unspecified, so sort to keep this target reproducible
        let mut entities: Vec<_> = entities.iter().collect();
        entities.sort_by_cached_key(|e| e.uid().to_string());
        Ok(Self {
            entities: entities
                .into_iter()
                .map(|e| entity_to_unchecked_partial_entity(e, u))
                .collect::<arbitrary::Result<_>>()?,
            schema,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        schema_and_entities_size_hint(depth)
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let ffi = CedarLeanFfi::new();
    let lean_schema = ffi.load_lean_schema_object(&input.schema).unwrap();
    test_partial_entity_validation_equiv(&ffi, &input.schema, lean_schema, &input.entities);
});
