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

use cedar_drt_inner::fuzz_target;

use cedar_policy::{Entities, Schema};

use cedar_policy::{
    conformance_errors::EntitySchemaConformanceError, entities_errors::EntitiesError,
    entities_json_errors::JsonSerializationError,
};
use cedar_policy_generators::{hierarchy::HierarchyGenerator, schema, settings::ABACSettings};
use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use similar_asserts::assert_eq;

#[derive(Debug)]
struct FuzzTargetInput {
    pub schema: Schema,
    pub entities: Entities,
}

const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 10,
    max_width: 10,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let entities: Entities = schema
            .arbitrary_hierarchy(u)?
            .try_into()
            .expect("Should be able to get entities from hierarchy.");
        let schema =
            Schema::try_from(schema).expect("Should be able to get validator schema from schema.");
        Ok(Self { entities, schema })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    let json = match input.entities.as_ref().to_json_value() {
        Ok(json) => json,
        Err(EntitiesError::Serialization(JsonSerializationError::ReservedKey(_))) => {
            // Serializing to JSON is expected to fail when there's a record
            // attribute `__entity`, `__expr`, or `__extn`
            return;
        }
        Err(EntitiesError::Serialization(JsonSerializationError::ExtnCall2OrMoreArguments(
            err,
        ))) if err.to_string().contains("offset") => {
            // Serializing to JSON is expected to fail when there's a record
            // attribute of type `datetime`, which involves calls to `offset`.
            // This is because years before AD 1 cannot be constructed using the
            // `datetime` function, of which the valid inputs span from AD 1 to
            // year 9999.
            return;
        }
        Err(err) => {
            panic!("Should be able to serialize entities to JSON, instead got error: {err}")
        }
    };

    let roundtripped_entities = Entities::from_json_value(json.clone(), None)
        .expect("Should be able to parse serialized entity JSON");

    assert_eq!(input.entities, roundtripped_entities);

    // The entity store generator currently produces entities of enumerated entity types but with invalid EIDs,
    // which are rejected by entity validation
    match Entities::from_json_value(json.clone(), Some(&input.schema)) {
        Ok(roundtripped_entities) => {
            // Weaker assertion for schema based parsing because it adds actions from the schema into entities.
            for e in input.entities {
                let roundtripped_e = roundtripped_entities
                    .get(&e.uid())
                    .expect("Schema-based roundtrip dropped entity");
                assert_eq!(&e, roundtripped_e);
            }
        }
        Err(err) => {
            // The error should only be `InvalidEnumEntity`
            assert!(matches!(
                err,
                EntitiesError::InvalidEntity(EntitySchemaConformanceError::InvalidEnumEntity(_))
            ));
        }
    }
});
