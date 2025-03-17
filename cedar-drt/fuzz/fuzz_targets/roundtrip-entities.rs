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

use cedar_drt::{
    entities::{EntityJsonParser, NoEntitiesSchema, TCComputation},
    extensions::Extensions,
    Entities, ValidatorSchema,
};
use cedar_policy::{
    conformance_errors::EntitySchemaConformanceError, entities_errors::EntitiesError,
    entities_json_errors::JsonSerializationError,
};
use cedar_policy_generators::{
    hierarchy::HierarchyGenerator, schema::Schema, settings::ABACSettings,
};
use cedar_policy_validator::CoreSchema;
use libfuzzer_sys::{
    arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured},
    fuzz_target,
};
use similar_asserts::assert_eq;

#[derive(Debug)]
struct FuzzTargetInput {
    pub schema: ValidatorSchema,
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
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let entities: Entities = schema
            .arbitrary_hierarchy(u)?
            .try_into()
            .expect("Should be able to get entities from hierarchy.");
        let validator_schema: ValidatorSchema = schema
            .try_into()
            .expect("Should be able to get validator schema from schema.");
        Ok(Self {
            entities,
            schema: validator_schema,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    let json = match input.entities.to_json_value() {
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
            // attribute of type `datetime` and it represents a time before AD
            // 1, which involves calls to `datetime` and `offset`.
            return;
        }
        Err(err) => {
            panic!("Should be able to serialize entities to JSON, instead got error: {err}")
        }
    };

    let eparser: EntityJsonParser<'_, '_, NoEntitiesSchema> = EntityJsonParser::new(
        None,
        Extensions::all_available(),
        TCComputation::EnforceAlreadyComputed,
    );
    let roundtripped_entities = eparser
        .from_json_value(json.clone())
        .expect("Should be able to parse serialized entity JSON");
    assert_eq!(input.entities, roundtripped_entities);

    let core_schema = CoreSchema::new(&input.schema);
    let eparser: EntityJsonParser<'_, '_, _> = EntityJsonParser::new(
        Some(&core_schema),
        Extensions::all_available(),
        TCComputation::EnforceAlreadyComputed,
    );
    // The entity store generator currently produces entities of enumerated entity types but with invalid EIDs,
    // which are rejected by entity validation
    match eparser.from_json_value(json.clone()) {
        Ok(roundtripped_entities) => {
            // Weaker assertion for schema based parsing because it adds actions from the schema into entities.
            for e in input.entities {
                let roundtripped_e = roundtripped_entities
                    .entity(e.uid())
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
