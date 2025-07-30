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

use cedar_policy::{Entities, Schema};

use cedar_policy::{
    conformance_errors::EntitySchemaConformanceError, entities_errors::EntitiesError,
    entities_json_errors::JsonSerializationError,
};
use itertools::Itertools;

pub fn pretty_assert_entities_deep_eq(original: &Entities, roundtripped: &Entities) {
    if !original.deep_eq(roundtripped) {
        // Sort for usefull diff. `Entities` is backed by a `HashMap`
        let original = original.iter().sorted_by_key(|e| e.uid()).collect_vec();
        let roundtripped = roundtripped.iter().sorted_by_key(|e| e.uid()).collect_vec();
        panic!(
            "{}",
            similar_asserts::SimpleDiff::from_str(
                &format!("{original:#?}"),
                &format!("{roundtripped:#?}"),
                "original",
                "roundtripped",
            )
        );
    }
}

pub fn fuzz_target(entities: Entities, schema: Option<Schema>) {
    let json = match entities.as_ref().to_json_value() {
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
    pretty_assert_entities_deep_eq(&entities, &roundtripped_entities);

    // Also check schema-based roundtrip
    if let Some(schema) = schema {
        // The entity store generator currently produces entities of enumerated entity types but with invalid EIDs,
        // which are rejected by entity validation
        match Entities::from_json_value(json.clone(), Some(&schema)) {
            Ok(roundtripped_entities) => {
                // Weaker assertion for schema based parsing because it adds actions from the schema into entities.
                for e in entities {
                    let roundtripped_e = roundtripped_entities
                        .get(&e.uid())
                        .expect("Schema-based roundtrip dropped entity");
                    if !e.deep_eq(&roundtripped_e) {
                        panic!(
                            "{}",
                            similar_asserts::SimpleDiff::from_str(
                                &format!("{e:#?}"),
                                &format!("{roundtripped_e:#?}"),
                                "original",
                                "roundtripped",
                            )
                        );
                    }
                }
            }
            Err(err) => {
                // The error should only be `InvalidEnumEntity`
                assert!(matches!(
                    err,
                    EntitiesError::InvalidEntity(EntitySchemaConformanceError::InvalidEnumEntity(
                        _
                    ))
                ));
            }
        }
    }
}
