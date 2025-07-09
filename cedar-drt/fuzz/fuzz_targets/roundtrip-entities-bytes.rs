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
use cedar_drt::fuzz_target;

use cedar_policy::Entities;

use cedar_policy::{entities_errors::EntitiesError, entities_json_errors::JsonSerializationError};
use similar_asserts::assert_eq;

fuzz_target!(|input: String| {
    let Ok(entities) = Entities::from_json_str(&input, None) else {
        return;
    };
    let json = match entities.as_ref().to_json_value() {
        Ok(json) => json,
        Err(EntitiesError::Serialization(JsonSerializationError::ReservedKey(_))) => {
            // Serializing to JSON is expected to fail when there's a record
            // attribute `__entity`, `__expr`, or `__extn`
            return;
        }
        _ => panic!("Should be able to serialize entities to JSON"),
    };
    let rountripped =
        Entities::from_json_value(json, None).expect("Should parse serialized entities JSON");
    assert_eq!(entities, rountripped);
});
