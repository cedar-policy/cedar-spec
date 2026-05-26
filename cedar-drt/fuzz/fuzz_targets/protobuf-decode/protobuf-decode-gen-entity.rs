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
use cedar_drt_inner::proto_gen::ProtoEntityInput;

use cedar_policy::proto::models;
use cedar_policy::{Entities, Entity};
use prost::Message;

// This tests that validation when decoding protobufs for an entity is the same as validation
// when deserializing from JSON.
//
// Generates a proto Entity → encode to bytes → decode → convert to domain →
// serialize to JSON → re-parse from JSON.
// Property: if decode+conversion succeeds, JSON serialization and re-parsing must also succeed.
fuzz_target!(|input: ProtoEntityInput| {
    // Encode the generated proto model to bytes
    let buf = input.entity.encode_to_vec();

    // Decode from bytes
    let decoded = models::Entity::decode(&buf[..])
        .expect("Failed to decode proto Entity that was just encoded.");

    // Convert proto model → domain type
    // If it doesn't fail here, then all subsequent steps should not fail.
    let entity = match Entity::try_from(decoded) {
        Ok(e) => e,
        Err(_) => return,
    };

    // Wrap in Entities for JSON serialization
    let entities = Entities::from_entities([entity.clone()], None)
        .expect("Failed to create Entities from single entity");

    // Serialize to JSON
    let json = entities.to_json_value().unwrap_or_else(|e| {
        panic!(
            "Entity accepted from proto could not be serialized to JSON.\n\
             Proto input: {:?}\nError: {e}",
            input.entity
        )
    });

    // Re-parse from JSON
    let reparsed = Entities::from_json_value(json.clone(), None).unwrap_or_else(|e| {
        panic!(
            "JSON from proto-accepted entity failed to re-parse.\n\
             Proto input: {:?}\nJSON: {json}\nParse error: {e}",
            input.entity
        )
    });

    // Verify the entity survived
    assert!(
        reparsed.get(&entity.uid()).is_some(),
        "Entity UID {:?} not found after JSON roundtrip.\nProto input: {:?}",
        entity.uid(),
        input.entity
    );
});
