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

use cedar_drt_inner::props::entity_to_json_roundtrips;
use cedar_policy::{
    Entity,
    proto::traits::{DecodeError, Protobuf},
};
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

    // Decode the encoded model into an `Entity`.
    // If it doesn't fail here, then all subsequent steps should not fail.
    let entity = match Entity::decode(&buf[..]) {
        Ok(e) => e,
        Err(DecodeError::Proto(err)) => {
            panic!("Failed to decode proto Entity that was just encoded: {err}")
        }
        Err(_) => return,
    };
    // Once we have an `Entity` it should roundtrip through JSON. We test that validation in the
    // JSON deserialization is not stronger than in Proto decoding.
    entity_to_json_roundtrips(entity);
});
