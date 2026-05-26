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
use cedar_drt_inner::proto_gen;

use cedar_policy::Entities;
use cedar_policy::proto::models;
use prost::Message;

use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

#[derive(Debug, Clone)]
struct ProtoEntitiesInput {
    entities: models::Entities,
}

impl<'a> Arbitrary<'a> for ProtoEntitiesInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let g = proto_gen::ModelGenerator::arbitrary(u)?;
        Ok(Self {
            entities: g.arbitrary_model_entities(u)?,
        })
    }
}

// This fuzz target checks that the validation of entity sets on the protobuf decode path is the
// same as on the JSON parsing path.
//
// Generate a proto Entities → encode to bytes → decode → convert to domain →
// serialize to JSON → re-parse from JSON.
// Property: if decode+conversion succeeds, JSON serialization and re-parsing must also succeed.
fuzz_target!(|input: ProtoEntitiesInput| {
    // Encode the generated proto model to bytes. Should not fail since it is the encoding of
    // a models::Entities.
    let buf = input.entities.encode_to_vec();

    // Decode from bytes.
    let decoded =
        models::Entities::decode(&buf[..]).expect("Decoding an encoded models::Entities failed");

    // Convert proto model → domain type.
    // This is expected to fail for many inputs.
    let entities = match Entities::try_from(decoded) {
        Ok(e) => e,
        Err(_) => return,
    };

    // Serialize to JSON
    let json = entities.to_json_value().unwrap_or_else(|e| {
        panic!(
            "Entities accepted from proto could not be serialized to JSON.\n\
             Proto input: {:?}\nError: {e}",
            input.entities
        )
    });

    // Re-parse from JSON; this shouldn't fail
    let _reparsed = Entities::from_json_value(json.clone(), None).unwrap_or_else(|e| {
        panic!(
            "JSON from proto-accepted entities failed to re-parse.\n\
             Proto input: {:?}\nJSON: {json}\nParse error: {e}",
            input.entities
        )
    });
});
