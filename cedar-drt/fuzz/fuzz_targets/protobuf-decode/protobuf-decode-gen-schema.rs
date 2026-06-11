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
use cedar_drt_inner::props::{schema_to_cedar_parses, schema_to_json_deserializes};
use cedar_drt_inner::proto_gen::ProtoSchemaInput;

use cedar_policy::Schema;
use cedar_policy::proto::models;
use prost::Message;

// Generates a proto Schema → encode to bytes → decode → convert to domain →
// roundtrip through JSON and Cedar text.
fuzz_target!(|input: ProtoSchemaInput| {
    let buf = input.schema.encode_to_vec();

    let decoded = models::Schema::decode(&buf[..])
        .expect("Failed to decode proto Schema that was just encoded.");

    // Convert proto model -> schema. If it doesn't fail here, then the roundtrips through
    // other formats should succeed.
    let schema = match Schema::try_from(decoded) {
        Ok(s) => s,
        Err(_) => return,
    };
    // It should roundtrip through JSON and Cedar formats.
    schema_to_json_deserializes(&schema);
    schema_to_cedar_parses(&schema);
});
