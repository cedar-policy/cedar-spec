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
use cedar_drt_inner::roundtrip_entities::pretty_assert_entities_deep_eq;

use cedar_policy::Entities;
use cedar_policy::proto::traits::Protobuf;

// Feed arbitrary bytes into the Entities JSON parser.
// Property: if JSON parsing succeeds, encoding to protobuf must not panic,
// and decoding the encoded bytes must produce equivalent Entities.
fuzz_target!(|input: &[u8]| {
    let Ok(json) = serde_json::from_slice::<serde_json::Value>(input) else {
        return;
    };
    let Ok(entities) = Entities::from_json_value(json, None) else {
        return;
    };
    let buf = entities.encode();
    let decoded =
        Entities::decode(&buf[..]).expect("Failed to decode Entities that were just encoded");
    pretty_assert_entities_deep_eq(&entities, &decoded);
});
