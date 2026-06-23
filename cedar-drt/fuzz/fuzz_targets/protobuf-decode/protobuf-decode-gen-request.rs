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
use cedar_drt_inner::proto_gen::ProtoRequestInput;

use cedar_drt_inner::props::request_context_to_cedar_parses;
use cedar_policy::Request;
use cedar_policy::proto::traits::{DecodeError, Protobuf};
use prost::Message;

// This tests that validation when decoding protobufs for a request is the same as validation
// when parsing Cedar restricted expressions.
//
// Generates a proto Request → encode to bytes → decode → convert to domain →
// print context values to Cedar → re-parse from Cedar.
// Property: if decode+conversion succeeds, Cedar printing and re-parsing of context values
// must also succeed.
fuzz_target!(|input: ProtoRequestInput| {
    // Encode the generated proto model to bytes
    let buf = input.request.encode_to_vec();

    // Decode the encoded `Request`.
    // If it doesn't fail here, then all subsequent steps should not fail.
    let request = match Request::decode(&buf[..]) {
        Ok(r) => r,
        Err(DecodeError::Proto(err)) => {
            panic!("Decoding an encoded models::Request failed: {err}.")
        }
        Err(_) => return,
    };
    // Once we have a `Request`, its context values should roundtrip through Cedar text.
    // We test that validation when parsing Cedar is not stronger than when decoding Protobuf.
    request_context_to_cedar_parses(request);
});
