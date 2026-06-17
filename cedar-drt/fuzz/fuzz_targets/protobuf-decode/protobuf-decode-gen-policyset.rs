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
use cedar_drt_inner::props::policyset_to_cedar_parses;
use cedar_drt_inner::proto_gen::ProtoPolicySetInput;

use cedar_policy::PolicySet;
use cedar_policy::proto::traits::{DecodeError, Protobuf};

use prost::Message;

// This fuzz target checks that the validation of policy sets on the protobuf decode path is the
// same as on the Cedar text parsing path.
//
// Generate a proto PolicySet → encode to bytes → decode → convert to domain →
// print to Cedar text → re-parse.
// Property: if decode+conversion succeeds, printing and re-parsing must also succeed.
fuzz_target!(|input: ProtoPolicySetInput| {
    // Encode the generated proto model to bytes
    let buf = input.policy_set.encode_to_vec();

    // Convert proto model → domain type
    // This is expected to fail
    let policy_set = match PolicySet::decode(&buf[..]) {
        Ok(ps) => ps,
        Err(DecodeError::Proto(err)) => {
            panic!("Decoding an encoded models::PolicySet failed: {err}")
        }
        Err(_) => return,
    };
    // Once we have a PolicySet, printing and parsing it back should succeed.
    // We are testing that validation through the Cedar text parsing path is not stronger than the
    // validation in proto.
    policyset_to_cedar_parses(policy_set);
});
