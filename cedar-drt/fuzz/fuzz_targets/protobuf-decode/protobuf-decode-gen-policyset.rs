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
use cedar_drt_inner::proto_gen::ProtoPolicySetInput;

use cedar_policy::PolicySet;
use cedar_policy::proto::models;
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

    // Decode from bytes (as a real client would). Should not fail since it is the encoding of
    // a models::PolicySet.
    let decoded =
        models::PolicySet::decode(&buf[..]).expect("Decoding an encoded models::PolicySet failed");

    // Convert proto model → domain type
    // This is expected to fail
    let policy_set = match PolicySet::try_from(decoded) {
        Ok(ps) => ps,
        Err(_) => return,
    };

    // Print the whole policy set to Cedar text
    let cedar_text = policy_set.to_cedar().unwrap_or_else(|| {
        panic!(
            "PolicySet accepted from proto could not be printed to Cedar.\n\
             Proto input: {:?}",
            input.policy_set
        )
    });

    // Re-parse the Cedar text; this should succeed
    let _: PolicySet = cedar_text.parse().unwrap_or_else(|e| {
        panic!(
            "Cedar text from proto-accepted PolicySet failed to re-parse.\n\
             Proto input: {:?}\nCedar text: {cedar_text}\nParse error: {e}",
            input.policy_set
        )
    });
});
