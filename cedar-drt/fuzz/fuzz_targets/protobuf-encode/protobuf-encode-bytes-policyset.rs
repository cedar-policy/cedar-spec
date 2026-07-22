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
use cedar_drt_inner::props::policyset_protobuf_decodes;

use cedar_policy::PolicySet;
use cedar_policy::proto::traits::{EncodeError, Protobuf};

// Feed arbitrary strings into the Cedar policy parser.
// Property: if parsing succeeds, encoding to protobuf must not panic,
// and decoding the encoded bytes must produce an equivalent PolicySet.
fuzz_target!(|input: String| {
    let Ok(policy_set) = input.parse::<PolicySet>() else {
        return;
    };
    let buf = match policy_set.encode() {
        Ok(buf) => buf,
        Err(EncodeError::MaxDepthExceeded) => return,
        Err(e) => panic!("only error expected encoding PolicySet is MaxDepthExceeded, got {e}"),
    };
    policyset_protobuf_decodes(&buf[..], &policy_set);
});
