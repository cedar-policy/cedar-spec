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

use cedar_drt_inner::props::{policyset_to_cedar_parses, policyset_to_json_deserializes};
use cedar_policy::PolicySet;
use cedar_policy::proto::traits::Protobuf;

// Feed arbitrary bytes into PolicySet protobuf decoder.
// The property under test: decode either returns Ok or Err, never panics.
fuzz_target!(|input: &[u8]| {
    match PolicySet::decode(input) {
        Ok(ps) => {
            let _ = policyset_to_cedar_parses(ps.clone());
            let _ = policyset_to_json_deserializes(ps);
        }
        Err(_) => (), // error is fine here
    }
});
