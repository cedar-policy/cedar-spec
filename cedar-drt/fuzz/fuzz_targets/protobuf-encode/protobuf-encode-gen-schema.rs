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
use cedar_drt_inner::props::schema_protobuf_decodes;

use cedar_policy::Schema;
use cedar_policy::proto::traits::{EncodeError, Protobuf};

use cedar_policy_generators::{schema, settings::ABACSettings};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

#[derive(Debug, Clone)]
struct FuzzTargetInput {
    schema: Schema,
}

const SETTINGS: ABACSettings = ABACSettings {
    enable_arbitrary_func_call: false,
    ..ABACSettings::undirected()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let schema = schema
            .try_into()
            .expect("Failed to convert schema to ValidatorSchema");
        Ok(Self { schema })
    }

    fn try_size_hint(
        depth: usize,
    ) -> Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        schema::Schema::arbitrary_size_hint(depth)
    }
}

// Generate a Schema using the ABAC generators, then encode to protobuf.
// Property: encoding a well-formed Schema must not panic, and decoding
// the result must produce an equivalent Schema.
fuzz_target!(|input: FuzzTargetInput| {
    let buf = match input.schema.encode() {
        Ok(buf) => buf,
        Err(EncodeError::MaxDepthExceeded) => return,
        Err(e) => panic!("only error expected encoding Schema is MaxDepthExceeded, got {e}"),
    };
    schema_protobuf_decodes(&buf[..], &input.schema);
});
