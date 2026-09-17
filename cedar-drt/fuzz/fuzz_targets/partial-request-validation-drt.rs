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

//! DRT fuzz target checking that Rust and Lean agree on whether a partial request
//! is valid for a schema.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    tpe::{
        arbitrary_schema_and_requests, make_unchecked_partial_request,
        schema_and_requests_size_hint, test_partial_request_validation_equiv,
    },
};

use cedar_lean_ffi::{CedarLeanFfi, UncheckedPartialRequest};
use cedar_policy::Schema;

use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: Schema,
    /// partial requests built by mixing components of generated requests, so they are
    /// not necessarily valid for `schema`
    pub requests: Vec<UncheckedPartialRequest>,
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let (schema, requests) = arbitrary_schema_and_requests(u)?;
        let requests = if u.arbitrary()? {
            // take the action and context from the next request, so that they are likely invalid
            requests
                .iter()
                .zip(requests.iter().cycle().skip(1))
                .map(|(req, action_from)| make_unchecked_partial_request(req, action_from, u))
                .collect::<arbitrary::Result<_>>()?
        } else {
            requests
                .iter()
                .map(|req| make_unchecked_partial_request(req, req, u))
                .collect::<arbitrary::Result<_>>()?
        };
        Ok(Self { schema, requests })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        schema_and_requests_size_hint(depth)
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let ffi = CedarLeanFfi::new();
    let lean_schema = ffi.load_lean_schema_object(&input.schema).unwrap();
    for request in &input.requests {
        test_partial_request_validation_equiv(&ffi, &input.schema, lean_schema.clone(), request);
    }
});
