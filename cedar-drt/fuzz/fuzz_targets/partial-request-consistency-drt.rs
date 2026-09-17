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

//! DRT fuzz target checking that Rust and Lean agree on whether a partial request is
//! consistent with a concrete request.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    tpe::{
        arbitrary_schema_and_requests, make_partial_request, schema_and_requests_size_hint,
        test_partial_request_consistency_equiv,
    },
};

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{PartialRequest, Request};

use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// partial requests derived from generated requests
    pub partial_requests: Vec<PartialRequest>,
    /// those requests, optionally rotated so that both consistent and inconsistent
    /// pairings are reachable
    pub requests: Vec<Request>,
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let (schema, generated_requests) = arbitrary_schema_and_requests(u)?;
        let partial_requests = generated_requests
            .iter()
            .map(|req| make_partial_request(req, u, &schema))
            .collect::<Result<Vec<_>, _>>()?;
        let mut requests: Vec<Request> = generated_requests.into_iter().map(Into::into).collect();
        if u.arbitrary()? {
            // pair each partial request with a different concrete request, so that they can be inconsistent
            requests.rotate_left(1);
        }
        Ok(Self {
            partial_requests,
            requests,
        })
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
    for (request, partial_request) in input.requests.iter().zip(&input.partial_requests) {
        test_partial_request_consistency_equiv(&ffi, request, partial_request);
    }
});
