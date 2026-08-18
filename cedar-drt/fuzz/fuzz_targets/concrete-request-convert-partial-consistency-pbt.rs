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

//! All valid concrete requests must be consistent with themselves converted to
//! a partial request with .

#![no_main]
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};
use cedar_policy::{
    PartialEntityUid, PartialRequest, PartialRequestCreationError, Request, Schema,
};
use std::convert::TryFrom;

fuzz_target!(|input: FuzzTargetInput<true>| {
    let Ok(schema) = Schema::try_from(input.schema) else {
        return;
    };

    for req in input.requests {
        let request: Request = req.into();
        // A concrete request always has known components; unwrap them to build a
        // fully-concrete partial request.
        let (Some(principal), Some(action), Some(resource), Some(context)) = (
            request.principal(),
            request.action(),
            request.resource(),
            request.context(),
        ) else {
            panic!("concrete request unexpectedly has an unknown component: {request}");
        };

        // Constructing the partial request should succeed, but here the request isn't always valid.
        let partial = match PartialRequest::new(
            PartialEntityUid::from_concrete(principal.clone()),
            action.clone(),
            PartialEntityUid::from_concrete(resource.clone()),
            Some(context.clone()),
            &schema,
        ) {
            Ok(partial) => partial,
            Err(PartialRequestCreationError::Validation(_)) => continue,
            Err(e) => {
                panic!(
                    "PartialRequest::new failed on a concrete request with an unexpected error: {e}"
                )
            }
        };

        partial.as_ref().check_consistency(request.as_ref()).unwrap_or_else(|e| {
            panic!(
                "Partial request derived from a concrete request should be consistent with it: {e}"
            )
        });
    }
});
