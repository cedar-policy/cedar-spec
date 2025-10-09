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
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};

use cedar_policy::{PolicySet, PrincipalQueryRequest, Request, Validator};

use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};
use std::{collections::BTreeSet, convert::TryFrom};

fuzz_target!(|input: FuzzTargetInput<true>| {
    let mut policyset = PolicySet::new();
    policyset.add(input.policy.into()).unwrap();
    let cedar_schema = cedar_policy::Schema::try_from(input.schema.clone()).unwrap();

    let validator = Validator::new(cedar_schema);
    if !validator
        .validate(&policyset, cedar_policy::ValidationMode::Strict)
        .validation_passed()
    {
        // Even with type-directed generation, policies might not be well typed.
        // This would cause `query_principal` to return an error.
        return;
    }

    let auth = cedar_policy::Authorizer::new();
    for request in input.requests {
        let request: cedar_policy::Request = request.into();
        let principal_request = PrincipalQueryRequest::new(
            request.principal().unwrap().type_name().clone(),
            request.action().unwrap().clone(),
            request.resource().unwrap().clone(),
            request.context().unwrap().clone(),
            validator.schema(),
        )
        .unwrap();

        let principals: BTreeSet<_> = policyset
            .query_principal(&principal_request, &input.entities, validator.schema())
            .unwrap()
            .collect();

        // Every principal returned by the query has the requested type and is allowed.
        for p in &principals {
            assert_eq!(
                p.type_name(),
                request.principal().unwrap().type_name(),
                "All principals returned by query should have requested type"
            );
            let request = Request::new(
                p.clone(),
                request.action().unwrap().clone(),
                request.resource().unwrap().clone(),
                request.context().unwrap().clone(),
                None,
            )
            .unwrap();
            let resp = auth.is_authorized(&request, &policyset, &input.entities);
            assert_eq!(
                resp.decision(),
                cedar_policy::Decision::Allow,
                "All principals returned by query should be allowed\n{request:#?}"
            );
        }

        // Every entity having the requestesd type but not returned by the query is denied.
        for e in input.entities.iter().map(|e| e.uid()).filter(|e| {
            e.type_name() == request.principal().unwrap().type_name() && !principals.contains(e)
        }) {
            let request = Request::new(
                e,
                request.action().unwrap().clone(),
                request.resource().unwrap().clone(),
                request.context().unwrap().clone(),
                None,
            )
            .unwrap();
            let resp = auth.is_authorized(&request, &policyset, &input.entities);
            assert_eq!(
                resp.decision(),
                cedar_policy::Decision::Deny,
                "All entities having requested type but not returned by query should be denied\n{request:#?}"
            );
        }
    }
});
