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
use cedar_drt::{
    dump::dump,
    logger::{initialize_log, TOTAL_MSG},
    tests::run_auth_test,
};

use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Authorizer, Policy, PolicyId, PolicySet, Request, SchemaFragment};

use cedar_testing::cedar_test_impl::time_function;

use log::{debug, info};
use std::convert::TryFrom;

// Simple fuzzing of ABAC hierarchy/policy/requests without respect to types.
fuzz_target!(|input: FuzzTargetInput<false>| {
    initialize_log();
    let mut policyset = PolicySet::new();
    let policy = Policy::from(input.policy);
    policyset.add(policy.clone()).unwrap();
    debug!("Policies: {policyset}");
    debug!("Entities: {}", input.entities.as_ref());
    let requests = input
        .requests
        .into_iter()
        .map(Request::from)
        .collect::<Vec<_>>();

    let lean_engine = CedarLeanFfi::new();

    for request in requests.iter() {
        debug!("Request: {request}");
        let (_, total_dur) =
            time_function(|| run_auth_test(&lean_engine, request, &policyset, &input.entities));
        info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
    }
    if let Ok(test_name) = std::env::var("DUMP_TEST_NAME") {
        // When the corpus is re-parsed, the policy will be given id "policy0".
        // Recreate the policy set and compute responses here to account for this.
        let mut policyset = PolicySet::new();
        let policy = policy.new_id(PolicyId::new("policy0"));
        policyset.add(policy).unwrap();
        let responses = requests
            .iter()
            .map(|request| {
                let authorizer = Authorizer::new();
                authorizer.is_authorized(request, &policyset, &input.entities)
            })
            .collect::<Vec<_>>();
        let dump_dir = std::env::var("DUMP_TEST_DIR").unwrap_or_else(|_| ".".to_string());
        dump(
            dump_dir,
            &test_name,
            &SchemaFragment::try_from(input.schema).unwrap(),
            &policyset,
            &input.entities,
            std::iter::zip(requests, responses),
        )
        .expect("failed to dump test case");
    }
});
