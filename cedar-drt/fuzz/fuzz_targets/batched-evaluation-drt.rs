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
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Policy, PolicySet, Schema, TestEntityLoader};

// This target tests a property that batched evaluation, if succeeds, should
// produce the same authorization decision based on the Lean model output
fuzz_target!(|input: FuzzTargetInput<true>| {
    let ffi = CedarLeanFfi::new();
    initialize_log();

    if let Ok(schema) = Schema::try_from(input.schema) {
        let policy = Policy::from(input.policy);
        let mut policyset = PolicySet::new();
        policyset.add(policy.clone()).unwrap();
        let mut loader = TestEntityLoader::new(&input.entities);
        log::debug!("policy: {policyset}");
        let iteration = (FuzzTargetInput::<true>::settings().max_depth + 1) as u32;

        for req in input.requests {
            let req = req.into();
            log::debug!("req: {req}");
            // We need to start with an `Ok` result of Rust because the
            // validation DRT property is if Rust validations, then Lean also
            // does. `is_authorized_batched` validates policies/request/entities
            if let Ok(rust_decision) =
                policyset.is_authorized_batched(&req, &schema, &mut loader, iteration)
            {
                match ffi.batched_evaluation(&policy, &schema, &req, &input.entities, iteration) {
                    Ok(lean_decision) => {
                        assert_eq!(lean_decision, Some(rust_decision));
                    }
                    Err(err) => {
                        panic!("lean failed but rust didn't: {err}");
                    }
                }
            }
        }
    }
});
