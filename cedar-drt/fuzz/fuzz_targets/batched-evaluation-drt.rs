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
use cedar_policy::{Schema, TestEntityLoader};
use cedar_policy_core::batched_evaluator::err::BatchedEvalError;

// This target tests a property that batched evaluation, if succeeds, should
// produce the same authorization decision based on the Lean model output
fuzz_target!(|input: FuzzTargetInput<true>| {
    let ffi = CedarLeanFfi::new();
    initialize_log();

    if let Ok(schema) = Schema::try_from(input.schema) {
        let policyset = input.policy.into_policy_set();
        let mut loader = TestEntityLoader::new(&input.entities);
        log::debug!("policy: {policyset}");
        let iteration = (FuzzTargetInput::<true>::settings().max_depth + 1) as u32;

        for req in input.requests {
            let req = req.into();
            log::debug!("req: {req}");
            let rust_decision =
                match policyset.is_authorized_batched(&req, &schema, &mut loader, iteration) {
                    Ok(decision) => Ok(Some(decision)),
                    Err(BatchedEvalError::InsufficientIterations(_)) => Ok(None),
                    Err(e) => Err(e),
                };

            let lean_decision =
                ffi.batched_authorization(&policyset, &schema, &req, &input.entities, iteration);
            match (rust_decision, lean_decision) {
                (Ok(rust_decision), Ok(lean_decision)) => {
                    assert_eq!(rust_decision, lean_decision.decision);
                }
                (Ok(rust_decision), Err(lean_err)) => {
                    panic!("Rust reached decisions {rust_decision:?} but lean errored: {lean_err}")
                }
                (Err(rust_err), Ok(lean_decision)) => {
                    panic!("Lean reached decisions {lean_decision:?} but rust errored: {rust_err}")
                }
                (Err(_), Err(_)) => {}
            }
        }
    }
});
