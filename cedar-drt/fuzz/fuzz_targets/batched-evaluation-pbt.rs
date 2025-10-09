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

use cedar_policy::{Authorizer, Policy, PolicySet, Schema, TestEntityLoader};

use cedar_policy_core::batched_evaluator::err::BatchedEvalError;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

// This target tests a property that batched evaluation, if succeeds, should
// produce the same authorization decision of normal authorization where the
// the entire in-memory entity store is provided
fuzz_target!(|input: FuzzTargetInput<true>| {
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
            match policyset.is_authorized_batched(&req, &schema, &mut loader, iteration) {
                Ok(batched_decision) => {
                    let authorizer = Authorizer::new();
                    assert_eq!(
                        batched_decision,
                        authorizer
                            .is_authorized(&req, &policyset, &input.entities)
                            .decision()
                    );
                }
                Err(BatchedEvalError::InsufficientIterations(_)) => {
                    panic!("encountered unexpected `InsufficientIterations` error");
                }
                Err(_) => {}
            }
        }
    }
});
