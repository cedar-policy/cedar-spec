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
use cedar_drt_inner::{
    fuzz_target,
    symcc::{PolicyTask, RUNTIME, SinglePolicyFuzzTargetInput, ValidationTask},
};

fuzz_target!(|input: SinglePolicyFuzzTargetInput| {
    initialize_log();
    // Attempt to convert the generator schema to an actual schema.
    if let Ok((schema, policy)) = input.into_inputs() {
        RUNTIME
            .block_on(PolicyTask::CheckNeverErrors.check_ok(schema, policy))
            .unwrap();
    }
});
