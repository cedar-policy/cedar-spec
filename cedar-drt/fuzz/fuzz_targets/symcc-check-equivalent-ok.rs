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
    symcc::{PolicySetPair, PolicySetPairTask, RUNTIME, TwoPolicyFuzzTargetInput, ValidationTask},
};

fuzz_target!(|input: TwoPolicyFuzzTargetInput<128>| {
    initialize_log();
    if let Ok((schema, pset1, pset2)) = input.into_inputs_as_psets() {
        RUNTIME
            .block_on(
                PolicySetPairTask::CheckEquivalent.check_ok(schema, PolicySetPair { pset1, pset2 }),
            )
            .unwrap();
    }
});
