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
    symcc::{PolicySetTask, SinglePolicyFuzzTargetInput, ValidationTask},
};

use cedar_policy::{PolicySet, Schema};

use std::convert::TryFrom;
use std::sync::LazyLock;

static RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
});

fuzz_target!(|input: SinglePolicyFuzzTargetInput| {
    initialize_log();
    let mut policy_set = PolicySet::new();
    policy_set.add(input.policy.into()).unwrap();
    // Attempt to convert the generator schema to an actual schema.
    if let Ok(schema) = Schema::try_from(input.schema) {
        RUNTIME
            .block_on(PolicySetTask::CheckAlwaysAllows.check_ok(schema, policy_set))
            .unwrap();
    }
});
