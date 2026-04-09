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
use cedar_drt_inner::{fuzz_target, pst_equiv, pst_gen::PolicySetFuzzTargetInput};

use cedar_policy::PolicySet;
use log::debug;

// PST PolicySet -> from_pst -> to_json -> from_json -> to_pst -> compare
// Tests round-tripping through JSON, with policy/template and link management.
fuzz_target!(|input: PolicySetFuzzTargetInput| {
    initialize_log();
    let pst_set = input.policy_set;

    debug!("Running PST PolicySet roundtrip on: {:?}", pst_set);

    // PST into public PolicySet using from_pst
    let policy_set = PolicySet::from_pst(pst_set.clone())
        .unwrap_or_else(|e| panic!("Failed to create PolicySet from PST.\nError: {:?}", e));

    // PolicySet -> JSON
    let policy_set_json = policy_set
        .to_json()
        .unwrap_or_else(|e| panic!("Failed to get JSON from PolicySet:\nError: {:?}", e));
    // JSON -> PolicySet
    let policy_set_2 = PolicySet::from_json_value(policy_set_json)
        .unwrap_or_else(|e| panic!("Failed to get PolicySet from JSON:\nError: {:?}", e));
    // PolicySet -> PST
    let pst_set_2 = policy_set_2
        .to_pst()
        .unwrap_or_else(|e| panic!("to_pst failed: {:?}", e));
    pst_equiv::check_policy_set_equivalence(
        &pst_set,
        &pst_set_2,
        pst_equiv::CheckingParams { check_ids: true },
    );
});
