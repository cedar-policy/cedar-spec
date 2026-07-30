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

//! Differential testing that the Rust and Lean validators compute the same
//! typed expression for each (policy, environment) pair (issue #840).

use cedar_drt::logger::initialize_log;
use cedar_drt_inner::typed_expr::{TypedExprInput, compare_typed_expressions};
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};
use cedar_lean_ffi::CedarLeanFfi;
use std::sync::LazyLock;

static FFI: LazyLock<CedarLeanFfi> = LazyLock::new(CedarLeanFfi::new);

fuzz_target!(|input: FuzzTargetInput<true>| {
    initialize_log();

    let policyset = input.policy.clone().into_policy_set();
    let Some(tei) = TypedExprInput::new(input.schema.clone(), policyset) else {
        return;
    };

    let Some(report) = compare_typed_expressions(&FFI, &tei) else {
        return;
    };

    let findings = report.findings();

    if findings.is_empty() {
        return;
    }

    panic!(
        "typed expression mismatch over {} (policy, env) pairs:\n{}",
        report.compared,
        findings
            .iter()
            .map(|f| format!("  [{}] {f:?}", f.bucket()))
            .collect::<Vec<_>>()
            .join("\n")
    );
});
