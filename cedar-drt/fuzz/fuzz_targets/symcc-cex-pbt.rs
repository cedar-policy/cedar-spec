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
    symcc::{RUNTIME, SinglePolicyFuzzTargetInput, get_cex, get_solver, reproduce},
};
use cedar_policy::{Authorizer, Decision, PolicySet};
use cedar_policy_symcc::{CedarSymCompiler, CompiledPolicySet, Env, solver::LocalSolver};
use std::{future::Future, sync::LazyLock};
use tokio::{
    sync::{Mutex, MutexGuard},
    time::{Duration, timeout},
};

// Fuzzing target checking that counterexamples generated are true counterexamples
fuzz_target!(|input: SinglePolicyFuzzTargetInput| {
    initialize_log();
    if let Ok((schema, policyset)) = input.into_inputs_as_pset() {
        for req_env in schema.request_envs() {
            // We let Rust compile the policies as it's faster than Lean.
            // also note that we do the compilation (and reproduction) while _not_ holding the `get_solver()` lock
            if let Ok(cps) = CompiledPolicySet::compile(&policyset, &req_env, &schema) {
                RUNTIME.block_on(async {
                    if let Some(cex) = get_cex(get_solver().await.symcc.check_always_allows_with_counterexample_opt(&cps)).await {
                        assert_eq!(
                            reproduce(&cex, &policyset),
                            Decision::Deny,
                            "Rust SymCC counterexample for AlwaysAllows was expected to produce Deny but did not"
                        );
                    }
                    if let Some(cex) = get_cex(get_solver().await.symcc.check_always_denies_with_counterexample_opt(&cps)).await {
                        assert_eq!(
                            reproduce(&cex, &policyset),
                            Decision::Allow,
                            "Rust SymCC counterexample for AlwaysDenies was expected to produce Allow but did not"
                        );
                    }
                });
            }
        }
    }
});
