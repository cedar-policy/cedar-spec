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
    symcc::{RUNTIME, SinglePolicyFuzzTargetInput, local_solver},
};
use cedar_policy::{Authorizer, Decision, PolicySet};
use cedar_policy_symcc::{CedarSymCompiler, CompiledPolicySet, Env, solver::LocalSolver};
use std::{future::Future, sync::LazyLock};
use tokio::{
    sync::{Mutex, MutexGuard},
    time::{Duration, timeout},
};

/// Solver timeout used for this target
const TIMEOUT_DUR: Duration = Duration::from_secs(60);

struct Solver {
    local_solver: CedarSymCompiler<LocalSolver>,
    usage_count: usize,
}

impl Solver {
    const SOLVER_USAGE_LIMIT: usize = 10_000;
}

static SOLVER: LazyLock<Mutex<Solver>> = LazyLock::new(|| {
    Mutex::new(Solver {
        local_solver: CedarSymCompiler::new(local_solver().expect("CVC5 should exist"))
            .expect("solver construction should succeed"),
        usage_count: 0,
    })
});

async fn get_solver() -> MutexGuard<'static, Solver> {
    let mut guard = SOLVER.lock().await;
    guard.usage_count += 1;
    if guard.usage_count >= Solver::SOLVER_USAGE_LIMIT {
        let _ = guard.local_solver.solver_mut().clean_up().await;
        guard.local_solver = CedarSymCompiler::new(local_solver().expect("CVC5 should exist"))
            .expect("solver construction should succeed");
        guard.usage_count = 0;
    }
    guard
}

/// Run the given future (producing `Result<Option<Env>>`), and return the
/// counterexample if one was successfully generated.
///
/// Panics on unexpected errors. Ignores certain expected errors, returning
/// `None`. Also returns `None` if the property holds and there is no
/// counterexample.
async fn get_cex(
    f: impl Future<Output = cedar_policy_symcc::err::Result<Option<Env>>>,
) -> Option<Env> {
    match timeout(TIMEOUT_DUR, f).await {
        Ok(Ok(None)) => None, // successfully executed, no counterexample because the property holds
        Ok(Ok(Some(cex))) => Some(cex),
        Err(err) => panic!(
            "found a slow unit (solver took more than {secs:.2} sec) probably worth investigating: {err}",
            secs = TIMEOUT_DUR.as_secs_f32()
        ),
        Ok(Err(cedar_policy_symcc::err::Error::SolverError(err))) => panic!("solver failed: {err}"),
        Ok(Err(cedar_policy_symcc::err::Error::EncodeError(
            cedar_policy_symcc::err::EncodeError::EncodeStringFailed(_),
        )))
        | Ok(Err(cedar_policy_symcc::err::Error::EncodeError(
            cedar_policy_symcc::err::EncodeError::EncodePatternFailed(_),
        ))) => {
            // Encoding errors are benign -- SMTLIB doesn't support full unicode
            // but our generators generate full unicode
            None
        }
        Ok(Err(err)) => panic!("{err}"), // other errors are unexpected
    }
}

fn reproduce(env: &Env, policies: &PolicySet) -> Decision {
    Authorizer::new()
        .is_authorized(&env.request, policies, &env.entities)
        .decision()
}

// Fuzzing target checking that counterexamples generated are true counterexamples
fuzz_target!(|input: SinglePolicyFuzzTargetInput| {
    initialize_log();
    if let Ok((schema, policyset)) = input.into_inputs_as_pset() {
        for req_env in schema.request_envs() {
            // We let Rust compile the policies as it's faster than Lean.
            // also note that we do the compilation (and reproduction) while _not_ holding the `get_solver()` lock
            if let Ok(cps) = CompiledPolicySet::compile(&policyset, &req_env, &schema) {
                RUNTIME.block_on(async {
                    if let Some(cex) = get_cex(get_solver().await.local_solver.check_always_allows_with_counterexample_opt(&cps)).await {
                        assert_eq!(
                            reproduce(&cex, &policyset),
                            Decision::Deny,
                            "Rust SymCC counterexample for AlwaysAllows was expected to produce Deny but did not"
                        );
                    }
                    if let Some(cex) = get_cex(get_solver().await.local_solver.check_always_denies_with_counterexample_opt(&cps)).await {
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
