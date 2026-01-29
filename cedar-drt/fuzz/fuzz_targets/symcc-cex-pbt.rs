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
use cedar_policy_symcc::{
    CedarSymCompiler, CompiledPolicySet, Env, WellFormedAsserts, always_allows_asserts,
    always_denies_asserts, err::SolverError, solver::LocalSolver,
};

use std::sync::LazyLock;
use tokio::{
    sync::{Mutex, MutexGuard},
    time::{Duration, error::Elapsed, timeout},
};

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

#[derive(Debug)]
enum CexError {
    Solver(SolverError),
    Timeout(Elapsed),
    Other(String),
}

fn get_cex(
    always_allows_asserts: &WellFormedAsserts<'_>,
    always_denies_asserts: &WellFormedAsserts<'_>,
) -> Result<(Option<Env>, Option<Env>), CexError> {
    // TODO: wrap a single run in a function
    RUNTIME.block_on(async {
        let always_allow_result = timeout(
            Duration::from_secs(60),
            get_solver()
                .await
                .local_solver
                .check_sat(always_allows_asserts),
        )
        .await;

        let always_allow_result = match always_allow_result {
            // Propagate any solver errors because we shouldn't continue running
            // the solver if it errors
            Ok(Err(cedar_policy_symcc::err::Error::SolverError(err))) => Err(CexError::Solver(err)),
            // Encoding errors are benign -- SMTLIB doesn't support full unicode
            // but our generators generate full unicode
            Ok(Err(cedar_policy_symcc::err::Error::EncodeError(
                cedar_policy_symcc::err::EncodeError::EncodeStringFailed(_),
            )))
            | Ok(Err(cedar_policy_symcc::err::Error::EncodeError(
                cedar_policy_symcc::err::EncodeError::EncodePatternFailed(_),
            ))) => Ok(None),
            // Propagate any other errors
            Ok(Err(err)) => Err(CexError::Other(err.to_string())),
            Ok(Ok(env)) => Ok(env),
            // If timed out, propagate this error because we now have a
            // long-running solver and should not continue sending scripts
            Err(err) => Err(CexError::Timeout(err)),
        }?;

        let always_deny_result = timeout(
            Duration::from_secs(60),
            get_solver()
                .await
                .local_solver
                .check_sat(always_denies_asserts),
        )
        .await;

        let always_deny_result = match always_deny_result {
            Ok(Err(cedar_policy_symcc::err::Error::SolverError(err))) => Err(CexError::Solver(err)),
            Ok(Err(cedar_policy_symcc::err::Error::EncodeError(
                cedar_policy_symcc::err::EncodeError::EncodeStringFailed(_),
            )))
            | Ok(Err(cedar_policy_symcc::err::Error::EncodeError(
                cedar_policy_symcc::err::EncodeError::EncodePatternFailed(_),
            ))) => Ok(None),
            Ok(Err(err)) => Err(CexError::Other(err.to_string())),
            Ok(Ok(env)) => Ok(env),
            Err(err) => Err(CexError::Timeout(err)),
        }?;
        Ok((always_allow_result, always_deny_result))
    })
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
            // We let Rust compile the policies as it's faster than Lean
            if let Ok(cps) = CompiledPolicySet::compile(&policyset, &req_env, &schema) {
                match get_cex(&always_allows_asserts(&cps), &always_denies_asserts(&cps)) {
                    Ok((Some(env_deny), Some(env_allow))) => {
                        assert_eq!(
                            reproduce(&env_deny, &policyset),
                            Decision::Deny,
                            "Rust SymCC returned a wrong counterexample"
                        );
                        assert_eq!(
                            reproduce(&env_allow, &policyset),
                            Decision::Allow,
                            "Rust SymCC returned a wrong counterexample"
                        );
                    }
                    Ok((Some(env_deny), None)) => {
                        assert_eq!(
                            reproduce(&env_deny, &policyset),
                            Decision::Deny,
                            "Rust SymCC returned a wrong counterexample"
                        )
                    }
                    Ok((None, Some(env_allow))) => {
                        assert_eq!(
                            reproduce(&env_allow, &policyset),
                            Decision::Allow,
                            "Rust SymCC returned a wrong counterexample"
                        );
                    }
                    Ok((None, None)) => {}
                    Err(CexError::Solver(err)) => {
                        panic!("Error running solver: {err}");
                    }
                    Err(CexError::Timeout(err)) => {
                        panic!("Solver timed out: {err}");
                    }
                    Err(CexError::Other(err)) => panic!("failed to run checksat: {err}"),
                }
            }
        }
    }
});
