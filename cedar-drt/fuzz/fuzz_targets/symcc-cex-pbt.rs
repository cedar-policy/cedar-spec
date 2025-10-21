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
    symcc::{compile_policies, local_solver, total_action_request_env_limit},
};

use cedar_policy::{Authorizer, Decision, Policy, PolicySet, Schema};

use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema, settings::ABACSettings,
};

use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use log::debug;
use std::convert::TryFrom;
use tokio::time::{error::Elapsed, timeout, Duration};

use cedar_policy_symcc::{
    compile_always_allows, compile_always_denies, err::SolverError, solver::LocalSolver,
    CedarSymCompiler, Env, SymEnv, WellFormedAsserts,
};

use std::sync::{LazyLock, Mutex};

static RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
});

struct Solver {
    local_solver: CedarSymCompiler<LocalSolver>,
    usage_count: usize,
}

impl Solver {
    const SOLVER_USAGE_LIMIT: usize = 100_000;
}

static SOLVER: LazyLock<Mutex<Solver>> = LazyLock::new(|| {
    Mutex::new(Solver {
        local_solver: CedarSymCompiler::new(local_solver().expect("CVC5 should exist"))
            .expect("solver construction should succeed"),
        usage_count: 0,
    })
});

async fn get_solver() -> std::sync::MutexGuard<'static, Solver> {
    let mut guard = SOLVER.lock().unwrap();
    guard.usage_count += 1;
    if guard.usage_count >= Solver::SOLVER_USAGE_LIMIT {
        let _ = guard.local_solver.solver_mut().clean_up().await;
        guard.local_solver = CedarSymCompiler::new(local_solver().expect("CVC5 should exist"))
            .expect("solver construction should succeed");
        guard.usage_count = 0;
    }
    guard
}

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated policy
    pub policy: ABACPolicy,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 3,
    max_width: 3,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    per_action_request_env_limit: ABACSettings::default_per_action_request_env_limit(),
    total_action_request_env_limit: total_action_request_env_limit(),
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;

        Ok(Self { schema, policy })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
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
            // Propagate any error errors because we shouldn't continue running
            // the solver if it errors
            Ok(Err(cedar_policy_symcc::err::Error::SolverError(err))) => Err(CexError::Solver(err)),
            // Encoding errors are benign
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

fn reproduce(env: &Env, policies: &PolicySet) -> bool {
    let authorizer = Authorizer::new();
    matches!(
        authorizer
            .is_authorized(&env.request, policies, &env.entities)
            .decision(),
        Decision::Allow
    )
}

// Fuzzing target checking that counterexamples generated are true counterexamples
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    let mut policyset = PolicySet::new();
    let policy: Policy = input.policy.into();
    policyset.add(policy.clone()).unwrap();
    debug!("Schema: {}\n", input.schema.schemafile_string());
    debug!("Policies: {policy}\n");

    if let Ok(schema) = Schema::try_from(input.schema) {
        for req_env in schema.request_envs() {
            if let Ok(sym_env) = SymEnv::new(&schema, &req_env) {
                // We let Rust to drive the term generation as it's faster than Lean
                if let (Ok(always_allows_asserts), Ok(always_denies_asserts)) = (
                    compile_policies(
                        compile_always_allows,
                        &sym_env,
                        &policyset,
                        &req_env,
                        &schema,
                    ),
                    compile_policies(
                        compile_always_denies,
                        &sym_env,
                        &policyset,
                        &req_env,
                        &schema,
                    ),
                ) {
                    match get_cex(&always_allows_asserts, &always_denies_asserts) {
                        Ok((Some(env_deny), Some(env_allow))) => {
                            if reproduce(&env_deny, &policyset) {
                                panic!("Rust SymCC a wrong counterexample: authorization should deny but allow");
                            }
                            if !reproduce(&env_allow, &policyset) {
                                panic!("Rust SymCC a wrong counterexample: authorization should allow but deny");
                            }
                        }
                        Ok((Some(env_deny), None)) => {
                            if reproduce(&env_deny, &policyset) {
                                panic!("Rust SymCC a wrong counterexample: authorization should deny but allow");
                            }
                        }
                        Ok((None, Some(env_allow))) => {
                            if !reproduce(&env_allow, &policyset) {
                                panic!("Rust SymCC a wrong counterexample: authorization should allow but deny");
                            }
                        }
                        Ok((None, None)) => {}
                        Err(CexError::Solver(err)) => {
                            panic!("Error running solver: {err}");
                        }
                        Err(CexError::Timeout(err)) => {
                            panic!("Solver timed out: {err}");
                        }
                        Err(CexError::Other(err)) => panic!("failing to run checksat: {err}"),
                    }
                }
            }
        }
    }
});
