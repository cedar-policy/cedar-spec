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

use cedar_policy::{Policy, PolicySet, RequestEnv, Schema};
use cedar_policy_symcc::{
    Asserts, CedarSymCompiler, CompiledPolicies, CompiledPolicy, SymEnv, WellFormedAsserts, WellTypedPolicies, err::{EncodeError, Error}, solver::LocalSolver
};
use log::warn;
use std::fmt::Display;
use tokio::process::Command;

/// Compile a well-typed policy set to `WellFormedAsserts`
pub fn compile_well_typed_policies(
    func: impl for<'a> Fn(
        &WellTypedPolicies,
        &'a SymEnv,
    ) -> cedar_policy_symcc::err::Result<WellFormedAsserts<'a>>,
    policy: &WellTypedPolicies,
    schema: &Schema,
    req_env: &RequestEnv,
) -> Result<Asserts, String> {
    let sym_env = SymEnv::new(schema, req_env).map_err(|err| err.to_string())?;
    let asserts = func(policy, &sym_env).map_err(|err| err.to_string())?;
    Ok(asserts.asserts().clone())
}

/// Compile a policy set to `WellFormedAsserts`
pub fn compile_policies<'a>(
    func: impl for<'b> Fn(
        &WellTypedPolicies,
        &'b SymEnv,
    ) -> cedar_policy_symcc::err::Result<WellFormedAsserts<'b>>,
    sym_env: &'a SymEnv,
    policyset: &PolicySet,
    req_env: &RequestEnv,
    schema: &Schema,
) -> Result<WellFormedAsserts<'a>, String> {
    let well_typed_policies = WellTypedPolicies::from_policies(policyset, req_env, schema)
        .map_err(|err| err.to_string())?;
    func(&well_typed_policies, sym_env).map_err(|err| err.to_string())
}

/// The limit on the total number of request envs specific to symcc
pub const fn total_action_request_env_limit() -> usize {
    128
}

/// Create a local solver suited for fuzzing
pub fn local_solver() -> Result<cedar_policy_symcc::solver::LocalSolver, String> {
    let path = std::env::var("CVC5").unwrap_or_else(|_| "cvc5".into());
    let mut cmd = Command::new(path);
    // Do not set `tlimit` here and let tokio's `timeout` function handle timeout
    cmd.args(["--lang", "smt"]);
    unsafe {
        cmd.pre_exec(|| {
            // Set memory limit to 1GB before CVC5 starts
            let limit = libc::rlimit {
                rlim_cur: 1024 * 1024 * 1024,
                rlim_max: 1024 * 1024 * 1024,
            };
            libc::setrlimit(libc::RLIMIT_AS, &limit);
            Ok(())
        });
    }
    cedar_policy_symcc::solver::LocalSolver::from_command(&mut cmd).map_err(|err| err.to_string())
}

pub trait ValidationTask: Sync {
    type RawInput: Send + Sync + Display;
    type CompiledInput: Send;

    /// Constructs a `CompiledInput` from the specified `RawInput`.
    fn compile(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::CompiledInput, Box<cedar_policy_symcc::err::Error>>;

    /// Executes this task.
    fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        input: &Self::CompiledInput,
    ) -> impl std::future::Future<Output = Result<bool, cedar_policy_symcc::err::Error>> + Send;

    /// Checks that when this task is performed on input that successfully compiles, it either times out or produces a value.
    fn check_ok(
        &self,
        schema: Schema,
        raw_input: Self::RawInput,
    ) -> impl std::future::Future<Output = Result<(), Box<cedar_policy_symcc::err::Error>>> + Send
    {
        async move {
            // Use LocalSolver::cvc5_with_args to remove the timeout.
            let solver =
                cedar_policy_symcc::solver::LocalSolver::cvc5_with_args(Vec::<String>::new())
                    .map_err(|e| Box::new(e.into()))?;
            let mut compiler = CedarSymCompiler::new(solver)?;
            let check_result = self
                .check_ok_inner(&mut compiler, &schema, &raw_input)
                .await;
            // Ensure the solver process is reaped.
            let clean_up_result = compiler.solver_mut().clean_up().await;
            let check_result = match check_result {
                Ok(_) => Ok(()),
                // SMT-LIB only supports a limited set of unicode
                Err(err)
                    if matches!(
                        err.as_ref(),
                        Error::EncodeError(EncodeError::EncodePatternFailed(_))
                            | Error::EncodeError(EncodeError::EncodeStringFailed(_))
                    ) =>
                {
                    Ok(())
                }
                Err(err) => Err(err),
            };
            check_result?;
            clean_up_result.map_err(|e| Box::new(e.into()))
        }
    }

    fn check_ok_inner(
        &self,
        compiler: &mut CedarSymCompiler<cedar_policy_symcc::solver::LocalSolver>,
        schema: &Schema,
        raw_input: &Self::RawInput,
    ) -> impl std::future::Future<Output = Result<(), Box<cedar_policy_symcc::err::Error>>> + Send
    {
        async move {
            for env in schema.request_envs() {
                // Compilation should succeed for inputs generated by our generators, but for now if compilation returns an error we just warn-and-skip.
                let Ok(compiled_input) = self.compile(schema, &env, raw_input) else {
                    warn!("Compilation failed for input generated by our generators:\n\nschema:\n<as of this writing, no good way to print a cedar_policy::Schema object>\n\nenv:\n({p}, {a}, {r})\n\npolicies:\n{raw_input}\n", p = env.principal(), a = env.action(), r = env.resource());
                    continue;
                };
                // Perform the verification check; timeout after one second.
                let result = tokio::time::timeout(
                    std::time::Duration::from_secs(1),
                    self.execute(compiler, &compiled_input),
                )
                .await;
                // Allow timeouts.
                if let Ok(result) = result {
                    // The task should produce a value; propagate the error
                    result?;
                }
            }
            Ok(())
        }
    }
}

/// A SymCC verification task that is performed on a single policy set.
pub enum PolicySetTask {
    CheckAlwaysAllows,
    CheckAlwaysDenies,
}

impl ValidationTask for PolicySetTask {
    type RawInput = PolicySet;
    type CompiledInput = CompiledPolicies;

    fn compile(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::CompiledInput, Box<cedar_policy_symcc::err::Error>> {
        CompiledPolicies::compile(raw_input, env, schema).map_err(Box::new)
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        input: &Self::CompiledInput,
    ) -> Result<bool, cedar_policy_symcc::err::Error> {
        match self {
            Self::CheckAlwaysAllows => compiler.check_always_allows_opt(input).await,
            Self::CheckAlwaysDenies => compiler.check_always_denies_opt(input).await,
        }
    }
}

/// A SymCC verification task that is performed on a single policy.
pub enum PolicyTask {
    CheckNeverErrors,
}

impl ValidationTask for PolicyTask {
    type RawInput = Policy;
    type CompiledInput = CompiledPolicy;

    fn compile(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::CompiledInput, Box<cedar_policy_symcc::err::Error>> {
        CompiledPolicy::compile(raw_input, env, schema).map_err(Box::new)
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        input: &Self::CompiledInput,
    ) -> Result<bool, cedar_policy_symcc::err::Error> {
        match self {
            Self::CheckNeverErrors => compiler.check_never_errors_opt(input).await,
        }
    }
}

/// A SymCC verification task that is performed on a pair of policy sets.
pub enum PolicySetPairTask {
    CheckImplies,
    CheckEquivalent,
    CheckDisjoint,
}

pub struct PolicySetPair {
    pub pset1: PolicySet,
    pub pset2: PolicySet,
}

impl Display for PolicySetPair {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "pset1:\n{pset1}\n\npset2:\n{pset2}\n", pset1 = self.pset1, pset2 = self.pset2)
    }
}

impl ValidationTask for PolicySetPairTask {
    type RawInput = PolicySetPair;
    type CompiledInput = (CompiledPolicies, CompiledPolicies);

    fn compile(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::CompiledInput, Box<cedar_policy_symcc::err::Error>> {
        Ok((
          CompiledPolicies::compile(&raw_input.pset1, env, schema)?,
          CompiledPolicies::compile(&raw_input.pset2, env, schema)?,
        ))
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        (pset1, pset2): &Self::CompiledInput,
    ) -> Result<bool, cedar_policy_symcc::err::Error> {
        match self {
            PolicySetPairTask::CheckImplies => compiler.check_implies_opt(pset1, pset2).await,
            PolicySetPairTask::CheckEquivalent => {
                compiler.check_equivalent_opt(pset1, pset2).await
            }
            PolicySetPairTask::CheckDisjoint => compiler.check_disjoint_opt(pset1, pset2).await,
        }
    }
}
