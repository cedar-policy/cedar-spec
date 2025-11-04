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
    err::{EncodeError, Error},
    solver::LocalSolver,
    Asserts, CedarSymCompiler, SymEnv, WellFormedAsserts, WellTypedPolicies, WellTypedPolicy,
};
use tokio::process::Command;

/// Compile a well-typed policy set to `Asserts`
pub fn compile_well_typed_policies(
    func: impl for<'a> Fn(
        &WellTypedPolicies,
        &'a SymEnv,
    ) -> cedar_policy_symcc::err::Result<WellFormedAsserts<'a>>,
    policy: &WellTypedPolicies,
    schema: &Schema,
    req_env: &RequestEnv,
) -> Result<Asserts, String> {
    let sym_env = SymEnv::new(&schema, &req_env).map_err(|err| err.to_string())?;
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
    func(&well_typed_policies, &sym_env).map_err(|err| err.to_string())
}

/// The limit on the total number of request envs specific to symcc
pub const fn total_action_request_env_limit() -> usize {
    128
}

/// Creat a local solver suited for fuzzing
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
    type RawInput: Send + Sync;
    type WellTypedInput: Send;

    /// Returns whether the specified raw input passed strict validation against the specified schema.
    fn is_valid(&self, schema: &Schema, raw_input: &Self::RawInput) -> bool;

    /// Constructs a well-typed input from the specified raw input.
    fn to_well_typed(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::WellTypedInput, Box<cedar_policy_symcc::err::Error>>;

    /// Executes this task.
    fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        env: &SymEnv,
        input: &Self::WellTypedInput,
    ) -> impl std::future::Future<Output = Result<bool, cedar_policy_symcc::err::Error>> + Send;

    /// Checks that when this task performed on input that successfully validates it either times out or produces a value.
    fn check_ok(
        &self,
        schema: Schema,
        raw_input: Self::RawInput,
    ) -> impl std::future::Future<Output = Result<(), Box<cedar_policy_symcc::err::Error>>> + Send
    {
        async move {
            if self.is_valid(&schema, &raw_input) {
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
            } else {
                Ok(())
            }
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
                // Encode the request environment symbolically.
                // Symbolic environment creation should succeed for request environments derived from schema; propagate the error.
                let sym_env = SymEnv::new(schema, &env)?;
                // Well-typed input creation should succeed for validated input; propagate the error.
                let well_typed_input = self.to_well_typed(schema, &env, raw_input)?;
                // Perform the verification check; timeout after one second.
                let result = tokio::time::timeout(
                    std::time::Duration::from_secs(1),
                    self.execute(compiler, &sym_env, &well_typed_input),
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

    type WellTypedInput = WellTypedPolicies;

    fn is_valid(&self, schema: &Schema, policy_set: &PolicySet) -> bool {
        cedar_policy::Validator::new(schema.clone())
            .validate(policy_set, cedar_policy::ValidationMode::Strict)
            .validation_passed()
    }

    fn to_well_typed(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::WellTypedInput, Box<cedar_policy_symcc::err::Error>> {
        WellTypedPolicies::from_policies(raw_input, env, schema).map_err(Box::new)
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        env: &SymEnv,
        input: &Self::WellTypedInput,
    ) -> Result<bool, cedar_policy_symcc::err::Error> {
        match self {
            Self::CheckAlwaysAllows => compiler.check_always_allows(input, env).await,
            Self::CheckAlwaysDenies => compiler.check_always_denies(input, env).await,
        }
    }
}

/// A SymCC verification task that is performed on a single policy.
pub enum PolicyTask {
    CheckNeverErrors,
}

impl ValidationTask for PolicyTask {
    type RawInput = Policy;

    type WellTypedInput = WellTypedPolicy;

    fn is_valid(&self, schema: &Schema, raw_input: &Self::RawInput) -> bool {
        let mut policy_set = PolicySet::new();
        policy_set.add(raw_input.clone()).unwrap();
        cedar_policy::Validator::new(schema.clone())
            .validate(&policy_set, cedar_policy::ValidationMode::Strict)
            .validation_passed()
    }

    fn to_well_typed(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::WellTypedInput, Box<cedar_policy_symcc::err::Error>> {
        WellTypedPolicy::from_policy(raw_input, env, schema).map_err(Box::new)
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        env: &SymEnv,
        input: &Self::WellTypedInput,
    ) -> Result<bool, cedar_policy_symcc::err::Error> {
        match self {
            Self::CheckNeverErrors => compiler.check_never_errors(input, env).await,
        }
    }
}

/// A SymCC verification task that is performed on a pair of policy sets.
pub enum PolicySetPairTask {
    CheckImplies,
    CheckEquivalent,
    CheckDisjoint,
}

impl ValidationTask for PolicySetPairTask {
    type RawInput = (PolicySet, PolicySet);

    type WellTypedInput = (WellTypedPolicies, WellTypedPolicies);

    fn is_valid(&self, schema: &Schema, raw_input: &Self::RawInput) -> bool {
        cedar_policy::Validator::new(schema.clone())
            .validate(&raw_input.0, cedar_policy::ValidationMode::Strict)
            .validation_passed()
            && cedar_policy::Validator::new(schema.clone())
                .validate(&raw_input.1, cedar_policy::ValidationMode::Strict)
                .validation_passed()
    }

    fn to_well_typed(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::WellTypedInput, Box<cedar_policy_symcc::err::Error>> {
        let p0 = WellTypedPolicies::from_policies(&raw_input.0, env, schema)?;
        let p1 = WellTypedPolicies::from_policies(&raw_input.1, env, schema)?;
        Ok((p0, p1))
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        env: &SymEnv,
        (pset1, pset2): &Self::WellTypedInput,
    ) -> Result<bool, cedar_policy_symcc::err::Error> {
        match self {
            PolicySetPairTask::CheckImplies => compiler.check_implies(pset1, pset2, env).await,
            PolicySetPairTask::CheckEquivalent => {
                compiler.check_equivalent(pset1, pset2, env).await
            }
            PolicySetPairTask::CheckDisjoint => compiler.check_disjoint(pset1, pset2, env).await,
        }
    }
}
