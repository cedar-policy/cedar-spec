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

use cedar_lean_ffi::{CedarLeanFfi, FfiError, LeanSchema};
use cedar_policy::{Authorizer, Policy, PolicySet, RequestEnv, Schema};
use cedar_policy_core::ast::PolicyID;
use cedar_policy_generators::{
    abac::ABACPolicy,
    accum, r#gen as weighted_generate, gen_inner,
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema,
    schema_gen::SchemaGen,
    settings::ABACSettings,
};
use cedar_policy_symcc::{
    CedarSymCompiler, CompiledPolicy, CompiledPolicySet, Env, WellFormedAsserts,
    err::{EncodeError, Error},
    solver::{self, LocalSolver, SolverError, WriterSolver},
    term::Term,
};
use itertools::Itertools;
use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use log::{debug, warn};
use std::{
    collections::{BTreeSet, HashSet},
    fmt::Display,
    sync::LazyLock,
};
use tokio::{
    process::Command,
    sync::{Mutex, MutexGuard},
    time::{Duration, timeout},
};

/// Tokio runtime used by all SymCC fuzz targets that need one. Note that it
/// runs tasks on only a single OS thread.
pub static RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
});

/// Create a local solver suited for fuzzing
fn local_solver() -> Result<LocalSolver, String> {
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
    LocalSolver::from_command(&mut cmd).map_err(|err| err.to_string())
}

pub async fn smtlib_of_check_asserts(
    rust_asserts: &WellFormedAsserts<'_>,
) -> Result<String, String> {
    let mut solver = CedarSymCompiler::new(WriterSolver {
        w: Vec::<u8>::new(),
    })
    .expect("solver construction should succeed");
    match solver.check_sat(rust_asserts).await {
        Ok(_) | Err(Error::SolverUnknown) => {
            Ok(String::from_utf8(std::mem::take(&mut solver.solver_mut().w)).unwrap())
        }
        Err(e) => Err(e.to_string()),
    }
}

#[track_caller]
pub fn lean_smtlib_of_check_asserts(
    rust_asserts: &WellFormedAsserts<'_>,
    lean_ffi: &CedarLeanFfi,
    lean_schema: LeanSchema,
    req_env: &RequestEnv,
) -> Result<String, FfiError> {
    let lean_asserts: Vec<_> = rust_asserts
        .asserts()
        .iter()
        .map(|assert| assert.clone().into())
        .collect();
    debug!("Lean asserts: {lean_asserts:#?}");
    lean_ffi.smtlib_of_check_asserts(&lean_asserts, lean_schema, req_env)
}

#[track_caller]
pub fn assert_smtlib_scripts_match<E1: Display, E2: Display>(
    rust_smtlib: Result<String, E1>,
    lean_smtlib: Result<String, E2>,
) {
    match (rust_smtlib, lean_smtlib) {
        (Ok(rust), Ok(lean)) => {
            similar_asserts::assert_eq!(rust, lean, "Rust:\n{rust}\nLean:\n{lean}")
        }
        (Ok(_), Err(e)) => panic!("Lean encoding should succeed: {e}"),
        (Err(e), Ok(_)) => panic!("Rust encoding should succeed: {e}"),
        (Err(_), Err(_)) => {}
    }
}

#[track_caller]
pub fn assert_that_asserts_match(
    rust_asserts: WellFormedAsserts<'_>,
    lean_asserts: impl IntoIterator<Item = cedar_lean_ffi::Term>,
) {
    let lean_asserts = lean_asserts
        .into_iter()
        .map(|t| Term::try_from(t).expect("term conversion should succeed"))
        .collect::<BTreeSet<_>>();
    let rust_asserts = BTreeSet::from_iter(rust_asserts.asserts().as_ref().iter().cloned());

    if lean_asserts != rust_asserts {
        // we have a DRT failure, just need to determine the most helpful way to report it

        // first check whether the pretty-printed representations of both Term lists are equal.
        // if there's a discrepancy, it will be easier to debug if we look at the difference
        // between pretty-printed representations.
        let pretty_lean_asserts = lean_asserts.iter().join("\n");
        let pretty_rust_asserts = rust_asserts.iter().join("\n");
        similar_asserts::assert_eq!(pretty_lean_asserts, pretty_rust_asserts);

        // if we get here, the Terms are not equal but their pretty-printed representations are.
        // The discrepancy must be in the parts of the Term structures that aren't represented
        // in the pretty-printed part, e.g., type information.
        similar_asserts::assert_eq!(
            lean_asserts,
            rust_asserts,
            "\n\nLean terms:\n{pretty_lean_asserts}\n\nRust terms:\n{pretty_rust_asserts}\n\n",
        );
    }
}

/// Limit on the number of request envs the schema may define. We also do not
/// allow the number of _actions_ to exceed that number, even in schemas that
/// comply with the request env limit (e.g., because most actions have no
/// `appliesTo` and therefore no request envs).  As of this writing, Lean
/// performance for many targets is cubic in the number of actions / request
/// envs, just considering that `ActionSchema.validateWellFormed` is at least
/// quadratic in the number of actions (if actions have "large" ancestor lists)
/// and that we call it once per request env.
pub type MaxRequestEnvs = usize;

/// Settings shared by all SymCC fuzz targets that use `FuzzTargetInput`s
/// declared in this file.
///
/// See comments on the `MaxRequestEnvs` type.
const fn settings(max_request_envs: MaxRequestEnvs) -> ABACSettings {
    ABACSettings {
        max_depth: 3,
        max_width: 3,
        total_action_request_env_limit: max_request_envs,
        max_actions: max_request_envs,
        ..ABACSettings::type_directed()
    }
}

/// Input to SymCC fuzz targets that need a single policy.
///
/// See comments on the `MaxRequestEnvs` type.
#[derive(Debug, Clone)]
pub struct SinglePolicyFuzzTargetInput<const MAX_REQUEST_ENVS: MaxRequestEnvs> {
    /// generated schema
    schema: schema::Schema,
    /// generated policy
    policy: ABACPolicy,
}

impl<const MAX_REQUEST_ENVS: MaxRequestEnvs> SinglePolicyFuzzTargetInput<MAX_REQUEST_ENVS> {
    /// Get the `cedar_policy::Schema` and `cedar_policy::Policy` that were generated
    pub fn into_inputs(self) -> Result<(Schema, Policy), cedar_policy::SchemaError> {
        Ok((Schema::try_from(self.schema)?, self.policy.into()))
    }

    /// Get the `cedar_policy::Schema` and singleton `cedar_policy::PolicySet` that were generated
    pub fn into_inputs_as_pset(self) -> Result<(Schema, PolicySet), cedar_policy::SchemaError> {
        let mut pset = PolicySet::new();
        pset.add(self.policy.into())
            .expect("creating a singleton policyset should not fail");
        Ok((Schema::try_from(self.schema)?, pset))
    }
}

impl<'a, const MAX_REQUEST_ENVS: MaxRequestEnvs> Arbitrary<'a>
    for SinglePolicyFuzzTargetInput<MAX_REQUEST_ENVS>
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(settings(MAX_REQUEST_ENVS), u)?;
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

fn arbitrary_policies(
    schema: &schema::Schema,
    hierarchy: &Hierarchy,
    u: &mut Unstructured<'_>,
) -> arbitrary::Result<Vec<ABACPolicy>> {
    let len = weighted_generate!(u,
        1 => 0, // very rarely, try the empty-policyset case
        0 => 1, // other targets cover the single-policy case
        50 => 2,
        40 => 3,
        30 => 4,
        20 => 5,
        10 => 6,
        8 => 7,
        6 => 8,
        4 => 9,
        2 => 10
    );
    let mut policies: Vec<ABACPolicy> = Vec::with_capacity(len);
    for _ in 0..len {
        policies.push(schema.arbitrary_policy(&hierarchy, u)?);
    }
    // we want to ensure that the policies all have unique IDs.
    // this will be a list of policy IDs that we have seen (and will ensure there are no duplicates of)
    let mut seen = HashSet::with_capacity(policies.len());
    // to avoid mutating-while-iterating, we collect a list of updates we need to make:
    // an entry in `updates` indicates we need to update the policy at the given index to have the given policy ID.
    let mut updates: Vec<(usize, PolicyID)> = Vec::new();
    for (idx, id) in policies.iter().map(|p| p.0.id()).enumerate() {
        if !seen.insert(id.clone()) {
            // If we've seen this ID already, we need to change it.
            // We'll do this by appending `_{idx}` to the ID.
            let mut new_id = format!("{id}_{idx}");
            while !seen.insert(PolicyID::from_string(new_id.clone())) {
                // uh-oh -- the policyid we just tried is _also_ already-seen.
                // we'll try again by appending `*` to the ID.
                new_id.push('*');
            }
            // the above loop can run at most `policies.len()` iterations.
            // now that it's done, we know that `new_id` is unique, and we've marked it as `seen`.
            // we will assign it to the policy that originally had the conflicting ID.
            updates.push((idx, PolicyID::from_string(new_id)));
        }
    }
    // now apply the updates
    for (idx, id) in updates {
        policies[idx].0.set_id(id);
    }
    Ok(policies)
}

/// Input to SymCC fuzz targets that need a single policyset (containing 0 or more policies).
///
/// See comments on the `MaxRequestEnvs` type.
#[derive(Debug, Clone)]
pub struct SinglePolicySetFuzzTargetInput<const MAX_REQUEST_ENVS: MaxRequestEnvs> {
    /// generated schema
    schema: schema::Schema,
    /// generated policyset
    pset: Vec<ABACPolicy>,
}

impl<const MAX_REQUEST_ENVS: MaxRequestEnvs> SinglePolicySetFuzzTargetInput<MAX_REQUEST_ENVS> {
    /// Get the `cedar_policy::Schema` and `cedar_policy::PolicySet` that were generated
    pub fn into_inputs(self) -> Result<(Schema, PolicySet), cedar_policy::SchemaError> {
        Ok((
            Schema::try_from(self.schema)?,
            PolicySet::from_policies(self.pset.into_iter().map(Into::into))
                .expect("creating a policyset from the generated policies should not fail"),
        ))
    }
}

impl<'a, const MAX_REQUEST_ENVS: MaxRequestEnvs> Arbitrary<'a>
    for SinglePolicySetFuzzTargetInput<MAX_REQUEST_ENVS>
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(settings(MAX_REQUEST_ENVS), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let pset = arbitrary_policies(&schema, &hierarchy, u)?;

        Ok(Self { schema, pset })
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

/// Input to SymCC fuzz targets that need two individual policies.
///
/// See comments on the `MaxRequestEnvs` type.
#[derive(Debug, Clone)]
pub struct TwoPolicyFuzzTargetInput<const MAX_REQUEST_ENVS: MaxRequestEnvs> {
    /// generated schema
    schema: schema::Schema,
    /// generated policy
    policy1: ABACPolicy,
    /// generated policy
    policy2: ABACPolicy,
}

impl<const MAX_REQUEST_ENVS: MaxRequestEnvs> TwoPolicyFuzzTargetInput<MAX_REQUEST_ENVS> {
    /// Get the `cedar_policy::Schema` and both `cedar_policy::Policy`s that were generated
    pub fn into_inputs(self) -> Result<(Schema, Policy, Policy), cedar_policy::SchemaError> {
        Ok((
            Schema::try_from(self.schema)?,
            self.policy1.into(),
            self.policy2.into(),
        ))
    }

    /// Get the `cedar_policy::Schema` and both singleton `cedar_policy::PolicySet`s that were generated
    pub fn into_inputs_as_psets(
        self,
    ) -> Result<(Schema, PolicySet, PolicySet), cedar_policy::SchemaError> {
        let mut pset1 = PolicySet::new();
        pset1
            .add(self.policy1.into())
            .expect("creating a singleton policyset should not fail");
        let mut pset2 = PolicySet::new();
        pset2
            .add(self.policy2.into())
            .expect("creating a singleton policyset should not fail");
        Ok((Schema::try_from(self.schema)?, pset1, pset2))
    }
}

impl<'a, const MAX_REQUEST_ENVS: MaxRequestEnvs> Arbitrary<'a>
    for TwoPolicyFuzzTargetInput<MAX_REQUEST_ENVS>
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(settings(MAX_REQUEST_ENVS), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy1 = schema.arbitrary_policy(&hierarchy, u)?;
        let policy2 = schema.arbitrary_policy(&hierarchy, u)?;

        Ok(Self {
            schema,
            policy1,
            policy2,
        })
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

/// Input to SymCC fuzz targets that need two policysets (each containing 0 or more policies).
///
/// See comments on the `MaxRequestEnvs` type.
#[derive(Debug, Clone)]
pub struct TwoPolicySetFuzzTargetInput<const MAX_REQUEST_ENVS: MaxRequestEnvs> {
    /// generated schema
    schema: schema::Schema,
    /// generated policyset
    pset1: Vec<ABACPolicy>,
    /// generated policyset
    pset2: Vec<ABACPolicy>,
}

impl<const MAX_REQUEST_ENVS: MaxRequestEnvs> TwoPolicySetFuzzTargetInput<MAX_REQUEST_ENVS> {
    /// Get the `cedar_policy::Schema` and both `cedar_policy::PolicySet`s that were generated
    pub fn into_inputs(self) -> Result<(Schema, PolicySet, PolicySet), cedar_policy::SchemaError> {
        Ok((
            Schema::try_from(self.schema)?,
            PolicySet::from_policies(self.pset1.into_iter().map(Into::into))
                .expect("creating a policyset from the generated policies should not fail"),
            PolicySet::from_policies(self.pset2.into_iter().map(Into::into))
                .expect("creating a policyset from the generated policies should not fail"),
        ))
    }
}

impl<'a, const MAX_REQUEST_ENVS: MaxRequestEnvs> Arbitrary<'a>
    for TwoPolicySetFuzzTargetInput<MAX_REQUEST_ENVS>
{
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(settings(MAX_REQUEST_ENVS), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let pset1 = arbitrary_policies(&schema, &hierarchy, u)?;
        let pset2 = arbitrary_policies(&schema, &hierarchy, u)?;

        Ok(Self {
            schema,
            pset1,
            pset2,
        })
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

/// For DRT purposes we use a wrapper around `LocalSolver` that allows us to
/// also inspect the raw model if we want
pub struct WrappedLocalSolver {
    pub solver: LocalSolver,
    /// Copy of the raw model generated by the most recent call to `get_model()`.
    ///
    /// If `get_model()` returned `Ok(None)`, or if `get_model()` has never been
    /// called, this will be `None`.
    pub raw_model: Option<String>,
}

impl WrappedLocalSolver {
    fn new(solver: LocalSolver) -> Self {
        Self {
            solver,
            raw_model: None,
        }
    }
}

impl solver::Solver for WrappedLocalSolver {
    fn smtlib_input(&mut self) -> &mut (dyn tokio::io::AsyncWrite + Unpin + Send) {
        self.solver.smtlib_input()
    }
    async fn check_sat(&mut self) -> Result<solver::Decision, SolverError> {
        self.solver.check_sat().await
    }
    async fn get_model(&mut self) -> Result<Option<String>, SolverError> {
        self.raw_model = self.solver.get_model().await?;
        Ok(self.raw_model.clone())
    }
}

pub struct SymCCWithUsageLimit {
    pub symcc: CedarSymCompiler<WrappedLocalSolver>,
    /// Maximum number of `CedarSymCompiler` calls (more specifically, calls of
    /// `get_solver()`, not all of which are actual solver interactions) before
    /// we kill the solver process and start a new one
    usage_count: usize,
}

impl SymCCWithUsageLimit {
    const SOLVER_USAGE_LIMIT: usize = 10_000;
}

fn new_symcc() -> CedarSymCompiler<WrappedLocalSolver> {
    let solver = local_solver().expect("CVC5 should exist");
    CedarSymCompiler::new(WrappedLocalSolver::new(solver))
        .expect("CedarSymCompiler construction should succeed")
}

static SOLVER: LazyLock<Mutex<SymCCWithUsageLimit>> = LazyLock::new(|| {
    Mutex::new(SymCCWithUsageLimit {
        symcc: new_symcc(),
        usage_count: 0,
    })
});

pub async fn get_solver() -> MutexGuard<'static, SymCCWithUsageLimit> {
    let mut guard = SOLVER.lock().await;
    guard.usage_count += 1;
    if guard.usage_count >= SymCCWithUsageLimit::SOLVER_USAGE_LIMIT {
        let _ = guard.symcc.solver_mut().solver.clean_up().await;
        guard.symcc = new_symcc();
        guard.usage_count = 0;
    }
    guard
}

/// Solver timeout used for `get_cex()`
const TIMEOUT_DUR: Duration = Duration::from_secs(60);

/// Run the given future (producing `Result<Option<Env>>`), and return the
/// counterexample if one was successfully generated.
///
/// Panics on unexpected errors. Ignores certain expected errors, returning
/// `None`. Also returns `None` if the property holds and there is no
/// counterexample.
pub async fn get_cex(
    f: impl Future<Output = cedar_policy_symcc::err::Result<Option<Env>>>,
) -> Option<Env> {
    match timeout(TIMEOUT_DUR, f).await {
        Ok(Ok(None)) => None, // successfully executed, no counterexample because the property holds
        Ok(Ok(Some(cex))) => Some(cex),
        Err(err) => panic!(
            "found a slow unit (solver took more than {secs:.2} sec) probably worth investigating: {err}",
            secs = TIMEOUT_DUR.as_secs_f32()
        ),
        Ok(Err(Error::SolverError(err))) => panic!("solver failed: {err}"),
        Ok(Err(Error::EncodeError(EncodeError::EncodeStringFailed(_))))
        | Ok(Err(Error::EncodeError(EncodeError::EncodePatternFailed(_)))) => {
            // Encoding errors are benign -- SMTLIB doesn't support full unicode
            // but our generators generate full unicode
            None
        }
        Ok(Err(err)) => panic!("{err}"), // other errors are unexpected
    }
}

/// Return the `Decision` produced by the Cedar (Rust) authorizer on the given
/// `policies` given a concrete `Env`
pub fn reproduce(env: &Env, policies: &PolicySet) -> cedar_policy::Decision {
    Authorizer::new()
        .is_authorized(&env.request, policies, &env.entities)
        .decision()
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
    ) -> Result<Self::CompiledInput, Box<Error>>;

    /// Executes this task.
    fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        input: &Self::CompiledInput,
    ) -> impl std::future::Future<Output = Result<bool, Error>> + Send;

    /// Checks that when this task is performed on input that successfully compiles, it either times out or produces a value.
    fn check_ok(
        &self,
        schema: Schema,
        raw_input: Self::RawInput,
    ) -> impl std::future::Future<Output = Result<(), Box<Error>>> + Send {
        async move {
            // Use LocalSolver::cvc5_with_args to remove the timeout.
            let solver = LocalSolver::cvc5_with_args(Vec::<String>::new())
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
        compiler: &mut CedarSymCompiler<LocalSolver>,
        schema: &Schema,
        raw_input: &Self::RawInput,
    ) -> impl std::future::Future<Output = Result<(), Box<Error>>> + Send {
        async move {
            for env in schema.request_envs() {
                // Compilation should succeed for inputs generated by our generators, but for now if compilation returns an error we just warn-and-skip.
                let Ok(compiled_input) = self.compile(schema, &env, raw_input) else {
                    warn!(
                        "Compilation failed for input generated by our generators:\n\nschema:\n<as of this writing, no good way to print a cedar_policy::Schema object>\n\nenv:\n({p}, {a}, {r})\n\npolicies:\n{raw_input}\n",
                        p = env.principal(),
                        a = env.action(),
                        r = env.resource()
                    );
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
    type CompiledInput = CompiledPolicySet;

    fn compile(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::CompiledInput, Box<Error>> {
        CompiledPolicySet::compile(raw_input, env, schema).map_err(Box::new)
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        input: &Self::CompiledInput,
    ) -> Result<bool, Error> {
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
    ) -> Result<Self::CompiledInput, Box<Error>> {
        CompiledPolicy::compile(raw_input, env, schema).map_err(Box::new)
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        input: &Self::CompiledInput,
    ) -> Result<bool, Error> {
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
        writeln!(
            f,
            "pset1:\n{pset1}\n\npset2:\n{pset2}\n",
            pset1 = self.pset1,
            pset2 = self.pset2
        )
    }
}

impl ValidationTask for PolicySetPairTask {
    type RawInput = PolicySetPair;
    type CompiledInput = (CompiledPolicySet, CompiledPolicySet);

    fn compile(
        &self,
        schema: &Schema,
        env: &RequestEnv,
        raw_input: &Self::RawInput,
    ) -> Result<Self::CompiledInput, Box<Error>> {
        Ok((
            CompiledPolicySet::compile(&raw_input.pset1, env, schema)?,
            CompiledPolicySet::compile(&raw_input.pset2, env, schema)?,
        ))
    }

    async fn execute(
        &self,
        compiler: &mut CedarSymCompiler<LocalSolver>,
        (pset1, pset2): &Self::CompiledInput,
    ) -> Result<bool, Error> {
        match self {
            PolicySetPairTask::CheckImplies => compiler.check_implies_opt(pset1, pset2).await,
            PolicySetPairTask::CheckEquivalent => compiler.check_equivalent_opt(pset1, pset2).await,
            PolicySetPairTask::CheckDisjoint => compiler.check_disjoint_opt(pset1, pset2).await,
        }
    }
}
