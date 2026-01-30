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
    symcc::{RUNTIME, TwoPolicyFuzzTargetInput, get_cex, get_solver, reproduce},
};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::Decision;
use cedar_policy_symcc::CompiledPolicySet;

// Fuzz target checking that the Rust and Lean implementations produce the same
// counterexamples for SAT results (in this case, for Implies queries on
// arbitrary policies)
fuzz_target!(|input: TwoPolicyFuzzTargetInput| {
    initialize_log();
    if let Ok((schema, policyset1, policyset2)) = input.into_inputs_as_psets() {
        let lean_ffi = CedarLeanFfi::new();
        let lean_schema = lean_ffi.load_lean_schema_object(&schema).unwrap();
        for req_env in schema.request_envs() {
            // We let Rust compile the policies as it's faster than Lean
            if let Ok(cpset1) = CompiledPolicySet::compile(&policyset1, &req_env, &schema)
                && let Ok(cpset2) = CompiledPolicySet::compile(&policyset2, &req_env, &schema)
            {
                RUNTIME.block_on(async {
                    let mut solver_guard = get_solver().await;
                    if let Some(rust_cex) = get_cex(
                        solver_guard
                            .symcc
                            .check_implies_with_counterexample_opt(&cpset1, &cpset2),
                    )
                    .await
                    {
                        // important that we `take()`, replacing the solver's raw_model with `None`,
                        // so that if a future `get_cex()` ends up not calling the solver at all,
                        // the solver will correctly report that `get_model()` was never called
                        let raw_model = std::mem::take(&mut solver_guard.symcc.solver_mut().raw_model);
                        // release the solver for someone else to use, while we call Lean.
                        // note that we do this _after_ we get the raw model, so that we
                        // hold the solver lock while calling `get_cex` and getting the raw
                        // model -- we don't want anyone else to use the solver in between
                        drop(solver_guard);
                        match raw_model {
                            Some(raw_model) => {
                                println!("raw model:\n{raw_model}");
                                let lean_cex = lean_ffi
                                    .run_check_implies_with_cex_given_raw_model(
                                        &policyset1,
                                        &policyset2,
                                        lean_schema.clone(),
                                        &req_env,
                                        &raw_model,
                                    )
                                    .unwrap()
                                    .try_into()
                                    .unwrap();
                                assert_eq!(rust_cex, lean_cex);
                            }
                            None => {
                                // `get_cex()` returned Some, but `raw_model` was None.
                                // As of this writing, this (only?) happens when SymCC reduces
                                // all asserts to constant `true` without calling the solver.
                                // In that case, we have a model on the Rust side, but it is not
                                // produced by a solver because the solver was never called.
                                // We can't call the Lean with a `raw_model` because we don't
                                // have one, so we'll just skip the Rust-Lean check in this case.
                            }
                        }
                        // while we're here, might as well also check that the
                        // counterexample is valid -- it's a negligible amount
                        // more computational work compared to everything we've
                        // already done.
                        // Since this is a counterexample to Implies, we expect
                        // Allow on the LHS and Deny on the RHS
                        assert_eq!(reproduce(&rust_cex, &policyset1), Decision::Allow);
                        assert_eq!(reproduce(&rust_cex, &policyset2), Decision::Deny);
                    }
                });
            }
        }
    }
});
