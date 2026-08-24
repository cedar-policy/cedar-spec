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

//! DRT fuzz target for evaluating residuals against concrete data
//!
//! Particularly interesting given the current implementations since Rust does this by converting to
//! a concrete Expr, while Lean directly interprets the residual.
//!
//! This intentionally runs over entirely arbitrary residuals which may not be well-typed. TPE
//! soundness assumes well-typed policies, but we can show Rust and Lean interpret all residuals the
//! same regardless.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    tpe::{TpeResidualFuzzTargetInput, test_tpe_reauthorize_residual_equiv},
};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::Request;

fuzz_target!(|input: TpeResidualFuzzTargetInput| {
    initialize_log();
    let ffi = CedarLeanFfi::new();
    let entities = input.entities;
    for request in input.reqs {
        let request: Request = request.into();
        test_tpe_reauthorize_residual_equiv(&ffi, &input.residual, &request, &entities);
    }
});
