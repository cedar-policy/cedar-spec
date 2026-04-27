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

//! DRT fuzz target comparing Rust and Lean TPE (is_authorized_partial) outputs,
//! including decisions, policy categorizations, and residual expressions.

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    fuzz_target,
    tpe::{
        TpeFuzzTargetInput, passes_policyset_validation, passes_request_validation,
        test_tpe_is_authorized_equiv,
    },
};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Policy, PolicySet, Request, Schema, Validator};
use log::debug;
use std::convert::TryFrom;

fuzz_target!(|input: TpeFuzzTargetInput| {
    initialize_log();
    let schemafile_string = input.abac_input.schema.schemafile_string();
    if let Ok(schema) = Schema::try_from(input.abac_input.schema) {
        debug!("Schema: {schemafile_string}");
        let validator = Validator::new(schema.clone());
        let mut policyset = PolicySet::new();
        let policy: Policy = input.abac_input.policy.into();
        policyset.add(policy).unwrap();
        if passes_policyset_validation(&validator, &policyset) {
            let ffi = CedarLeanFfi::new();
            for (request, partial_request) in input
                .abac_input
                .requests
                .into_iter()
                .zip(input.partial_requests)
            {
                let request: Request = request.into();
                if passes_request_validation(&validator, &request) {
                    test_tpe_is_authorized_equiv(
                        &ffi,
                        &schema,
                        &policyset,
                        &partial_request,
                        &input.partial_entities,
                    );
                }
            }
        }
    }
});
