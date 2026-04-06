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
    tpe::{TpeFuzzTargetInput, passes_request_validation, passes_validation},
};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{
    PartialEntities, PartialRequest, Policy, PolicyId, PolicySet, Request, Schema, Validator,
};
use cedar_policy_core::pst;
use log::debug;
use std::collections::HashSet;
use std::convert::TryFrom;

/// Compare Rust and Lean TPE outputs for a single partial request.
fn compare_tpe_outputs(
    ffi: &CedarLeanFfi,
    schema: &Schema,
    policies: &PolicySet,
    partial_request: &PartialRequest,
    partial_entities: &PartialEntities,
) {
    // Run Rust TPE
    let rust_resp = match policies.tpe(partial_request, partial_entities, schema) {
        Ok(r) => r,
        Err(_) => return,
    };

    // Run Lean TPE
    let lean_resp =
        match ffi.is_authorized_partial(policies, partial_request, partial_entities, schema) {
            Ok(r) => r,
            Err(_) => return,
        };

    let rust_inner = rust_resp.as_ref();

    // Compare decisions
    assert_eq!(
        rust_inner.decision(),
        lean_resp.decision,
        "TPE decision mismatch"
    );

    // Compare policy categorizations
    let to_set =
        |iter: Box<dyn Iterator<Item = &cedar_policy_core::tpe::response::ResidualPolicy> + '_>| {
            iter.map(|p| PolicyId::new(p.get_policy_id().as_ref()))
                .collect::<HashSet<PolicyId>>()
        };
    assert_eq!(
        to_set(Box::new(rust_inner.satisfied_permits())),
        lean_resp.satisfied_permits,
        "satisfied_permits mismatch"
    );
    assert_eq!(
        to_set(Box::new(rust_inner.satisfied_forbids())),
        lean_resp.satisfied_forbids,
        "satisfied_forbids mismatch"
    );
    assert_eq!(
        to_set(Box::new(rust_inner.false_permits())),
        &lean_resp.false_permits | &lean_resp.error_permits,
        "false_permits mismatch (Rust merges errors into false)"
    );
    assert_eq!(
        to_set(Box::new(rust_inner.false_forbids())),
        &lean_resp.false_forbids | &lean_resp.error_forbids,
        "false_forbids mismatch (Rust merges errors into false)"
    );
    assert_eq!(
        to_set(Box::new(rust_inner.residual_permits())),
        lean_resp.residual_permits,
        "residual_permits mismatch"
    );
    assert_eq!(
        to_set(Box::new(rust_inner.residual_forbids())),
        lean_resp.residual_forbids,
        "residual_forbids mismatch"
    );

    // Compare residual expressions by policy ID via PST
    let rust_residual_map: std::collections::HashMap<String, pst::Expr> = rust_inner
        .residual_policies()
        .map(|rp| {
            let id = rp.get_policy_id().to_string();
            let ast_expr = cedar_policy_core::ast::Expr::from(rp.get_residual().as_ref().clone());
            let pst_expr = pst::Expr::try_from(ast_expr)
                .expect("ast->pst conversion should succeed for residuals");
            (id, pst_expr)
        })
        .collect();

    for lean_rp in &lean_resp.residuals {
        let lean_pst = pst::Expr::try_from(lean_rp.residual.clone())
            .expect("lean residual->pst conversion should succeed");
        let id_str = lean_rp.id.to_string();
        let rust_pst = rust_residual_map.get(&id_str).unwrap_or_else(|| {
            panic!(
                "Lean returned residual for policy {id_str:?} but Rust did not.\n\
                 Rust residual IDs: {:?}",
                rust_residual_map.keys().collect::<Vec<_>>()
            )
        });
        assert_eq!(
            rust_pst, &lean_pst,
            "Residual expression mismatch for policy {id_str:?}\n\
             Rust PST: {rust_pst:?}\nLean PST: {lean_pst:?}"
        );
    }
}

fuzz_target!(|input: TpeFuzzTargetInput| {
    initialize_log();
    let schemafile_string = input.abac_input.schema.schemafile_string();
    if let Ok(schema) = Schema::try_from(input.abac_input.schema) {
        debug!("Schema: {schemafile_string}");
        let validator = Validator::new(schema.clone());
        let mut policyset = PolicySet::new();
        let policy: Policy = input.abac_input.policy.into();
        policyset.add(policy).unwrap();
        if passes_validation(&validator, &policyset) {
            let ffi = CedarLeanFfi::new();
            for (request, partial_request) in input
                .abac_input
                .requests
                .into_iter()
                .zip(input.partial_requests)
            {
                let request: Request = request.into();
                if passes_request_validation(&validator, &request) {
                    compare_tpe_outputs(
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
