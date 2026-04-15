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
    tpe::{TpeFuzzTargetInput, passes_policyset_validation, passes_request_validation},
};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{
    PartialEntities, PartialRequest, Policy, PolicyId, PolicySet, Request, Schema, Validator,
    pst::{Clause, Expr, UnaryOp},
};
use log::debug;
use std::convert::TryFrom;
use std::{collections::HashSet, sync::Arc};

/// Compare Rust and Lean TPE outputs for a single partial request.
fn test_tpe_is_authorized_equiv(
    ffi: &CedarLeanFfi,
    schema: &Schema,
    policies: &PolicySet,
    partial_request: &PartialRequest,
    partial_entities: &PartialEntities,
) {
    // Run Rust TPE
    let maybe_rust_resp = policies.tpe(partial_request, partial_entities, schema);

    // Run Lean TPE
    let maybe_lean_resp =
        ffi.is_authorized_partial(policies, partial_request, partial_entities, schema);

    let (rust_resp, lean_resp) = match (maybe_rust_resp, maybe_lean_resp) {
        (Ok(r), Ok(l)) => (r, l),
        (Err(_), Err(_)) => return,
        (Ok(r), Err(e)) => panic!(
            "Got Lean TPE error, but Rust returned response.\nRust: {:?}\n, Lean: {}",
            r, e
        ),
        (Err(e), Ok(l)) => panic!(
            "Got Rust TPE error, but Lean returned response.\nRust: {}\n, Lean: {:?}",
            e, l
        ),
    };

    let rust_inner = rust_resp.as_ref();

    // Compare decisions
    assert_eq!(
        rust_inner.decision(),
        lean_resp.decision,
        "TPE decision mismatch"
    );

    // Compare policy categorizations (comparing sets of policy IDs)
    let to_set =
        |iter: Box<dyn Iterator<Item = &cedar_policy_core::tpe::response::ResidualPolicy> + '_>| {
            iter.map(|p| PolicyId::new(p.get_policy_id().as_ref()))
                .collect::<HashSet<PolicyId>>()
        };
    // The satisified forbids/permits match.
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
    // Rust only returns false_permits, which should be the union of the
    // false_permits and error_permits of the Lean side.
    assert_eq!(
        to_set(Box::new(rust_inner.false_permits())),
        &lean_resp.false_permits | &lean_resp.error_permits,
        "rust false_permits mismatch with false permits union error permits"
    );
    // Same for the false_forbids and error_forbids. The Rust side puts the policy ID
    // in false_forbids for all Effect::Forbid policies that result in false or error.
    assert_eq!(
        to_set(Box::new(rust_inner.false_forbids())),
        &lean_resp.false_forbids | &lean_resp.error_forbids,
        "rust false_forbids mismatch with false forbids union error forbids"
    );
    // The policies with residuals match on both sides.
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
    let rust_residual_map: std::collections::HashMap<String, Expr> = rust_resp
        .residual_policies()
        .map(|rp| {
            let id: String = rp.id().to_string();
            let pst = rp
                .to_pst()
                .expect("policy->pst conversion should succeeed for residuals");
            // Residual should only have one clause
            let clause = match pst.body().clauses().as_slice() {
                [Clause::When(x)] => x.clone(),
                [Clause::Unless(x)] => Arc::new(Expr::UnaryOp {
                    op: UnaryOp::Not,
                    expr: x.clone(),
                }),
                _ => panic!(""),
            };
            (id, Arc::unwrap_or_clone(clause))
        })
        .collect();

    for lean_rp in &lean_resp.residuals {
        let lean_pst = Expr::try_from(lean_rp.residual.clone())
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
