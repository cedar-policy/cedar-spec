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

//! Test utilities for the typed-expression DRT target (issue #840).

use cedar_drt::typed_expr::{RunReport, run_typed_expr_drt};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{PolicySet, Schema};
use cedar_policy_core::ast;
use cedar_policy_core::validator::ValidatorSchema;

/// The four views of one input that the comparison needs: the core types the
/// Rust typechecker takes, and the public types the Lean FFI takes.
pub struct TypedExprInput {
    pub vschema: ValidatorSchema,
    pub policies: ast::PolicySet,
    pub ffi_schema: Schema,
    pub ffi_policies: PolicySet,
}

impl TypedExprInput {
    /// Build both views from one generated schema and policy set.
    ///
    /// Returns `None` when the generated input cannot be expressed in one of
    /// the two forms. That is a limitation of the generator plumbing, not a
    /// result, so it is skipped rather than reported.
    pub fn new(
        gen_schema: cedar_policy_generators::schema::Schema,
        ffi_policies: PolicySet,
    ) -> Option<Self> {
        let vschema: ValidatorSchema = gen_schema.clone().try_into().ok()?;
        let ffi_schema: Schema = gen_schema.try_into().ok()?;

        // Reparsed from source text rather than converted, so the two views
        // are produced by the two crates' own parsers.
        //
        // Parsed one policy at a time under its ORIGINAL id. Parsing the whole
        // set in one call assigns fresh `policy0`, `policy1`, ... ids and
        // discards the ids the input actually carries, which then fails to
        // align against the Lean side and reports every pair as unmatched.
        // Text round-tripping a policy set is not id-preserving.
        // Template-linked policies are out of scope for this target, matching
        // how `compare_validation_results` handles #945. They must be dropped
        // from BOTH sides: skipping them only on the Rust side leaves the Lean
        // side reporting pairs that never get compared, which surfaces as an
        // unmatched-environment harness problem rather than as a skip.
        let ffi_policies = {
            let mut keep = PolicySet::new();
            for p in ffi_policies.policies() {
                if p.template_id().is_some() {
                    continue;
                }
                keep.add(p.clone()).ok()?;
            }
            keep
        };

        let mut policies = ast::PolicySet::new();
        for p in ffi_policies.policies() {
            // Taken via AsRef rather than through Display, which escapes.
            let id: ast::PolicyID = AsRef::<ast::PolicyID>::as_ref(p.id()).clone();
            let parsed = cedar_policy_core::parser::parse_policy(Some(id), &p.to_string()).ok()?;
            policies.add_static(parsed).ok()?;
        }
        Some(Self {
            vschema,
            policies,
            ffi_schema,
            ffi_policies,
        })
    }
}

/// Compare the Rust and Lean typed expressions for one generated input.
///
/// Panics on a harness problem, which is a defect in this target rather than
/// a finding about either implementation. Findings are returned so the caller
/// decides whether to assert on them or tally them.
pub fn compare_typed_expressions(ffi: &CedarLeanFfi, input: &TypedExprInput) -> Option<RunReport> {
    let report = run_typed_expr_drt(
        ffi,
        &input.vschema,
        &input.policies,
        &input.ffi_schema,
        &input.ffi_policies,
    )
    .ok()?;

    assert!(
        report.harness_problems().is_empty(),
        "harness problems must be fixed before any finding is believable: {:?}",
        report.harness_problems()
    );

    Some(report)
}
