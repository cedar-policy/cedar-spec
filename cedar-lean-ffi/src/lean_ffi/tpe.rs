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

use crate::datatypes::{self as datatypes, ResultDef, TimedDef, TimedResult, TpeResponseInner};
use crate::err::FfiError;
use crate::messages::proto;

use cedar_policy::{PartialEntities, PartialRequest, PolicySet, Schema};

use super::{CedarLeanFfi, call_lean_ffi_takes_protobuf, isAuthorizedPartial};

impl CedarLeanFfi {
    /// Calls the Lean backend and performs type-aware partial evaluation of the partial request,
    /// given a policy set, a schema and a set of partial entities.
    /// This function returns a [`Result`] that is an [`FfiError`] when the FFI call failed,
    /// otherwise it is a [`TimedResult`] wrapping the response [`datatypes::TpeResponse`].
    pub fn is_authorized_partial_timed(
        &self,
        policies: &PolicySet,
        request: &PartialRequest,
        entities: &PartialEntities,
        schema: &Schema,
    ) -> Result<TimedResult<datatypes::TpeResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                isAuthorizedPartial,
                &proto::PartialAuthorizationRequest::new(schema, request, entities, policies),
            )
        };
        match response
            .as_borrowed()
            .deserialize_into::<ResultDef<TimedDef<ResultDef<TpeResponseInner>>>>()?
        {
            ResultDef::Ok(resp) => match resp.data {
                ResultDef::Ok(inner) => {
                    let tdef = TimedDef {
                        data: datatypes::TpeResponse::from_inner(inner)?,
                        duration: resp.duration,
                    };
                    Ok(TimedResult::from_def(tdef))
                }
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            },
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }

    /// Takes the result out of [`Self::is_authorized_partial_timed`].
    pub fn is_authorized_partial(
        &self,
        policies: &PolicySet,
        request: &PartialRequest,
        entities: &PartialEntities,
        schema: &Schema,
    ) -> Result<datatypes::TpeResponse, FfiError> {
        Ok(self
            .is_authorized_partial_timed(policies, request, entities, schema)?
            .take_result())
    }
}

#[cfg(test)]
mod test {
    /***************** Copy Extern Block so that Tests are also linked with lean code *****************/
    #[allow(clippy::duplicated_attributes)]
    #[link(name = "Cedar_Cedar", kind = "static")]
    #[link(name = "Cedar_Cedar_SymCC", kind = "static")]
    #[link(name = "Cedar_Protobuf", kind = "static")]
    #[link(name = "Cedar_CedarProto", kind = "static")]
    #[link(name = "batteries_Batteries", kind = "static")]
    #[link(name = "Cedar_CedarFFI", kind = "static")]
    unsafe extern "C" {}

    use cedar_policy::{
        Context, EntityTypeName, EntityUid, PartialEntities, PartialEntity, PartialEntityUid,
        PartialRequest, Policy, PolicyId, PolicySet, RestrictedExpression, Schema,
    };

    use std::collections::{BTreeMap, HashSet};
    use std::str::FromStr;

    use crate::CedarLeanFfi;

    /// Helper to compare Rust and Lean TPE responses: decision, policy categorizations,
    /// and residual expressions (via PST comparison).
    ///
    /// Uses explicit checks with `eprintln!` instead of `assert_eq!` so that failure
    /// messages are visible even when the Lean runtime's `exit_on_panic` is active.
    /// Collects all mismatches and panics once at the end.
    ///
    /// When using this, re-run tests with --nocapture to get output.
    fn assert_tpe_responses_match(
        rust: &cedar_policy::TpeResponse<'_>,
        lean: &crate::datatypes::TpeResponse,
    ) {
        let mut errors = Vec::new();
        let rust_inner = rust.as_ref();

        // Compare decisions
        if lean.decision != rust_inner.decision() {
            errors.push(format!(
                "decision mismatch: lean={:?}, rust={:?}",
                lean.decision,
                rust_inner.decision()
            ));
        }

        // Compare policy categorizations
        let policy_ids = |iter: Box<
            dyn Iterator<Item = &cedar_policy_core::tpe::response::ResidualPolicy> + '_,
        >|
         -> HashSet<PolicyId> {
            iter.map(|p| PolicyId::new(p.get_policy_id().as_ref()))
                .collect()
        };

        macro_rules! check_set {
            ($lean_field:expr, $rust_iter:expr, $name:expr) => {
                let rust_set = policy_ids(Box::new($rust_iter));
                if $lean_field != rust_set {
                    errors.push(format!(
                        "{} mismatch:\n  lean={:?}\n  rust={:?}",
                        $name, $lean_field, rust_set
                    ));
                }
            };
        }
        check_set!(
            lean.satisfied_permits,
            rust_inner.satisfied_permits(),
            "satisfied_permits"
        );
        check_set!(
            lean.satisfied_forbids,
            rust_inner.satisfied_forbids(),
            "satisfied_forbids"
        );
        check_set!(
            lean.false_permits,
            rust_inner.false_permits(),
            "false_permits"
        );
        check_set!(
            lean.false_forbids,
            rust_inner.false_forbids(),
            "false_forbids"
        );
        check_set!(
            lean.residual_permits,
            rust_inner.residual_permits(),
            "residual_permits"
        );
        check_set!(
            lean.residual_forbids,
            rust_inner.residual_forbids(),
            "residual_forbids"
        );

        // Compare residual expressions via PST
        use cedar_policy_core::pst;
        let rust_residual_map: std::collections::HashMap<String, pst::Expr> = rust_inner
            .residual_policies()
            .map(|rp| {
                let id = rp.get_policy_id().to_string();
                let ast_expr =
                    cedar_policy_core::ast::Expr::from(rp.get_residual().as_ref().clone());
                let pst_expr = pst::Expr::try_from(ast_expr)
                    .expect("ast->pst conversion should succeed for residuals");
                (id, pst_expr)
            })
            .collect();

        for lean_rp in &lean.residuals {
            let lean_pst = pst::Expr::try_from(lean_rp.residual.clone())
                .expect("lean residual->pst conversion should succeed");
            let id_str = lean_rp.id.to_string();
            match rust_residual_map.get(&id_str) {
                None => {
                    errors.push(format!(
                        "Lean returned residual for policy {id_str:?} but Rust did not.\n\
                         Rust residual IDs: {:?}",
                        rust_residual_map.keys().collect::<Vec<_>>()
                    ));
                }
                Some(rust_pst) if rust_pst != &lean_pst => {
                    errors.push(format!(
                        "Residual expression mismatch for policy {id_str:?}\n\
                         Rust PST: {rust_pst:?}\n\
                         Lean PST: {lean_pst:?}"
                    ));
                }
                _ => {}
            }
        }

        if !errors.is_empty() {
            let msg = errors.join("\n\n");
            // Use eprint + exit instead of panic! because Lean's `exit_on_panic`
            // aborts the process before Rust can print the panic message.
            eprint!("TPE response comparison failed:\n{msg}\n");
            std::process::exit(1);
        }
    }

    fn tpe_schema() -> Schema {
        Schema::from_cedarschema_str(
            r#"
            entity Account = {
                balance: Long,
                owner: String,
            } tags Set<String>;
            entity User in [Account] = {
                name: String,
                age: Long,
            };
            action transfer appliesTo {
                principal: [User],
                resource: [Account],
                context: {
                    amount: Long,
                    memo: String,
                }
            };
        "#,
        )
        .expect("TPE test schema failed to parse")
        .0
    }

    /// Fully concrete partial authorization: all fields known, expect a definite decision
    #[test]
    fn test_is_authorized_partial_fully_concrete() {
        let schema = tpe_schema();
        let policies = PolicySet::from_str(
            r#"
            permit(principal, action == Action::"transfer", resource)
            when { context.amount < 1000 };
            "#,
        )
        .unwrap();

        let principal =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"User::"alice""#).unwrap());
        let action = EntityUid::from_str(r#"Action::"transfer""#).unwrap();
        let resource =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"Account::"checking""#).unwrap());
        let context = Context::from_pairs([
            ("amount".into(), RestrictedExpression::new_long(500)),
            (
                "memo".into(),
                RestrictedExpression::new_string("rent".into()),
            ),
        ])
        .unwrap();
        let request =
            PartialRequest::new(principal, action, resource, Some(context), &schema).unwrap();

        let account = PartialEntity::new(
            EntityUid::from_str(r#"Account::"checking""#).unwrap(),
            Some(BTreeMap::from([
                ("balance".into(), RestrictedExpression::new_long(10000)),
                (
                    "owner".into(),
                    RestrictedExpression::new_string("alice".into()),
                ),
            ])),
            Some(HashSet::new()),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let user = PartialEntity::new(
            EntityUid::from_str(r#"User::"alice""#).unwrap(),
            Some(BTreeMap::from([
                (
                    "name".into(),
                    RestrictedExpression::new_string("Alice".into()),
                ),
                ("age".into(), RestrictedExpression::new_long(30)),
            ])),
            Some(HashSet::from([EntityUid::from_str(
                r#"Account::"checking""#,
            )
            .unwrap()])),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let entities = PartialEntities::from_partial_entities([account, user], &schema).unwrap();

        // First verify Rust TPE accepts this input
        let rust_resp = policies
            .tpe(&request, &entities, &schema)
            .expect("Rust TPE call failed");

        let ffi = CedarLeanFfi::new();
        let lean_resp = ffi
            .is_authorized_partial(&policies, &request, &entities, &schema)
            .expect("Lean FFI call failed");

        assert_tpe_responses_match(&rust_resp, &lean_resp);
        // Fully concrete: definite Allow, one satisfied permit, nothing residual
        assert_eq!(lean_resp.decision, Some(cedar_policy::Decision::Allow));
        assert_eq!(lean_resp.satisfied_permits.len(), 1);
        assert!(lean_resp.residual_permits.is_empty());
        assert!(lean_resp.error_permits.is_empty());
        assert!(lean_resp.false_forbids.is_empty() || lean_resp.satisfied_forbids.is_empty());
    }

    /// Partial authorization with unknown resource eid: expect residuals
    #[test]
    fn test_is_authorized_partial_unknown_resource() {
        let schema = tpe_schema();
        let policies = PolicySet::from_str(
            r#"
            permit(principal, action == Action::"transfer", resource)
            when { context.amount < resource.balance };
            "#,
        )
        .unwrap();

        let principal =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"User::"alice""#).unwrap());
        let action = EntityUid::from_str(r#"Action::"transfer""#).unwrap();
        let resource = PartialEntityUid::new(
            EntityTypeName::from_str("Account").unwrap(),
            None, // unknown resource eid
        );
        let context = Context::from_pairs([
            ("amount".into(), RestrictedExpression::new_long(500)),
            (
                "memo".into(),
                RestrictedExpression::new_string("rent".into()),
            ),
        ])
        .unwrap();
        let request =
            PartialRequest::new(principal, action, resource, Some(context), &schema).unwrap();

        let user = PartialEntity::new(
            EntityUid::from_str(r#"User::"alice""#).unwrap(),
            Some(BTreeMap::from([
                (
                    "name".into(),
                    RestrictedExpression::new_string("Alice".into()),
                ),
                ("age".into(), RestrictedExpression::new_long(30)),
            ])),
            Some(HashSet::new()),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let entities = PartialEntities::from_partial_entities([user], &schema).unwrap();

        let rust_resp = policies
            .tpe(&request, &entities, &schema)
            .expect("Rust TPE call failed");

        let ffi = CedarLeanFfi::new();
        let lean_resp = ffi
            .is_authorized_partial(&policies, &request, &entities, &schema)
            .expect("FFI call failed");

        assert_tpe_responses_match(&rust_resp, &lean_resp);
        // Unknown resource → can't evaluate resource.balance → residual
        assert_eq!(lean_resp.decision, None);
        assert!(lean_resp.satisfied_permits.is_empty());
        assert!(!lean_resp.residual_permits.is_empty());
        assert!(!lean_resp.residuals.is_empty());
    }

    /// Partial authorization with unknown context: expect residuals
    #[test]
    fn test_is_authorized_partial_unknown_context() {
        let schema = tpe_schema();
        let policies = PolicySet::from_str(
            r#"
            permit(principal, action == Action::"transfer", resource)
            when { context.amount < 1000 };
            "#,
        )
        .unwrap();

        let principal =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"User::"alice""#).unwrap());
        let action = EntityUid::from_str(r#"Action::"transfer""#).unwrap();
        let resource =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"Account::"checking""#).unwrap());
        // No context → unknown
        let request = PartialRequest::new(principal, action, resource, None, &schema).unwrap();

        let account = PartialEntity::new(
            EntityUid::from_str(r#"Account::"checking""#).unwrap(),
            Some(BTreeMap::from([
                ("balance".into(), RestrictedExpression::new_long(10000)),
                (
                    "owner".into(),
                    RestrictedExpression::new_string("alice".into()),
                ),
            ])),
            Some(HashSet::new()),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let user = PartialEntity::new(
            EntityUid::from_str(r#"User::"alice""#).unwrap(),
            Some(BTreeMap::from([
                (
                    "name".into(),
                    RestrictedExpression::new_string("Alice".into()),
                ),
                ("age".into(), RestrictedExpression::new_long(30)),
            ])),
            Some(HashSet::from([EntityUid::from_str(
                r#"Account::"checking""#,
            )
            .unwrap()])),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let entities = PartialEntities::from_partial_entities([account, user], &schema).unwrap();

        let rust_resp = policies
            .tpe(&request, &entities, &schema)
            .expect("Rust TPE call failed");

        let ffi = CedarLeanFfi::new();
        let lean_resp = ffi
            .is_authorized_partial(&policies, &request, &entities, &schema)
            .expect("FFI call failed");

        assert_tpe_responses_match(&rust_resp, &lean_resp);
        // Unknown context → can't evaluate context.amount → residual
        assert_eq!(lean_resp.decision, None);
        assert!(!lean_resp.residual_permits.is_empty());
        assert!(!lean_resp.residuals.is_empty());
    }

    /// Partial authorization: forbid always satisfied → definite Deny even with unknowns
    #[test]
    fn test_is_authorized_partial_definite_deny() {
        let schema = tpe_schema();
        let policies = PolicySet::from_str(
            r#"
            forbid(principal, action, resource);
            permit(principal, action == Action::"transfer", resource)
            when { context.amount < resource.balance };
            "#,
        )
        .unwrap();

        let principal =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"User::"alice""#).unwrap());
        let action = EntityUid::from_str(r#"Action::"transfer""#).unwrap();
        let resource =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"Account::"checking""#).unwrap());
        let context = Context::from_pairs([
            ("amount".into(), RestrictedExpression::new_long(500)),
            (
                "memo".into(),
                RestrictedExpression::new_string("test".into()),
            ),
        ])
        .unwrap();
        let request =
            PartialRequest::new(principal, action, resource, Some(context), &schema).unwrap();

        let user = PartialEntity::new(
            EntityUid::from_str(r#"User::"alice""#).unwrap(),
            Some(BTreeMap::from([
                (
                    "name".into(),
                    RestrictedExpression::new_string("Alice".into()),
                ),
                ("age".into(), RestrictedExpression::new_long(30)),
            ])),
            Some(HashSet::from([EntityUid::from_str(
                r#"Account::"checking""#,
            )
            .unwrap()])),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        // Resource entity with unknown attrs — can't evaluate resource.balance
        let account = PartialEntity::new(
            EntityUid::from_str(r#"Account::"checking""#).unwrap(),
            None, // unknown attrs
            Some(HashSet::new()),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let entities = PartialEntities::from_partial_entities([user, account], &schema).unwrap();

        let rust_resp = policies
            .tpe(&request, &entities, &schema)
            .expect("Rust TPE call failed");

        let ffi = CedarLeanFfi::new();
        let lean_resp = ffi
            .is_authorized_partial(&policies, &request, &entities, &schema)
            .expect("FFI call failed");

        assert_tpe_responses_match(&rust_resp, &lean_resp);
        // Unconditional forbid → definite Deny; permit is residual due to unknown attrs
        assert_eq!(lean_resp.decision, Some(cedar_policy::Decision::Deny));
        assert!(!lean_resp.satisfied_forbids.is_empty());
        assert!(!lean_resp.residual_permits.is_empty());
    }

    /// Multiple policies: mix of satisfied, false, and residual in both permit and forbid
    #[test]
    fn test_is_authorized_partial_multi_policy() {
        let schema = tpe_schema();
        let mut policies = PolicySet::new();
        policies
            .add(
                Policy::parse(
                    Some(PolicyId::new("always-permit")),
                    r#"permit(principal, action, resource);"#,
                )
                .unwrap(),
            )
            .unwrap();
        policies
            .add(
                Policy::parse(
                    Some(PolicyId::new("condition-on-context")),
                    r#"permit(principal, action, resource) when { context.amount > 9999 };"#,
                )
                .unwrap(),
            )
            .unwrap();
        policies
            .add(
                Policy::parse(
                    Some(PolicyId::new("always-false-forbid")),
                    r#"forbid(principal, action, resource) when { false };"#,
                )
                .unwrap(),
            )
            .unwrap();
        policies
            .add(
                Policy::parse(
                    Some(PolicyId::new("residual-forbid")),
                    r#"forbid(principal, action, resource) when { context.memo == "blocked" };"#,
                )
                .unwrap(),
            )
            .unwrap();

        let principal =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"User::"alice""#).unwrap());
        let action = EntityUid::from_str(r#"Action::"transfer""#).unwrap();
        let resource =
            PartialEntityUid::from_concrete(EntityUid::from_str(r#"Account::"checking""#).unwrap());
        // Unknown context
        let request = PartialRequest::new(principal, action, resource, None, &schema).unwrap();

        let account = PartialEntity::new(
            EntityUid::from_str(r#"Account::"checking""#).unwrap(),
            Some(BTreeMap::from([
                ("balance".into(), RestrictedExpression::new_long(10000)),
                (
                    "owner".into(),
                    RestrictedExpression::new_string("alice".into()),
                ),
            ])),
            Some(HashSet::new()),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let user = PartialEntity::new(
            EntityUid::from_str(r#"User::"alice""#).unwrap(),
            Some(BTreeMap::from([
                (
                    "name".into(),
                    RestrictedExpression::new_string("Alice".into()),
                ),
                ("age".into(), RestrictedExpression::new_long(30)),
            ])),
            Some(HashSet::from([EntityUid::from_str(
                r#"Account::"checking""#,
            )
            .unwrap()])),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let entities = PartialEntities::from_partial_entities([account, user], &schema).unwrap();

        let rust_resp = policies
            .tpe(&request, &entities, &schema)
            .expect("Rust TPE call failed");

        let ffi = CedarLeanFfi::new();
        let lean_resp = ffi
            .is_authorized_partial(&policies, &request, &entities, &schema)
            .expect("FFI call failed");

        assert_tpe_responses_match(&rust_resp, &lean_resp);

        // With unknown context:
        // - "always-permit" (permit with no when) → satisfied (scope matches, no condition)
        // - "condition-on-context" (permit when context.amount > 9999) → residual
        // - "always-false-forbid" (forbid when false) → false
        // - "residual-forbid" (forbid when context.memo == "blocked") → residual
        assert!(
            lean_resp
                .satisfied_permits
                .contains(&PolicyId::new("always-permit"))
        );
        assert!(
            lean_resp
                .residual_permits
                .contains(&PolicyId::new("condition-on-context"))
        );
        assert!(
            lean_resp
                .false_forbids
                .contains(&PolicyId::new("always-false-forbid"))
        );
        assert!(
            lean_resp
                .residual_forbids
                .contains(&PolicyId::new("residual-forbid"))
        );
        assert!(lean_resp.error_permits.is_empty());
        assert!(lean_resp.error_forbids.is_empty());
        assert!(lean_resp.satisfied_forbids.is_empty());
        assert!(lean_resp.false_permits.is_empty());

        // With a satisfied permit and residual forbid → no definite decision
        assert_eq!(lean_resp.decision, None);
        // 4 policies → 4 residuals
        assert_eq!(lean_resp.residuals.len(), 4);
    }

    /// Regression: enum entity type with `principal is a` scope and unknown principal eid.
    /// Rust TPE simplifies away the `is` check and keeps the `in` (since the type is
    /// already constrained),
    /// Lean keeps both checks it in the residual.
    ///
    /// Both are semantically correct.
    #[test]
    fn test_is_authorized_partial_enum_entity_scope_residual() {
        let schema = Schema::from_cedarschema_str(
            r#"
            entity a enum [""];
            action "action" appliesTo {
                principal: [a],
                resource: [a],
                context: {}
            };
            "#,
        )
        .expect("schema parse failed")
        .0;

        let policies = PolicySet::from_str(
            r#"
            forbid(principal is a, action == Action::"action", resource == a::"")
            when { true };
            "#,
        )
        .unwrap();

        let principal = PartialEntityUid::new(
            EntityTypeName::from_str("a").unwrap(),
            None, // unknown principal eid
        );
        let action = EntityUid::from_str(r#"Action::"action""#).unwrap();
        let resource = PartialEntityUid::new(
            EntityTypeName::from_str("a").unwrap(),
            None, // unknown resource eid
        );
        let request = PartialRequest::new(principal, action, resource, None, &schema).unwrap();

        let entity_a = PartialEntity::new(
            EntityUid::from_str(r#"a::"" "#.trim()).unwrap(),
            None, // unknown attrs
            None, // unknown ancestors
            None, // unknown tags
            &schema,
        )
        .unwrap();
        let action_entity = PartialEntity::new(
            EntityUid::from_str(r#"Action::"action""#).unwrap(),
            Some(BTreeMap::new()),
            Some(HashSet::new()),
            Some(BTreeMap::new()),
            &schema,
        )
        .unwrap();
        let entities =
            PartialEntities::from_partial_entities([entity_a, action_entity], &schema).unwrap();

        let rust_resp = policies
            .tpe(&request, &entities, &schema)
            .expect("Rust TPE call failed");

        let ffi = CedarLeanFfi::new();
        let lean_resp = ffi
            .is_authorized_partial(&policies, &request, &entities, &schema)
            .expect("Lean FFI call failed");

        assert_tpe_responses_match(&rust_resp, &lean_resp);
    }
}
