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
use cedar_drt::*;
use cedar_drt_inner::fuzz_target;
use cedar_drt_inner::*;
use cedar_policy_core::ast::Context;
use cedar_policy_core::ast::Effect;
use cedar_policy_core::ast::Expr;
use cedar_policy_core::ast::Policy;
use cedar_policy_core::ast::PolicyID;
use cedar_policy_core::ast::PolicySet;
use cedar_policy_core::ast::Request;
use cedar_policy_core::ast::RestrictedExpr;
use cedar_policy_core::entities::Entities;
use cedar_policy_core::extensions::Extensions;
use cedar_testing::cedar_test_impl::RustEngine;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use serde::Serialize;

#[derive(Debug, Clone, Serialize)]
struct FuzzTargetInput {
    policies: PolicySet,
}

#[derive(Debug, Clone)]
pub struct PolicySpec {
    effect: Effect,
    kind: PolicyKind,
}

impl PolicySpec {
    pub fn policy(&self, id: String) -> Policy {
        let when = match self.kind {
            PolicyKind::True => Expr::val(true),
            PolicyKind::False => Expr::val(false),
            PolicyKind::Error => Expr::add(Expr::val(1), Expr::val(false)),
            PolicyKind::Residual => Expr::get_attr(Expr::var(ast::Var::Context), "unknown".into()),
        };
        Policy::from_when_clause(self.effect, when, PolicyID::from_string(id), None)
    }
}

impl Arbitrary<'_> for PolicySpec {
    fn arbitrary(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let effect = u.arbitrary()?;
        let kind = u.arbitrary()?;
        Ok(Self { effect, kind })
    }
}

#[derive(Debug, Clone, Copy, Arbitrary)]
enum PolicyKind {
    True,
    False,
    Error,
    Residual,
}

impl Arbitrary<'_> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let mut policies = PolicySet::new();

        let len = u.arbitrary_len::<PolicySpec>()?;

        for i in 0..len {
            let id = format!("{i}");
            let spec: PolicySpec = u.arbitrary()?;
            let policy = spec.policy(id);
            policies.add(policy).unwrap();
        }

        Ok(Self { policies })
    }
}

fn build_request() -> Request {
    let principal = r#"Principal::"alice""#.parse().unwrap();
    let action = r#"Action::"read""#.parse().unwrap();
    let resource = r#"Resource::"photo""#.parse().unwrap();
    use std::iter::once;
    let context = Context::from_pairs(
        once((
            "unknown".into(),
            RestrictedExpr::call_extension_fn(
                "unknown".parse().unwrap(),
                once(RestrictedExpr::val("a")),
            ),
        )),
        Extensions::all_available(),
    )
    .unwrap();

    Request::new::<cedar_policy_core::ast::RequestSchemaAllPass>(
        (principal, None),
        (action, None),
        (resource, None),
        context,
        None,
        Extensions::all_available(),
    )
    .unwrap()
}

fuzz_target! {|input: FuzzTargetInput| {
        let request = build_request();
        let entities = Entities::new();
        let def_impl = LeanDefinitionalEngine::new();
        let prod_impl = RustEngine::new();
        let def_answer = def_impl.partial_is_authorized(&request, &entities, &input.policies).expect("Lean engine failed to produce a repsonse: ");
        let prod_answer = prod_impl.partial_is_authorized(&request, &entities, &input.policies).expect("Rust engine failed to produce a response: ");
        assert_eq!(def_answer, prod_answer);
    }
}
