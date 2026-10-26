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

//! The authorizer (`Cedar/Spec/Authorizer.lean`).

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::entities::*;
use super::evaluator::*;
use super::expr::*;
use super::request::*;
use super::value::*;

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Effect {
    Permit,
    Forbid,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub struct Policy {
    pub id: Str,
    pub effect: Effect,
    /// Scope and conditions as one expression (`Cedar.Spec.Policy.toExpr`)
    pub condition: Expr,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Decision {
    Allow,
    Deny,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub struct Response {
    pub decision: Decision,
    /// Sorted, without duplicates
    pub determining_policies: List<Str>,
    /// Sorted, without duplicates
    pub erroring_policies: List<Str>,
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_permit(e)))]
pub fn is_permit(e: &Effect) -> bool {
    match e {
        Effect::Permit => true,
        Effect::Forbid => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns satisfied(p, req, es)))]
pub fn satisfied(p: &Policy, req: &Request, es: &Entities) -> bool {
    match evaluate(&p.condition, req, es) {
        Ok(Value::Prim(Prim::Bool(true))) => true,
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns has_error(p, req, es)))]
pub fn has_error(p: &Policy, req: &Request, es: &Entities) -> bool {
    match evaluate(&p.condition, req, es) {
        Ok(_) => false,
        Err(_) => true,
    }
}

/// The IDs of the satisfied policies with the given effect.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns satisfied_policies(permit, ps, req, es)))]
pub fn satisfied_policies(
    permit: bool,
    ps: &List<Policy>,
    req: &Request,
    es: &Entities,
) -> List<Str> {
    decreases!(ps);
    match ps {
        List::Nil => List::Nil,
        List::Cons(p, rest) => {
            let rest_ids = satisfied_policies(permit, rest, req, es);
            if is_permit(&p.effect) == permit && satisfied(p, req, es) {
                List::Cons(clone_str(&p.id), Box::new(rest_ids))
            } else {
                rest_ids
            }
        }
    }
}

/// The IDs of the policies that produce an error.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns error_policies(ps, req, es)))]
pub fn error_policies(ps: &List<Policy>, req: &Request, es: &Entities) -> List<Str> {
    decreases!(ps);
    match ps {
        List::Nil => List::Nil,
        List::Cons(p, rest) => {
            let rest_ids = error_policies(rest, req, es);
            if has_error(p, req, es) {
                List::Cons(clone_str(&p.id), Box::new(rest_ids))
            } else {
                rest_ids
            }
        }
    }
}

/// `Cedar.Spec.isAuthorized`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns is_authorized(req, es, ps)))]
pub fn is_authorized(req: &Request, es: &Entities, ps: &List<Policy>) -> Response {
    let forbids = strs_canonicalize(satisfied_policies(false, ps, req, es));
    let permits = strs_canonicalize(satisfied_policies(true, ps, req, es));
    let erroring_policies = strs_canonicalize(error_policies(ps, req, es));
    match (&forbids, &permits) {
        (List::Nil, List::Cons(_, _)) => Response {
            decision: Decision::Allow,
            determining_policies: permits,
            erroring_policies,
        },
        _ => Response {
            decision: Decision::Deny,
            determining_policies: forbids,
            erroring_policies,
        },
    }
}
