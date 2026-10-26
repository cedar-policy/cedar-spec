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

//! Policies (`Cedar/Spec/Policy.lean`) and their conversion to the authorizer's
//! `Policy` (ID, effect, condition expression).

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::authorizer::*;
use super::expr::*;
use super::ext;
use super::value::*;


// ---------------------------------------------------------------------------
// Data
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Scope {
    Any,
    Eq(EntityUID),
    Mem(EntityUID),
    Is(Name),
    IsMem(Name, EntityUID),
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum ActionScope {
    ActionScope(Scope),
    ActionInAny(List<EntityUID>),
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum ConditionKind {
    When,
    Unless,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub struct Condition {
    pub kind: ConditionKind,
    pub body: Expr,
}

/// `Cedar.Spec.Policy`: a static or template-linked policy.
#[cfg_attr(feature = "verus", verus_verify)]
pub struct LinkedPolicy {
    pub id: Str,
    pub effect: Effect,
    pub principal_scope: Scope,
    pub action_scope: ActionScope,
    pub resource_scope: Scope,
    pub condition: List<Condition>,
}

// ---------------------------------------------------------------------------
// Copying
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_effect(e)))]
pub fn clone_effect(e: &Effect) -> Effect {
    match e {
        Effect::Permit => Effect::Permit,
        Effect::Forbid => Effect::Forbid,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_pattern(p)))]
pub fn clone_pattern(p: &List<PatElem>) -> List<PatElem> {
    decreases!(p);
    match p {
        List::Nil => List::Nil,
        List::Cons(PatElem::Star, rest) => List::Cons(PatElem::Star, Box::new(clone_pattern(rest))),
        List::Cons(PatElem::JustChar(c), rest) => {
            List::Cons(PatElem::JustChar(*c), Box::new(clone_pattern(rest)))
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_unary_op(o)))]
pub fn clone_unary_op(o: &UnaryOp) -> UnaryOp {
    match o {
        UnaryOp::Not => UnaryOp::Not,
        UnaryOp::Neg => UnaryOp::Neg,
        UnaryOp::IsEmpty => UnaryOp::IsEmpty,
        UnaryOp::Like(p) => UnaryOp::Like(clone_pattern(p)),
        UnaryOp::Is(n) => UnaryOp::Is(clone_name(n)),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_binary_op(o)))]
pub fn clone_binary_op(o: &BinaryOp) -> BinaryOp {
    match o {
        BinaryOp::Eq => BinaryOp::Eq,
        BinaryOp::Mem => BinaryOp::Mem,
        BinaryOp::HasTag => BinaryOp::HasTag,
        BinaryOp::GetTag => BinaryOp::GetTag,
        BinaryOp::Less => BinaryOp::Less,
        BinaryOp::LessEq => BinaryOp::LessEq,
        BinaryOp::Add => BinaryOp::Add,
        BinaryOp::Sub => BinaryOp::Sub,
        BinaryOp::Mul => BinaryOp::Mul,
        BinaryOp::Contains => BinaryOp::Contains,
        BinaryOp::ContainsAll => BinaryOp::ContainsAll,
        BinaryOp::ContainsAny => BinaryOp::ContainsAny,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_var(v)))]
pub fn clone_var(v: &Var) -> Var {
    match v {
        Var::Principal => Var::Principal,
        Var::Action => Var::Action,
        Var::Resource => Var::Resource,
        Var::Context => Var::Context,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_expr(x)))]
pub fn clone_expr(x: &Expr) -> Expr {
    decreases!(x);
    match x {
        Expr::Lit(p) => Expr::Lit(clone_prim(p)),
        Expr::Var(v) => Expr::Var(clone_var(v)),
        Expr::Ite(x1, x2, x3) => Expr::Ite(
            Box::new(clone_expr(x1)),
            Box::new(clone_expr(x2)),
            Box::new(clone_expr(x3)),
        ),
        Expr::And(x1, x2) => Expr::And(Box::new(clone_expr(x1)), Box::new(clone_expr(x2))),
        Expr::Or(x1, x2) => Expr::Or(Box::new(clone_expr(x1)), Box::new(clone_expr(x2))),
        Expr::UnaryApp(o, x1) => Expr::UnaryApp(clone_unary_op(o), Box::new(clone_expr(x1))),
        Expr::BinaryApp(o, x1, x2) => Expr::BinaryApp(
            clone_binary_op(o),
            Box::new(clone_expr(x1)),
            Box::new(clone_expr(x2)),
        ),
        Expr::GetAttr(x1, a) => Expr::GetAttr(Box::new(clone_expr(x1)), clone_str(a)),
        Expr::HasAttr(x1, a) => Expr::HasAttr(Box::new(clone_expr(x1)), clone_str(a)),
        Expr::ExtHasAttr(x1, a, attrs) => {
            Expr::ExtHasAttr(Box::new(clone_expr(x1)), clone_str(a), clone_strs(attrs))
        }
        Expr::Set(xs) => Expr::Set(Box::new(clone_exprs(xs))),
        Expr::Record(axs) => Expr::Record(Box::new(clone_attr_exprs(axs))),
        Expr::Call(f, xs) => Expr::Call(ext::clone_extfun(f), Box::new(clone_exprs(xs))),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_exprs(xs)))]
pub fn clone_exprs(xs: &List<Expr>) -> List<Expr> {
    decreases!(xs);
    match xs {
        List::Nil => List::Nil,
        List::Cons(x, rest) => List::Cons(clone_expr(x), Box::new(clone_exprs(rest))),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_attr_exprs(axs)))]
pub fn clone_attr_exprs(axs: &List<(Str, Expr)>) -> List<(Str, Expr)> {
    decreases!(axs);
    match axs {
        List::Nil => List::Nil,
        List::Cons((a, x), rest) => List::Cons(
            (clone_str(a), clone_expr(x)),
            Box::new(clone_attr_exprs(rest)),
        ),
    }
}

// ---------------------------------------------------------------------------
// Policy expressions
// ---------------------------------------------------------------------------

/// `Expr.mkAnd`: like production's `Expr::and`, folds `lit && lit` to a literal
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns mk_and(x1, x2)))]
pub fn mk_and(x1: Expr, x2: Expr) -> Expr {
    match x1 {
        Expr::Lit(Prim::Bool(b1)) => match x2 {
            Expr::Lit(Prim::Bool(b2)) => Expr::Lit(Prim::Bool(b1 && b2)),
            x2 => Expr::And(Box::new(Expr::Lit(Prim::Bool(b1))), Box::new(x2)),
        },
        x1 => Expr::And(Box::new(x1), Box::new(x2)),
    }
}

/// `v == u`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns var_eq_uid(v, u)))]
pub fn var_eq_uid(v: Var, u: &EntityUID) -> Expr {
    Expr::BinaryApp(
        BinaryOp::Eq,
        Box::new(Expr::Var(v)),
        Box::new(Expr::Lit(Prim::EntityUID(clone_uid(u)))),
    )
}

/// `v in u`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns var_in_uid(v, u)))]
pub fn var_in_uid(v: Var, u: &EntityUID) -> Expr {
    Expr::BinaryApp(
        BinaryOp::Mem,
        Box::new(Expr::Var(v)),
        Box::new(Expr::Lit(Prim::EntityUID(clone_uid(u)))),
    )
}

/// `v is n`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns var_is(v, n)))]
pub fn var_is(v: Var, n: &Name) -> Expr {
    Expr::UnaryApp(UnaryOp::Is(clone_name(n)), Box::new(Expr::Var(v)))
}

/// `Scope.toExpr`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns scope_to_expr(s, v)))]
pub fn scope_to_expr(s: &Scope, v: &Var) -> Expr {
    match s {
        Scope::Any => Expr::Lit(Prim::Bool(true)),
        Scope::Eq(u) => var_eq_uid(clone_var(v), u),
        Scope::Mem(u) => var_in_uid(clone_var(v), u),
        Scope::Is(n) => var_is(clone_var(v), n),
        Scope::IsMem(n, u) => Expr::And(
            Box::new(var_is(clone_var(v), n)),
            Box::new(var_in_uid(clone_var(v), u)),
        ),
    }
}

/// The entity literals `[u1, ..., un]`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns uid_lits(us)))]
pub fn uid_lits(us: &List<EntityUID>) -> List<Expr> {
    decreases!(us);
    match us {
        List::Nil => List::Nil,
        List::Cons(u, rest) => List::Cons(Expr::Lit(Prim::EntityUID(clone_uid(u))), Box::new(uid_lits(rest))),
    }
}

/// `ActionScope.toExpr`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns action_scope_to_expr(s)))]
pub fn action_scope_to_expr(s: &ActionScope) -> Expr {
    match s {
        ActionScope::ActionScope(s) => scope_to_expr(s, &Var::Action),
        ActionScope::ActionInAny(us) => Expr::BinaryApp(
            BinaryOp::Mem,
            Box::new(Expr::Var(Var::Action)),
            Box::new(Expr::Set(Box::new(uid_lits(us)))),
        ),
    }
}

/// `Condition.toExpr`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns condition_to_expr(c)))]
pub fn condition_to_expr(c: &Condition) -> Expr {
    match c.kind {
        ConditionKind::When => clone_expr(&c.body),
        ConditionKind::Unless => Expr::UnaryApp(UnaryOp::Not, Box::new(clone_expr(&c.body))),
    }
}

/// `Conditions.toExpr`: the `mk_and` of the conditions, `true` if none
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns conditions_to_expr(cs)))]
pub fn conditions_to_expr(cs: &List<Condition>) -> Expr {
    decreases!(cs);
    match cs {
        List::Nil => Expr::Lit(Prim::Bool(true)),
        List::Cons(c, rest) => match &**rest {
            List::Nil => condition_to_expr(c),
            List::Cons(_, _) => mk_and(condition_to_expr(c), conditions_to_expr(rest)),
        },
    }
}

/// `Policy.toExpr`, which is production's `Policy::condition`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns policy_to_expr(p)))]
pub fn policy_to_expr(p: &LinkedPolicy) -> Expr {
    mk_and(
        scope_to_expr(&p.principal_scope, &Var::Principal),
        mk_and(
            action_scope_to_expr(&p.action_scope),
            mk_and(
                scope_to_expr(&p.resource_scope, &Var::Resource),
                conditions_to_expr(&p.condition),
            ),
        ),
    )
}

/// The authorizer's view of the policy
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns to_policy(p)))]
pub fn to_policy(p: &LinkedPolicy) -> Policy {
    Policy {
        id: clone_str(&p.id),
        effect: clone_effect(&p.effect),
        condition: policy_to_expr(p),
    }
}
