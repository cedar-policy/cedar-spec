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

//! The evaluator (`Cedar/Spec/Evaluator.lean`).

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::entities::*;
use super::expr::*;
use super::ext;
use super::request::*;
use super::value::*;

// ---------------------------------------------------------------------------
// Operators
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns int_or_err(i)))]
pub fn int_or_err(i: Option<i64>) -> Result<Value, Error> {
    match i {
        Some(i) => Ok(Value::Prim(Prim::Int(i))),
        None => Err(Error::ArithBoundsError),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns bool_val(b)))]
pub fn bool_val(b: bool) -> Value {
    Value::Prim(Prim::Bool(b))
}

/// `text like pattern`, where `*` matches any (possibly empty) sequence
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns wildcard_match(text, pattern)))]
pub fn wildcard_match(text: &Str, pattern: &List<PatElem>) -> bool {
    decreases!(text, pattern);
    match pattern {
        List::Nil => match text {
            List::Nil => true,
            List::Cons(_, _) => false,
        },
        List::Cons(PatElem::Star, prest) => {
            wildcard_match(text, prest)
                || match text {
                    List::Nil => false,
                    List::Cons(_, trest) => wildcard_match(trest, pattern),
                }
        }
        List::Cons(PatElem::JustChar(c), prest) => match text {
            List::Nil => false,
            List::Cons(d, trest) => *c == *d && wildcard_match(trest, prest),
        },
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns apply1(op, v)))]
pub fn apply1(op: &UnaryOp, v: &Value) -> Result<Value, Error> {
    match (op, v) {
        (UnaryOp::Not, Value::Prim(Prim::Bool(b))) => Ok(bool_val(!*b)),
        (UnaryOp::Neg, Value::Prim(Prim::Int(i))) => int_or_err(0i64.checked_sub(*i)),
        (UnaryOp::IsEmpty, Value::Set(vs)) => Ok(bool_val(match &**vs {
            List::Nil => true,
            List::Cons(_, _) => false,
        })),
        (UnaryOp::Like(p), Value::Prim(Prim::String(s))) => Ok(bool_val(wildcard_match(s, p))),
        (UnaryOp::Is(ety), Value::Prim(Prim::EntityUID(u))) => Ok(bool_val(name_eq(ety, &u.ty))),
        _ => Err(Error::TypeError),
    }
}

/// `uid1 in uid2`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns in_e(u1, u2, es)))]
pub fn in_e(u1: &EntityUID, u2: &EntityUID, es: &Entities) -> bool {
    uid_eq(u1, u2)
        || match entities_find(es, u1) {
            Some(d) => uids_contains(&d.ancestors, u2),
            None => false,
        }
}

/// `uid in [..]`: a type error if the set contains a non-entity; otherwise,
/// whether `uid` is in any of the elements.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns in_s(u, vs, es)))]
pub fn in_s(u: &EntityUID, vs: &List<Value>, es: &Entities) -> Result<bool, Error> {
    decreases!(vs);
    match vs {
        List::Nil => Ok(false),
        List::Cons(Value::Prim(Prim::EntityUID(u2)), rest) => {
            let found = in_e(u, u2, es);
            match in_s(u, rest, es) {
                Ok(b) => Ok(found || b),
                Err(e) => Err(e),
            }
        }
        List::Cons(_, _) => Err(Error::TypeError),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns get_tag(u, tag, es)))]
pub fn get_tag(u: &EntityUID, tag: &Str, es: &Entities) -> Result<Value, Error> {
    match entities_find(es, u) {
        Some(d) => match attrs_find(&d.tags, tag) {
            Some(v) => Ok(clone_value(v)),
            None => Err(Error::TagDoesNotExist),
        },
        None => Err(Error::EntityDoesNotExist),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns has_tag(u, tag, es)))]
pub fn has_tag(u: &EntityUID, tag: &Str, es: &Entities) -> bool {
    match entities_find(es, u) {
        Some(d) => attrs_contains(&d.tags, tag),
        None => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns apply2(op, v1, v2, es)))]
pub fn apply2(op: &BinaryOp, v1: &Value, v2: &Value, es: &Entities) -> Result<Value, Error> {
    match (op, v1, v2) {
        (BinaryOp::Eq, _, _) => Ok(bool_val(value_eq(v1, v2))),
        (BinaryOp::Less, Value::Prim(Prim::Int(i)), Value::Prim(Prim::Int(j))) => {
            Ok(bool_val(*i < *j))
        }
        (
            BinaryOp::Less,
            Value::Ext(ext::Ext::Datetime(i)),
            Value::Ext(ext::Ext::Datetime(j)),
        ) => Ok(bool_val(*i < *j)),
        (
            BinaryOp::Less,
            Value::Ext(ext::Ext::Duration(i)),
            Value::Ext(ext::Ext::Duration(j)),
        ) => Ok(bool_val(*i < *j)),
        (BinaryOp::LessEq, Value::Prim(Prim::Int(i)), Value::Prim(Prim::Int(j))) => {
            Ok(bool_val(*i <= *j))
        }
        (
            BinaryOp::LessEq,
            Value::Ext(ext::Ext::Datetime(i)),
            Value::Ext(ext::Ext::Datetime(j)),
        ) => Ok(bool_val(*i <= *j)),
        (
            BinaryOp::LessEq,
            Value::Ext(ext::Ext::Duration(i)),
            Value::Ext(ext::Ext::Duration(j)),
        ) => Ok(bool_val(*i <= *j)),
        (BinaryOp::Add, Value::Prim(Prim::Int(i)), Value::Prim(Prim::Int(j))) => {
            int_or_err(i.checked_add(*j))
        }
        (BinaryOp::Sub, Value::Prim(Prim::Int(i)), Value::Prim(Prim::Int(j))) => {
            int_or_err(i.checked_sub(*j))
        }
        (BinaryOp::Mul, Value::Prim(Prim::Int(i)), Value::Prim(Prim::Int(j))) => {
            int_or_err(i.checked_mul(*j))
        }
        (BinaryOp::Contains, Value::Set(vs), _) => Ok(bool_val(values_contains(vs, v2))),
        (BinaryOp::ContainsAll, Value::Set(vs1), Value::Set(vs2)) => {
            Ok(bool_val(values_sub(vs2, vs1)))
        }
        (BinaryOp::ContainsAny, Value::Set(vs1), Value::Set(vs2)) => {
            Ok(bool_val(values_intersect(vs1, vs2)))
        }
        (BinaryOp::Mem, Value::Prim(Prim::EntityUID(u1)), Value::Prim(Prim::EntityUID(u2))) => {
            Ok(bool_val(in_e(u1, u2, es)))
        }
        (BinaryOp::Mem, Value::Prim(Prim::EntityUID(u1)), Value::Set(vs)) => match in_s(u1, vs, es)
        {
            Ok(b) => Ok(bool_val(b)),
            Err(e) => Err(e),
        },
        (BinaryOp::HasTag, Value::Prim(Prim::EntityUID(u)), Value::Prim(Prim::String(t))) => {
            Ok(bool_val(has_tag(u, t, es)))
        }
        (BinaryOp::GetTag, Value::Prim(Prim::EntityUID(u)), Value::Prim(Prim::String(t))) => {
            get_tag(u, t, es)
        }
        _ => Err(Error::TypeError),
    }
}

// ---------------------------------------------------------------------------
// Attributes
// ---------------------------------------------------------------------------

/// `v has a`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns has_attr(v, a, es)))]
pub fn has_attr(v: &Value, a: &Str, es: &Entities) -> Result<Value, Error> {
    match v {
        Value::Record(avs) => Ok(bool_val(attrs_contains(avs, a))),
        Value::Prim(Prim::EntityUID(u)) => Ok(bool_val(entity_has_attr(es, u, a))),
        _ => Err(Error::TypeError),
    }
}

/// Does the entity `u` exist and have attribute `a`?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns entity_has_attr(es, u, a)))]
pub fn entity_has_attr(es: &Entities, u: &EntityUID, a: &Str) -> bool {
    match entities_find(es, u) {
        Some(d) => attrs_contains(&d.attrs, a),
        None => false,
    }
}

/// `v has a.b.c`, written `has_attrs(v, [a, b, c], es)`.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns has_attrs(v, attrs, es)))]
pub fn has_attrs(v: &Value, attrs: &List<Str>, es: &Entities) -> Result<Value, Error> {
    decreases!(attrs, 0u8);
    match attrs {
        List::Nil => Ok(bool_val(true)),
        List::Cons(a, rest) => match v {
            Value::Record(avs) => attrs_has_attrs(avs, a, rest, es),
            Value::Prim(Prim::EntityUID(u)) => entity_has_attrs(es, u, a, rest),
            _ => Err(Error::TypeError),
        },
    }
}

/// `{..} has a.rest`, for the record `avs`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_has_attrs(avs, a, rest, es)))]
pub fn attrs_has_attrs(
    avs: &Attrs,
    a: &Str,
    rest: &List<Str>,
    es: &Entities,
) -> Result<Value, Error> {
    decreases!(rest, 1u8);
    match attrs_find(avs, a) {
        Some(v) => has_attrs(v, rest, es),
        None => Ok(bool_val(false)),
    }
}

/// `u has a.rest`, for the entity `u`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns entity_has_attrs(es, u, a, rest)))]
pub fn entity_has_attrs(
    es: &Entities,
    u: &EntityUID,
    a: &Str,
    rest: &List<Str>,
) -> Result<Value, Error> {
    decreases!(rest, 2u8);
    match entities_find(es, u) {
        Some(d) => attrs_has_attrs(&d.attrs, a, rest, es),
        None => Ok(bool_val(false)),
    }
}

/// `v.a`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns get_attr(v, a, es)))]
pub fn get_attr(v: &Value, a: &Str, es: &Entities) -> Result<Value, Error> {
    match v {
        Value::Record(avs) => attrs_find_or_err(avs, a),
        Value::Prim(Prim::EntityUID(u)) => entity_attr_or_err(es, u, a),
        _ => Err(Error::TypeError),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_find_or_err(avs, a)))]
pub fn attrs_find_or_err(avs: &Attrs, a: &Str) -> Result<Value, Error> {
    match attrs_find(avs, a) {
        Some(v) => Ok(clone_value(v)),
        None => Err(Error::AttrDoesNotExist),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns entity_attr_or_err(es, u, a)))]
pub fn entity_attr_or_err(es: &Entities, u: &EntityUID, a: &Str) -> Result<Value, Error> {
    match entities_find(es, u) {
        Some(d) => attrs_find_or_err(&d.attrs, a),
        None => Err(Error::EntityDoesNotExist),
    }
}

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns as_bool(r)))]
pub fn as_bool(r: Result<Value, Error>) -> Result<bool, Error> {
    match r {
        Ok(Value::Prim(Prim::Bool(b))) => Ok(b),
        Ok(_) => Err(Error::TypeError),
        Err(e) => Err(e),
    }
}

// ---------------------------------------------------------------------------
// Extension calls
// ---------------------------------------------------------------------------

/// The value of the result of an extension function
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns ext_res_value(r)))]
pub fn ext_res_value(r: ext::ExtRes) -> Value {
    match r {
        ext::ExtRes::Bool(b) => Value::Prim(Prim::Bool(b)),
        ext::ExtRes::Int(i) => Value::Prim(Prim::Int(i)),
        ext::ExtRes::Ext(e) => Value::Ext(e),
    }
}

/// `Cedar.Spec.call` on evaluated arguments
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns call_ext(f, vs)))]
pub fn call_ext(f: &ext::ExtFun, vs: &List<Value>) -> Result<Value, Error> {
    match ext::call(f, vs) {
        Ok(r) => Ok(ext_res_value(r)),
        Err(e) => Err(e),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns evaluate(x, req, es)))]
pub fn evaluate(x: &Expr, req: &Request, es: &Entities) -> Result<Value, Error> {
    decreases!(x);
    match x {
        Expr::Lit(p) => Ok(Value::Prim(clone_prim(p))),
        Expr::Var(Var::Principal) => Ok(Value::Prim(Prim::EntityUID(clone_uid(&req.principal)))),
        Expr::Var(Var::Action) => Ok(Value::Prim(Prim::EntityUID(clone_uid(&req.action)))),
        Expr::Var(Var::Resource) => Ok(Value::Prim(Prim::EntityUID(clone_uid(&req.resource)))),
        Expr::Var(Var::Context) => Ok(Value::Record(Box::new(clone_attrs(&req.context)))),
        Expr::Ite(x1, x2, x3) => match as_bool(evaluate(x1, req, es)) {
            Ok(true) => evaluate(x2, req, es),
            Ok(false) => evaluate(x3, req, es),
            Err(e) => Err(e),
        },
        Expr::And(x1, x2) => match as_bool(evaluate(x1, req, es)) {
            Ok(true) => match as_bool(evaluate(x2, req, es)) {
                Ok(b) => Ok(bool_val(b)),
                Err(e) => Err(e),
            },
            Ok(false) => Ok(bool_val(false)),
            Err(e) => Err(e),
        },
        Expr::Or(x1, x2) => match as_bool(evaluate(x1, req, es)) {
            Ok(true) => Ok(bool_val(true)),
            Ok(false) => match as_bool(evaluate(x2, req, es)) {
                Ok(b) => Ok(bool_val(b)),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        },
        Expr::UnaryApp(op, x1) => match evaluate(x1, req, es) {
            Ok(v1) => apply1(op, &v1),
            Err(e) => Err(e),
        },
        Expr::BinaryApp(op, x1, x2) => match evaluate(x1, req, es) {
            Ok(v1) => match evaluate(x2, req, es) {
                Ok(v2) => apply2(op, &v1, &v2, es),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        },
        Expr::GetAttr(x1, a) => match evaluate(x1, req, es) {
            Ok(v1) => get_attr(&v1, a, es),
            Err(e) => Err(e),
        },
        Expr::HasAttr(x1, a) => match evaluate(x1, req, es) {
            Ok(v1) => has_attr(&v1, a, es),
            Err(e) => Err(e),
        },
        Expr::ExtHasAttr(x1, a, attrs) => match evaluate(x1, req, es) {
            Ok(v1) => has_attrs(
                &v1,
                &List::Cons(clone_str(a), Box::new(clone_strs(attrs))),
                es,
            ),
            Err(e) => Err(e),
        },
        Expr::Set(xs) => match evaluate_list(xs, req, es) {
            Ok(vs) => Ok(Value::Set(Box::new(values_canonicalize(vs)))),
            Err(e) => Err(e),
        },
        Expr::Record(axs) => match evaluate_attrs(axs, req, es) {
            Ok(avs) => Ok(Value::Record(Box::new(attrs_canonicalize(avs)))),
            Err(e) => Err(e),
        },
        Expr::Call(f, xs) => match evaluate_list(xs, req, es) {
            Ok(vs) => call_ext(f, &vs),
            Err(e) => Err(e),
        },
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns evaluate_list(xs, req, es)))]
pub fn evaluate_list(xs: &List<Expr>, req: &Request, es: &Entities) -> Result<List<Value>, Error> {
    decreases!(xs);
    match xs {
        List::Nil => Ok(List::Nil),
        List::Cons(x, rest) => match evaluate(x, req, es) {
            Ok(v) => match evaluate_list(rest, req, es) {
                Ok(vs) => Ok(List::Cons(v, Box::new(vs))),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        },
    }
}

/// Evaluates the attributes of a record literal, in order.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns evaluate_attrs(axs, req, es)))]
pub fn evaluate_attrs(
    axs: &List<(Str, Expr)>,
    req: &Request,
    es: &Entities,
) -> Result<Attrs, Error> {
    decreases!(axs);
    match axs {
        List::Nil => Ok(List::Nil),
        List::Cons((a, x), rest) => match evaluate(x, req, es) {
            Ok(v) => match evaluate_attrs(rest, req, es) {
                Ok(avs) => Ok(List::Cons((clone_str(a), v), Box::new(avs))),
                Err(e) => Err(e),
            },
            Err(e) => Err(e),
        },
    }
}
