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

//! Values (`Cedar/Spec/Value.lean`) and their operations. As in Lean, sets and
//! maps are canonical lists (sorted, no duplicates), so equality is structural.

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::ext;

// ---------------------------------------------------------------------------
// Data
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

/// A string, as a list of Unicode scalar values.
pub type Str = List<char>;

#[cfg_attr(feature = "verus", verus_verify)]
pub struct Name {
    pub id: Str,
    pub path: List<Str>,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub struct EntityUID {
    pub ty: Name,
    pub eid: Str,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Prim {
    Bool(bool),
    Int(i64),
    String(Str),
    EntityUID(EntityUID),
}

/// A record or entity attribute map. Well-formed maps are in canonical form.
pub type Attrs = List<(Str, Value)>;

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Value {
    Prim(Prim),
    /// Well-formed sets are in canonical form.
    Set(Box<List<Value>>),
    Record(Box<Attrs>),
    Ext(ext::Ext),
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Error {
    EntityDoesNotExist,
    AttrDoesNotExist,
    TagDoesNotExist,
    TypeError,
    ArithBoundsError,
    ExtensionError,
}

// ---------------------------------------------------------------------------
// Copying
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_str(s)))]
pub fn clone_str(s: &Str) -> Str {
    decreases!(s);
    match s {
        List::Nil => List::Nil,
        List::Cons(c, rest) => List::Cons(*c, Box::new(clone_str(rest))),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_strs(ss)))]
pub fn clone_strs(ss: &List<Str>) -> List<Str> {
    decreases!(ss);
    match ss {
        List::Nil => List::Nil,
        List::Cons(s, rest) => List::Cons(clone_str(s), Box::new(clone_strs(rest))),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_name(n)))]
pub fn clone_name(n: &Name) -> Name {
    Name {
        id: clone_str(&n.id),
        path: clone_strs(&n.path),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_uid(u)))]
pub fn clone_uid(u: &EntityUID) -> EntityUID {
    EntityUID {
        ty: clone_name(&u.ty),
        eid: clone_str(&u.eid),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_prim(p)))]
pub fn clone_prim(p: &Prim) -> Prim {
    match p {
        Prim::Bool(b) => Prim::Bool(*b),
        Prim::Int(i) => Prim::Int(*i),
        Prim::String(s) => Prim::String(clone_str(s)),
        Prim::EntityUID(u) => Prim::EntityUID(clone_uid(u)),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_value(v)))]
pub fn clone_value(v: &Value) -> Value {
    decreases!(v);
    match v {
        Value::Prim(p) => Value::Prim(clone_prim(p)),
        Value::Set(vs) => Value::Set(Box::new(clone_values(vs))),
        Value::Record(avs) => Value::Record(Box::new(clone_attrs(avs))),
        Value::Ext(e) => Value::Ext(ext::clone_ext(e)),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_values(vs)))]
pub fn clone_values(vs: &List<Value>) -> List<Value> {
    decreases!(vs);
    match vs {
        List::Nil => List::Nil,
        List::Cons(v, rest) => List::Cons(clone_value(v), Box::new(clone_values(rest))),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns clone_attrs(avs)))]
pub fn clone_attrs(avs: &Attrs) -> Attrs {
    decreases!(avs);
    match avs {
        List::Nil => List::Nil,
        List::Cons((a, v), rest) => {
            List::Cons((clone_str(a), clone_value(v)), Box::new(clone_attrs(rest)))
        }
    }
}

// ---------------------------------------------------------------------------
// Equality and ordering (the ordering is Lean's `Cedar.Spec.Value.lt`)
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns str_eq(a, b)))]
pub fn str_eq(a: &Str, b: &Str) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons(c, a1), List::Cons(d, b1)) => *c == *d && str_eq(a1, b1),
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns strs_eq(a, b)))]
pub fn strs_eq(a: &List<Str>, b: &List<Str>) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons(s, a1), List::Cons(t, b1)) => str_eq(s, t) && strs_eq(a1, b1),
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns name_eq(a, b)))]
pub fn name_eq(a: &Name, b: &Name) -> bool {
    str_eq(&a.id, &b.id) && strs_eq(&a.path, &b.path)
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns uid_eq(a, b)))]
pub fn uid_eq(a: &EntityUID, b: &EntityUID) -> bool {
    name_eq(&a.ty, &b.ty) && str_eq(&a.eid, &b.eid)
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns prim_eq(a, b)))]
pub fn prim_eq(a: &Prim, b: &Prim) -> bool {
    match (a, b) {
        (Prim::Bool(x), Prim::Bool(y)) => *x == *y,
        (Prim::Int(x), Prim::Int(y)) => *x == *y,
        (Prim::String(x), Prim::String(y)) => str_eq(x, y),
        (Prim::EntityUID(x), Prim::EntityUID(y)) => uid_eq(x, y),
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns value_eq(a, b)))]
pub fn value_eq(a: &Value, b: &Value) -> bool {
    decreases!(a);
    match (a, b) {
        (Value::Prim(x), Value::Prim(y)) => prim_eq(x, y),
        (Value::Set(xs), Value::Set(ys)) => values_eq(xs, ys),
        (Value::Record(xs), Value::Record(ys)) => attrs_eq(xs, ys),
        (Value::Ext(x), Value::Ext(y)) => ext::ext_eq(x, y),
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns values_eq(a, b)))]
pub fn values_eq(a: &List<Value>, b: &List<Value>) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons(x, a1), List::Cons(y, b1)) => value_eq(x, y) && values_eq(a1, b1),
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_eq(a, b)))]
pub fn attrs_eq(a: &Attrs, b: &Attrs) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => true,
        (List::Cons((k, x), a1), List::Cons((l, y), b1)) => {
            str_eq(k, l) && value_eq(x, y) && attrs_eq(a1, b1)
        }
        _ => false,
    }
}

/// `Char.lt`. Opaque to Aeneas, which can't compare `char`s; hand-written in
/// `lean/CedarRustModel/FunsExternal.lean`.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns char_lt(c, d)))]
pub fn char_lt(c: char, d: char) -> bool {
    (c as u32) < (d as u32)
}

/// Lexicographic order on strings (`String.lt` in Lean)
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns str_lt(a, b)))]
pub fn str_lt(a: &Str, b: &Str) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => false,
        (List::Nil, List::Cons(_, _)) => true,
        (List::Cons(_, _), List::Nil) => false,
        (List::Cons(c, a1), List::Cons(d, b1)) => char_lt(*c, *d) || (*c == *d && str_lt(a1, b1)),
    }
}

/// Lexicographic order on lists of strings
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns strs_lt(a, b)))]
pub fn strs_lt(a: &List<Str>, b: &List<Str>) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => false,
        (List::Nil, List::Cons(_, _)) => true,
        (List::Cons(_, _), List::Nil) => false,
        (List::Cons(s, a1), List::Cons(t, b1)) => str_lt(s, t) || (str_eq(s, t) && strs_lt(a1, b1)),
    }
}

/// `Name.lt`: compares `id :: path` lexicographically
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns name_lt(a, b)))]
pub fn name_lt(a: &Name, b: &Name) -> bool {
    str_lt(&a.id, &b.id) || (str_eq(&a.id, &b.id) && strs_lt(&a.path, &b.path))
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns uid_lt(a, b)))]
pub fn uid_lt(a: &EntityUID, b: &EntityUID) -> bool {
    name_lt(&a.ty, &b.ty) || (name_eq(&a.ty, &b.ty) && str_lt(&a.eid, &b.eid))
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns prim_lt(a, b)))]
pub fn prim_lt(a: &Prim, b: &Prim) -> bool {
    match (a, b) {
        (Prim::Bool(x), Prim::Bool(y)) => !*x && *y,
        (Prim::Int(x), Prim::Int(y)) => *x < *y,
        (Prim::String(x), Prim::String(y)) => str_lt(x, y),
        (Prim::EntityUID(x), Prim::EntityUID(y)) => uid_lt(x, y),
        (Prim::Bool(_), _) => true,
        (Prim::Int(_), Prim::String(_)) => true,
        (Prim::Int(_), Prim::EntityUID(_)) => true,
        (Prim::String(_), Prim::EntityUID(_)) => true,
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns value_lt(a, b)))]
pub fn value_lt(a: &Value, b: &Value) -> bool {
    decreases!(a);
    match (a, b) {
        (Value::Prim(x), Value::Prim(y)) => prim_lt(x, y),
        (Value::Set(xs), Value::Set(ys)) => values_lt(xs, ys),
        (Value::Record(xs), Value::Record(ys)) => attrs_lt(xs, ys),
        (Value::Ext(x), Value::Ext(y)) => ext::ext_lt(x, y),
        (Value::Prim(_), _) => true,
        (Value::Set(_), Value::Record(_)) => true,
        (Value::Set(_), Value::Ext(_)) => true,
        (Value::Record(_), Value::Ext(_)) => true,
        _ => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns values_lt(a, b)))]
pub fn values_lt(a: &List<Value>, b: &List<Value>) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => false,
        (List::Nil, List::Cons(_, _)) => true,
        (List::Cons(_, _), List::Nil) => false,
        (List::Cons(x, a1), List::Cons(y, b1)) => {
            value_lt(x, y) || (value_eq(x, y) && values_lt(a1, b1))
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_lt(a, b)))]
pub fn attrs_lt(a: &Attrs, b: &Attrs) -> bool {
    decreases!(a);
    match (a, b) {
        (List::Nil, List::Nil) => false,
        (List::Nil, List::Cons(_, _)) => true,
        (List::Cons(_, _), List::Nil) => false,
        (List::Cons((k, x), a1), List::Cons((l, y), b1)) => {
            str_lt(k, l)
                || (str_eq(k, l) && value_lt(x, y))
                || (str_eq(k, l) && value_eq(x, y) && attrs_lt(a1, b1))
        }
    }
}

// ---------------------------------------------------------------------------
// Canonical forms (`Cedar.Data.List.canonicalize`)
// ---------------------------------------------------------------------------

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns values_insert(x, xs)))]
pub fn values_insert(x: Value, xs: List<Value>) -> List<Value> {
    decreases!(&xs);
    match xs {
        List::Nil => List::Cons(x, Box::new(List::Nil)),
        List::Cons(hd, tl) => {
            if value_lt(&x, &hd) {
                List::Cons(x, Box::new(List::Cons(hd, tl)))
            } else if value_lt(&hd, &x) {
                List::Cons(hd, Box::new(values_insert(x, *tl)))
            } else {
                List::Cons(x, tl)
            }
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns values_canonicalize(xs)))]
pub fn values_canonicalize(xs: List<Value>) -> List<Value> {
    decreases!(&xs);
    match xs {
        List::Nil => List::Nil,
        List::Cons(hd, tl) => values_insert(hd, values_canonicalize(*tl)),
    }
}

/// Inserts `(k, v)` into a canonical record, replacing any existing entry for `k`.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_insert(k, v, avs)))]
pub fn attrs_insert(k: Str, v: Value, avs: Attrs) -> Attrs {
    decreases!(&avs);
    match avs {
        List::Nil => List::Cons((k, v), Box::new(List::Nil)),
        List::Cons((k1, v1), tl) => {
            if str_lt(&k, &k1) {
                List::Cons((k, v), Box::new(List::Cons((k1, v1), tl)))
            } else if str_lt(&k1, &k) {
                List::Cons((k1, v1), Box::new(attrs_insert(k, v, *tl)))
            } else {
                List::Cons((k, v), tl)
            }
        }
    }
}

/// Sorts by key; if a key occurs more than once, its first occurrence wins.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_canonicalize(avs)))]
pub fn attrs_canonicalize(avs: Attrs) -> Attrs {
    decreases!(&avs);
    match avs {
        List::Nil => List::Nil,
        List::Cons((k, v), tl) => attrs_insert(k, v, attrs_canonicalize(*tl)),
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns strs_insert(x, xs)))]
pub fn strs_insert(x: Str, xs: List<Str>) -> List<Str> {
    decreases!(&xs);
    match xs {
        List::Nil => List::Cons(x, Box::new(List::Nil)),
        List::Cons(hd, tl) => {
            if str_lt(&x, &hd) {
                List::Cons(x, Box::new(List::Cons(hd, tl)))
            } else if str_lt(&hd, &x) {
                List::Cons(hd, Box::new(strs_insert(x, *tl)))
            } else {
                List::Cons(x, tl)
            }
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns strs_canonicalize(xs)))]
pub fn strs_canonicalize(xs: List<Str>) -> List<Str> {
    decreases!(&xs);
    match xs {
        List::Nil => List::Nil,
        List::Cons(hd, tl) => strs_insert(hd, strs_canonicalize(*tl)),
    }
}

// ---------------------------------------------------------------------------
// Lookups
// ---------------------------------------------------------------------------

/// `Set.contains`
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns values_contains(xs, y)))]
pub fn values_contains(xs: &List<Value>, y: &Value) -> bool {
    decreases!(xs);
    match xs {
        List::Nil => false,
        List::Cons(x, rest) => value_eq(x, y) || values_contains(rest, y),
    }
}

/// `Set.subset`: is every element of `xs` an element of `ys`?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns values_sub(xs, ys)))]
pub fn values_sub(xs: &List<Value>, ys: &List<Value>) -> bool {
    decreases!(xs);
    match xs {
        List::Nil => true,
        List::Cons(x, rest) => values_contains(ys, x) && values_sub(rest, ys),
    }
}

/// `Set.intersects`: do the two sets have an element in common?
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns values_intersect(xs, ys)))]
pub fn values_intersect(xs: &List<Value>, ys: &List<Value>) -> bool {
    decreases!(xs);
    match xs {
        List::Nil => false,
        List::Cons(x, rest) => values_contains(ys, x) || values_intersect(rest, ys),
    }
}

/// The value of the first occurrence of `k` in `avs`.
#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_find(avs, k)))]
pub fn attrs_find<'a>(avs: &'a Attrs, k: &Str) -> Option<&'a Value> {
    decreases!(avs);
    match avs {
        List::Nil => None,
        List::Cons((a, v), rest) => {
            if str_eq(a, k) {
                Some(v)
            } else {
                attrs_find(rest, k)
            }
        }
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns attrs_contains(avs, k)))]
pub fn attrs_contains(avs: &Attrs, k: &Str) -> bool {
    match attrs_find(avs, k) {
        Some(_) => true,
        None => false,
    }
}

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns uids_contains(uids, u)))]
pub fn uids_contains(uids: &List<EntityUID>, u: &EntityUID) -> bool {
    decreases!(uids);
    match uids {
        List::Nil => false,
        List::Cons(v, rest) => uid_eq(v, u) || uids_contains(rest, u),
    }
}
