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

//! Expressions (`Cedar/Spec/Expr.lean`).

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::ext;
use super::value::*;

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Var {
    Principal,
    Action,
    Resource,
    Context,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum PatElem {
    Star,
    JustChar(char),
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum UnaryOp {
    Not,
    Neg,
    IsEmpty,
    Like(List<PatElem>),
    Is(Name),
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum BinaryOp {
    Eq,
    Mem,
    HasTag,
    GetTag,
    Less,
    LessEq,
    Add,
    Sub,
    Mul,
    Contains,
    ContainsAll,
    ContainsAny,
}

#[cfg_attr(feature = "verus", verus_verify)]
pub enum Expr {
    Lit(Prim),
    Var(Var),
    Ite(Box<Expr>, Box<Expr>, Box<Expr>),
    And(Box<Expr>, Box<Expr>),
    Or(Box<Expr>, Box<Expr>),
    UnaryApp(UnaryOp, Box<Expr>),
    BinaryApp(BinaryOp, Box<Expr>, Box<Expr>),
    GetAttr(Box<Expr>, Str),
    HasAttr(Box<Expr>, Str),
    /// `x has a.b.c` is `ExtHasAttr(x, a, [b, c])`
    ExtHasAttr(Box<Expr>, Str, List<Str>),
    Set(Box<List<Expr>>),
    Record(Box<List<(Str, Expr)>>),
    Call(ext::ExtFun, Box<List<Expr>>),
}
