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

//! Typed-expression differential testing (cedar-spec issue #840).
//!
//! The existing validator DRT compares only whether Rust and Lean agree that
//! validation passed. This module compares the *typed expression* each side
//! produces: `Typechecker::typecheck_by_single_request_env` on the Rust side
//! and `Validation.typecheckPolicy` on the Lean side.
//!
//! ## What is compared
//!
//! Every disagreement is placed in exactly one bucket by [`classify`]. No
//! disagreement is discarded, and `Unclassified` is a failure of this module,
//! not of either implementation.
//!
//! ## Declared normalisations
//!
//! The two ASTs are not isomorphic, so the comparison declares its folds
//! rather than hiding them:
//!
//! * Rust `ExprKind::Like { .. }` and `ExprKind::Is { .. }` are separate AST
//!   variants; Lean models both as `unaryApp` with a `like`/`is` `UnaryOp`.
//!   The Rust side is folded to the Lean shape. Recorded, not silent.
//! * Rust `Record` is a `BTreeMap` (sorted by key); Lean `record` is an
//!   association list. Fields are compared as sorted key/value pairs so that
//!   ordering alone never produces a divergence.
//! * Rust `ExprKind::Slot` and `ExprKind::Unknown` have no Lean counterpart.
//!   Inputs reaching them yield [`Divergence::UnsupportedRustVariant`] rather
//!   than a spurious shape mismatch.
//! * Rust `Var(Action)` against the Lean literal for this environment's own
//!   action is [`Divergence::ActionSubstituted`], a declared difference. A
//!   `var` against any OTHER entity literal, or against this action with a
//!   differing type, stays a `ShapeMismatch`.
//! * Rust `PolicyCheck::Irrelevant` (the policy always evaluates to false for
//!   this environment, whether from the scope or from a folded condition)
//!   against a Lean error is [`Divergence::StaticallyFalsePolicy`], a declared
//!   difference.
//!   Neither side offers an expression, so there is nothing to disagree about.
//!   The same `Irrelevant` against a Lean expression is compared normally, and
//!   a Rust `Success` against a Lean error stays an outcome disagreement.
//!
//! ## Known cause of the `var` against `lit` result
//!
//! Lean's `typecheckPolicy` substitutes the concrete action EUID into the
//! policy expression before typechecking (`Cedar/Validation/Validator.lean`,
//! `let expr := substituteAction env.reqty.action policy.toExpr`). Rust's
//! `typecheck_by_single_request_env` typechecks `t.condition()` directly and
//! has no equivalent substitution, so it keeps `Var(Action)` where Lean has
//! the literal.
//!
//! This is deliberate on the Lean side and is recorded here so the result is
//! not read as an unexplained disagreement. Both sides reach the same
//! validation verdict, which is why a pass/fail comparison never surfaced it.
//!
//! It is recorded as [`Divergence::ActionSubstituted`], a declared difference,
//! and it is recognised ONLY when the Lean literal is this environment's own
//! action and the two sides agree on the node's type. Declaring it is what
//! lets the target assert on everything else: while it was a finding the
//! target panicked on roughly one pair in ten of ordinary generated input, so
//! it could not be run.
//!
//! Declaring it does NOT answer whether the Rust typed expression ought to
//! mirror the specification's substitution. That question is open, and the
//! pairs are still counted and still reported through
//! [`RunReport::declared_differences`]. Removing the `ActionSubstituted` arm
//! of [`Divergence::is_declared_difference`] puts them back among the findings
//! and changes nothing else.
//!
//! ## Independence
//!
//! The two typecheckers are independently authored (different repositories,
//! different languages), so their agreement carries information. The
//! *comparator* is not independent of either: it is this harness. Its ability
//! to fire is therefore established by a planted-divergence control
//! (`tests::negative_control_*`), not assumed. Agreement is also bounded by
//! the shared Cedar specification: if the spec is wrong, both sides can agree
//! and both be wrong.

use cedar_lean_ffi::LeanTypedExprEnvResult;
use cedar_policy_core::ast::{
    BinaryOp, EntityType, Expr, ExprKind, Literal, Name, PatternElem, UnaryOp, Var,
};
use cedar_policy_core::validator::types::{BoolType, EntityKind, OpenTag, Type};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap, HashSet};

/// One classified disagreement between the Rust and Lean typed expressions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Divergence {
    /// Same position, different AST constructor. A genuine structural
    /// disagreement between the two typecheckers.
    ShapeMismatch {
        path: String,
        rust: String,
        lean: String,
    },
    /// Same constructor, different operator, attribute, variable or literal.
    OperatorMismatch {
        path: String,
        field: String,
        rust: String,
        lean: String,
    },
    /// Same constructor, different number of children (set/record/call arity).
    ArityMismatch {
        path: String,
        rust: usize,
        lean: usize,
    },
    /// One side produced a typed expression and the other reported an error.
    OutcomeMismatch {
        policy: String,
        env: String,
        rust_ok: bool,
        lean_ok: bool,
    },
    /// An environment key present on one side only. This is an alignment
    /// problem in the harness, not a finding about either implementation.
    EnvUnmatched { policy: String, env: String },
    /// A Rust AST variant with no Lean counterpart (`Slot`, `Unknown`).
    /// Out of scope for this target, recorded rather than dropped.
    UnsupportedRustVariant { path: String, variant: String },
    /// One side folded a statically-true policy condition to a boolean
    /// literal and the other kept the scope-constraint conjunction.
    ///
    /// Its own bucket rather than a `ShapeMismatch`, because it is a
    /// difference in constant folding and not a disagreement about the shape
    /// of a shared expression: the folded side has no subtree to compare, so
    /// grouping it with genuine shape disagreements buries them.
    ///
    /// The types the two sides assign to the whole condition are still
    /// compared and reported here, which is the only part of these trees that
    /// remains comparable.
    ConstantFoldedCondition {
        path: String,
        folded: &'static str,
        rust_ty: String,
        lean_ty: String,
        types_agree: bool,
    },
    /// Rust kept `Var(Action)` where Lean substituted the concrete action
    /// EUID literal for this environment.
    ///
    /// Its own bucket rather than a `ShapeMismatch`, for the same reason as
    /// constant folding: it is a difference in what each side typechecks, not
    /// a disagreement about the shape of a shared expression.
    ///
    /// Recognised ONLY when the Lean literal is *this environment's* action.
    /// A `var` against any other entity literal is not this case and stays a
    /// `ShapeMismatch`, so a substitution of the WRONG action is still caught.
    /// The types both sides assign are compared and carried here; a pair whose
    /// types DISAGREE is not declared and stays a finding.
    ActionSubstituted {
        path: String,
        action: String,
        rust_ty: String,
        lean_ty: String,
        types_agree: bool,
    },
    /// Rust reported the policy statically false for this environment
    /// (`PolicyCheck::Irrelevant`) and Lean's `typecheckPolicy` reported an
    /// error. Both sides decline to offer a typed expression to compare, for
    /// the same underlying reason, so this is a representational difference
    /// and not a disagreement to act on.
    ///
    /// Its own bucket rather than an `OutcomeMismatch`, because the two are
    /// not the same claim: an `OutcomeMismatch` says one side typechecked a
    /// policy the other rejected, and that is never what this is. A Rust
    /// *success* against a Lean error is still an `OutcomeMismatch`, which is
    /// what keeps this from swallowing a real outcome disagreement.
    StaticallyFalsePolicy { policy: String, env: String },
    /// The Lean JSON did not have the expected tagged shape. A harness
    /// problem: the encoding changed under us.
    MalformedLeanJson { path: String, detail: String },
}

impl Divergence {
    /// Buckets that indicate a problem with this harness rather than a
    /// finding about either typechecker.
    pub fn is_harness_problem(&self) -> bool {
        matches!(
            self,
            Divergence::EnvUnmatched { .. } | Divergence::MalformedLeanJson { .. }
        )
    }

    /// A representational difference that is declared and tested rather than
    /// a disagreement to act on. Two of them:
    ///
    /// * The two implementations constant-fold a statically-true condition
    ///   differently but assign it the same type. A folded pair whose types
    ///   DISAGREE is not declared and stays a finding.
    /// * Rust reports a policy statically false for an environment and Lean
    ///   reports an error for it. Neither offers an expression to compare, so
    ///   there is nothing they disagree about.
    /// * Lean substituted this environment's concrete action EUID where Rust
    ///   kept `Var(Action)`, and both sides gave the node the same type. A
    ///   substitution of a DIFFERENT action never reaches this bucket, and one
    ///   whose types disagree stays a finding.
    ///
    /// Declaring the substitution case does not settle whether the Rust typed
    /// expression ought to mirror the specification's substitution. It is
    /// still reported, through [`RunReport::declared_differences`]; removing
    /// the `ActionSubstituted` arm below puts those pairs back among the
    /// findings without touching anything else.
    pub fn is_declared_difference(&self) -> bool {
        matches!(
            self,
            Divergence::ConstantFoldedCondition {
                types_agree: true,
                ..
            } | Divergence::ActionSubstituted {
                types_agree: true,
                ..
            } | Divergence::StaticallyFalsePolicy { .. }
        )
    }

    pub fn bucket(&self) -> &'static str {
        match self {
            Divergence::ShapeMismatch { .. } => "SHAPE_MISMATCH",
            Divergence::OperatorMismatch { .. } => "OPERATOR_MISMATCH",
            Divergence::ArityMismatch { .. } => "ARITY_MISMATCH",
            Divergence::OutcomeMismatch { .. } => "OUTCOME_MISMATCH",
            Divergence::EnvUnmatched { .. } => "ENV_UNMATCHED",
            Divergence::UnsupportedRustVariant { .. } => "UNSUPPORTED_RUST_VARIANT",
            Divergence::ConstantFoldedCondition { .. } => "CONSTANT_FOLDED_CONDITION",
            Divergence::ActionSubstituted { .. } => "ACTION_SUBSTITUTED",
            Divergence::StaticallyFalsePolicy { .. } => "STATICALLY_FALSE_POLICY",
            Divergence::MalformedLeanJson { .. } => "MALFORMED_LEAN_JSON",
        }
    }
}

/// A normalised node: the constructor tag, scalar fields that identify the
/// node (operator, attribute, variable, literal), and ordered children.
///
/// Both sides are rendered into this type independently. Neither renderer
/// reads the other side's value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Node {
    pub ctor: String,
    pub scalars: BTreeMap<String, String>,
    pub children: Vec<(String, Node)>,
}

impl Node {
    fn leaf(ctor: &str) -> Self {
        Node {
            ctor: ctor.to_string(),
            scalars: BTreeMap::new(),
            children: Vec::new(),
        }
    }
    fn with_scalar(mut self, k: &str, v: String) -> Self {
        self.scalars.insert(k.to_string(), v);
        self
    }
    fn with_child(mut self, k: &str, n: Node) -> Self {
        self.children.push((k.to_string(), n));
        self
    }

    /// Put children into one canonical order, keyed by field name.
    ///
    /// Load-bearing. Lean's derived `ToJson` does not emit constructor fields
    /// in declaration order — `and` comes back as `{"ty": .., "b": .., "a": ..}`
    /// — and `cedar-policy-core` enables serde_json's `preserve_order`, so
    /// that emission order survives parsing. The Rust renderer naturally emits
    /// source order. Comparing children positionally without this step reports
    /// a mismatch on every binary node, which is an artifact of two encoders'
    /// field order and says nothing about either typechecker.
    ///
    /// Sorting by key is safe because the key names, not the positions, carry
    /// the meaning: `compare` still pairs `a` with `a` and reports a genuinely
    /// missing or extra child as an arity or shape mismatch.
    fn canonical(mut self) -> Self {
        self.children.sort_by(|x, y| x.0.cmp(&y.0));
        self
    }
}

/// Render the Lean `TypedExpr` JSON into [`Node`].
///
/// The encoding is Lean's derived `ToJson`: `{"<ctor>": {"ty": .., ..}}`.
/// Scalar fields are compared by their JSON rendering; the `ty` annotation is
/// carried as a scalar so that a type disagreement surfaces as an
/// `OperatorMismatch` on the `ty` field.
pub fn lean_to_node(v: &Value, path: &str) -> Result<Node, Divergence> {
    let obj = v.as_object().ok_or_else(|| Divergence::MalformedLeanJson {
        path: path.to_string(),
        detail: format!("expected object, got {v}"),
    })?;
    if obj.len() != 1 {
        return Err(Divergence::MalformedLeanJson {
            path: path.to_string(),
            detail: format!(
                "expected exactly one constructor tag, got {} keys",
                obj.len()
            ),
        });
    }
    let (ctor, body) = obj.iter().next().expect("len checked above");
    let body = body
        .as_object()
        .ok_or_else(|| Divergence::MalformedLeanJson {
            path: path.to_string(),
            detail: format!("constructor {ctor} body is not an object"),
        })?;

    let mut node = Node::leaf(ctor);
    // Child field names, per Lean's TypedExpr constructors.
    const CHILD_KEYS: &[&str] = &["cond", "thenExpr", "elseExpr", "a", "b", "expr"];

    for (k, val) in body {
        if CHILD_KEYS.contains(&k.as_str()) {
            let child = lean_to_node(val, &format!("{path}.{k}"))?;
            node = node.with_child(k, child);
        } else if k == "ls" || k == "args" {
            let arr = val
                .as_array()
                .ok_or_else(|| Divergence::MalformedLeanJson {
                    path: path.to_string(),
                    detail: format!("{k} is not an array"),
                })?;
            for (i, item) in arr.iter().enumerate() {
                let child = lean_to_node(item, &format!("{path}.{k}[{i}]"))?;
                node = node.with_child(&format!("{k}[{i}]"), child);
            }
        } else if k == "map" {
            // record: list of [attr, TypedExpr] pairs. Sort by attr so that
            // ordering alone cannot produce a divergence.
            let arr = val
                .as_array()
                .ok_or_else(|| Divergence::MalformedLeanJson {
                    path: path.to_string(),
                    detail: "record map is not an array".to_string(),
                })?;
            let mut pairs: Vec<(String, Node)> = Vec::new();
            for (i, item) in arr.iter().enumerate() {
                let pair = item
                    .as_array()
                    .ok_or_else(|| Divergence::MalformedLeanJson {
                        path: path.to_string(),
                        detail: "record entry is not a pair".to_string(),
                    })?;
                let attr = pair.first().and_then(|a| a.as_str()).ok_or_else(|| {
                    Divergence::MalformedLeanJson {
                        path: path.to_string(),
                        detail: "record key is not a string".to_string(),
                    }
                })?;
                let val = pair.get(1).ok_or_else(|| Divergence::MalformedLeanJson {
                    path: path.to_string(),
                    detail: "record entry has no value".to_string(),
                })?;
                pairs.push((
                    attr.to_string(),
                    lean_to_node(val, &format!("{path}.map[{i}]"))?,
                ));
            }
            pairs.sort_by(|a, b| a.0.cmp(&b.0));
            for (attr, child) in pairs {
                node = node.with_child(&format!("map[{attr}]"), child);
            }
        } else {
            // ty, op, attr, v, p, xfn: identifying scalars, compared verbatim.
            node = node.with_scalar(k, canonical_scalar(val));
        }
    }
    Ok(node.canonical())
}

/// Stable rendering of a scalar JSON value, so that two structurally equal
/// values always render identically.
///
/// Object keys are emitted in sorted order. This is load-bearing, not
/// cosmetic: `cedar-policy-core` enables serde_json's `preserve_order`
/// feature, so `Value::Object` is insertion-ordered rather than sorted.
/// Lean's derived `ToJson` emits an entity type as `{"path": .., "id": ..}`
/// while the natural Rust construction order is `{"id": .., "path": ..}`.
/// Comparing `to_string()` directly would then report a divergence on every
/// entity-typed node, which is an artifact of two encoders' field order and
/// says nothing about either typechecker.
///
/// Arrays are *not* reordered. Array position is meaningful in both encodings
/// (`path` is an ordered namespace, `p` is an ordered `like` pattern), so
/// sorting them would absorb real disagreements.
fn canonical_scalar(v: &Value) -> String {
    match v {
        Value::String(s) => s.clone(),
        other => {
            let mut out = String::new();
            write_canonical(other, &mut out);
            out
        }
    }
}

fn write_canonical(v: &Value, out: &mut String) {
    match v {
        Value::Object(m) => {
            let mut keys: Vec<&String> = m.keys().collect();
            keys.sort();
            out.push('{');
            for (i, k) in keys.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                out.push_str(&Value::String((*k).to_string()).to_string());
                out.push(':');
                match m.get(k.as_str()) {
                    Some(val) => write_canonical(val, out),
                    None => out.push_str("null"),
                }
            }
            out.push('}');
        }
        Value::Array(a) => {
            out.push('[');
            for (i, x) in a.iter().enumerate() {
                if i > 0 {
                    out.push(',');
                }
                write_canonical(x, out);
            }
            out.push(']');
        }
        other => out.push_str(&other.to_string()),
    }
}

// ---------------------------------------------------------------------------
// Rust renderer
// ---------------------------------------------------------------------------
//
// Renders `Expr<Option<Type>>` — what `Typechecker::typecheck_by_single_request_env`
// returns — into the same [`Node`] shape that [`lean_to_node`] produces.
//
// The two renderers are independent in the sense that matters: neither reads
// the other side's value, and neither is a decoder from one AST into the
// other. They share only [`canonical_scalar`], which is a *formatter*, not a
// correspondence — sharing it removes an encoding artifact without removing
// any disagreement about content.
//
// ## What is asserted rather than measured
//
// The type-name mapping below (`type_json`) is a claim that Rust's
// `Type::Long` denotes what Lean's `.int` denotes, and so on for each
// constructor. That claim is part of this target's TRUSTED BASE, not part of
// its evidence: if the mapping is wrong, the target reports a divergence that
// is really a renderer bug. What the design buys is that such a mistake is
// *visible and adjudicable* — it surfaces as an `OperatorMismatch` on `ty`
// with both renderings printed, rather than as a silent pass or as a panic
// attributed to the harness. The mapping is deliberately kept in one small
// table so it can be audited as a unit.
//
// ## Rust type constructs Lean's `CedarType` cannot express
//
// `Type::Never`, `Type::Entity(AnyEntity)`, a non-singleton entity LUB,
// `Type::Set { element_type: None }`, `OpenTag::OpenAttributes`, and an
// unmodelled extension type have no Lean counterpart. They render to a
// `__rust_only__` tag which cannot equal any Lean rendering, so they surface
// as a divergence. Mapping them onto the nearest Lean type would be the one
// thing this target must not do.

/// A Rust-side type construct with no Lean `CedarType` counterpart. Renders to
/// a value that no Lean encoding can produce, so the difference is reported
/// rather than absorbed.
fn rust_only(what: &str) -> Value {
    json!({ "__rust_only__": what })
}

fn name_json(n: &Name) -> Value {
    json!({
        "id": n.basename_as_ref().to_string(),
        "path": n.as_ref().namespace_components().map(|c| c.to_string()).collect::<Vec<_>>(),
    })
}

fn entity_type_json(et: &EntityType) -> Value {
    name_json(et.name())
}

/// Render the Rust node annotation into Lean's `CedarType` JSON shape.
///
/// `None` is not silently treated as "some type": Rust's annotation is
/// `Option<Type>` and Lean's is a total `CedarType`, so an unannotated Rust
/// node renders to a value no Lean type can equal.
fn ty_json(t: &Option<Type>) -> Value {
    match t {
        None => json!({ "__unannotated__": true }),
        Some(t) => type_json(t),
    }
}

fn type_json(t: &Type) -> Value {
    match t {
        Type::Bool(BoolType::AnyBool) => json!({"bool": {"bty": "anyBool"}}),
        Type::Bool(BoolType::True) => json!({"bool": {"bty": "tt"}}),
        Type::Bool(BoolType::False) => json!({"bool": {"bty": "ff"}}),
        Type::Long => json!("int"),
        Type::String => json!("string"),
        Type::Never => rust_only("Never"),
        Type::Entity(EntityKind::AnyEntity) => rust_only("Entity(AnyEntity)"),
        Type::Entity(EntityKind::Entity(lub)) => match lub.get_single_entity() {
            Some(et) => json!({"entity": {"ety": entity_type_json(et)}}),
            // Lean's `.entity` names one entity type; a least-upper-bound of
            // several has no counterpart.
            None => rust_only("Entity(non-singleton LUB)"),
        },
        Type::Set {
            element_type: Some(el),
        } => json!({"set": {"ty": type_json(el)}}),
        // Lean's `.set` element type is total.
        Type::Set { element_type: None } => rust_only("Set(no element type)"),
        Type::Record {
            attrs,
            open_attributes,
        } => {
            let rty: Vec<Value> = attrs
                .iter()
                .map(|(k, at)| {
                    let qualifier = if at.is_required {
                        "required"
                    } else {
                        "optional"
                    };
                    let mut q = serde_json::Map::new();
                    q.insert(
                        qualifier.to_string(),
                        json!({ "a": type_json(&at.attr_type) }),
                    );
                    json!([k.to_string(), Value::Object(q)])
                })
                .collect();
            match open_attributes {
                OpenTag::ClosedAttributes => json!({"record": {"rty": rty}}),
                // Lean's record type has no open/closed tag.
                OpenTag::OpenAttributes => {
                    json!({"record": {"rty": rty, "__rust_only__": "openAttributes"}})
                }
            }
        }
        Type::ExtensionType { name } => {
            let base = name.basename_as_ref().to_string();
            match base.as_str() {
                // Lean spells this one differently; the rest coincide.
                "ipaddr" => json!({"ext": {"xty": "ipAddr"}}),
                "decimal" | "datetime" | "duration" => json!({"ext": {"xty": base}}),
                other => rust_only(&format!("ExtensionType({other})")),
            }
        }
    }
}

fn literal_json(l: &Literal) -> Value {
    match l {
        Literal::Bool(b) => json!({ "bool": b }),
        Literal::Long(i) => json!({ "int": i }),
        Literal::String(s) => json!({ "string": s.to_string() }),
        // The eid is taken raw rather than through `Eid::escaped()`. `escaped()`
        // is a Rust display convention: it renders U+0007 as the six characters
        // `\u{7}`, which serde then escapes again to `\\u{7}`. Lean emits the
        // raw character and its JSON encoder escapes it once, to `\u0007`. Only
        // the raw form is comparable. This is the same cause as the environment
        // key fix below, at a site that fix did not reach.
        Literal::EntityUID(uid) => json!({"entityUID": {
            "ty": entity_type_json(uid.entity_type()),
            "eid": <cedar_policy_core::ast::Eid as AsRef<str>>::as_ref(uid.eid()),
        }}),
    }
}

fn var_str(v: Var) -> &'static str {
    match v {
        Var::Principal => "principal",
        Var::Action => "action",
        Var::Resource => "resource",
        Var::Context => "context",
    }
}

fn unary_op_str(op: UnaryOp) -> &'static str {
    match op {
        UnaryOp::Not => "not",
        UnaryOp::Neg => "neg",
        UnaryOp::IsEmpty => "isEmpty",
    }
}

fn binary_op_str(op: BinaryOp) -> &'static str {
    match op {
        BinaryOp::Eq => "eq",
        // Cedar's `in`; Lean names the constructor `mem`.
        BinaryOp::In => "mem",
        BinaryOp::HasTag => "hasTag",
        BinaryOp::GetTag => "getTag",
        BinaryOp::Less => "less",
        BinaryOp::LessEq => "lessEq",
        BinaryOp::Add => "add",
        BinaryOp::Sub => "sub",
        BinaryOp::Mul => "mul",
        BinaryOp::Contains => "contains",
        BinaryOp::ContainsAll => "containsAll",
        BinaryOp::ContainsAny => "containsAny",
    }
}

fn pattern_json(elems: &[PatternElem]) -> Value {
    Value::Array(
        elems
            .iter()
            .map(|e| match e {
                PatternElem::Wildcard => json!("star"),
                PatternElem::Char(c) => json!({"justChar": {"c": *c as u32}}),
            })
            .collect(),
    )
}

/// Render a Rust typed expression into [`Node`].
///
/// Returns `Err(UnsupportedRustVariant)` for `Slot`, `Unknown` and `Error`,
/// which have no Lean `TypedExpr` counterpart. The whole (policy, environment)
/// pair is then reported as unsupported rather than compared, because a tree
/// containing one of these cannot be aligned with the Lean tree at all.
pub fn rust_to_node(e: &Expr<Option<Type>>, path: &str) -> Result<Node, Divergence> {
    let ty = canonical_scalar(&ty_json(e.data()));
    let unsupported = |variant: &str| {
        Err(Divergence::UnsupportedRustVariant {
            path: path.to_string(),
            variant: variant.to_string(),
        })
    };
    let child = |k: &str, sub: &Expr<Option<Type>>| rust_to_node(sub, &format!("{path}.{k}"));

    let node = match e.expr_kind() {
        ExprKind::Lit(l) => Node::leaf("lit").with_scalar("p", canonical_scalar(&literal_json(l))),
        ExprKind::Var(v) => Node::leaf("var").with_scalar("v", var_str(*v).to_string()),
        ExprKind::If {
            test_expr,
            then_expr,
            else_expr,
        } => Node::leaf("ite")
            .with_child("cond", child("cond", test_expr)?)
            .with_child("thenExpr", child("thenExpr", then_expr)?)
            .with_child("elseExpr", child("elseExpr", else_expr)?),
        ExprKind::And { left, right } => Node::leaf("and")
            .with_child("a", child("a", left)?)
            .with_child("b", child("b", right)?),
        ExprKind::Or { left, right } => Node::leaf("or")
            .with_child("a", child("a", left)?)
            .with_child("b", child("b", right)?),
        ExprKind::UnaryApp { op, arg } => Node::leaf("unaryApp")
            .with_scalar("op", unary_op_str(*op).to_string())
            .with_child("expr", child("expr", arg)?),
        // Declared fold: Rust has `Like` as its own AST variant, Lean models it
        // as `unaryApp` with a `like` operator carrying the pattern.
        ExprKind::Like { expr, pattern } => Node::leaf("unaryApp")
            .with_scalar(
                "op",
                canonical_scalar(&json!({"like": {"p": pattern_json(pattern.get_elems())}})),
            )
            .with_child("expr", child("expr", expr)?),
        // Declared fold: same story for `is`.
        ExprKind::Is { expr, entity_type } => Node::leaf("unaryApp")
            .with_scalar(
                "op",
                canonical_scalar(&json!({"is": {"ety": entity_type_json(entity_type)}})),
            )
            .with_child("expr", child("expr", expr)?),
        ExprKind::BinaryApp { op, arg1, arg2 } => Node::leaf("binaryApp")
            .with_scalar("op", binary_op_str(*op).to_string())
            .with_child("a", child("a", arg1)?)
            .with_child("b", child("b", arg2)?),
        ExprKind::GetAttr { expr, attr } => Node::leaf("getAttr")
            .with_scalar("attr", attr.to_string())
            .with_child("expr", child("expr", expr)?),
        ExprKind::HasAttr { expr, attr } => Node::leaf("hasAttr")
            .with_scalar("attr", attr.to_string())
            .with_child("expr", child("expr", expr)?),
        ExprKind::Set(elems) => {
            let mut n = Node::leaf("set");
            for (i, el) in elems.iter().enumerate() {
                n = n.with_child(&format!("ls[{i}]"), child(&format!("ls[{i}]"), el)?);
            }
            n
        }
        ExprKind::Record(map) => {
            // Rust's `Record` is a `BTreeMap`, so this iterates in key order;
            // `lean_to_node` sorts the Lean association list by key. Ordering
            // alone therefore never produces a divergence, while a duplicated
            // or missing key still surfaces as an arity or shape mismatch.
            let mut n = Node::leaf("record");
            for (k, v) in map.iter() {
                n = n.with_child(&format!("map[{k}]"), child(&format!("map[{k}]"), v)?);
            }
            n
        }
        ExprKind::ExtensionFunctionApp { fn_name, args } => {
            // The function name is carried through verbatim rather than mapped
            // through a whitelist: an unrecognised name must surface as a
            // mismatch, not be quietly dropped.
            let mut n =
                Node::leaf("call").with_scalar("xfn", fn_name.basename_as_ref().to_string());
            for (i, a) in args.iter().enumerate() {
                n = n.with_child(&format!("args[{i}]"), child(&format!("args[{i}]"), a)?);
            }
            n
        }
        ExprKind::Slot(_) => return unsupported("Slot"),
        ExprKind::Unknown(_) => return unsupported("Unknown"),
        // `ExprKind::Error` exists only under the `tolerant-ast` feature, which
        // this crate does not enable. The match is left exhaustive on purpose:
        // if Cedar adds an expression variant, this stops compiling, which is
        // the outcome we want rather than a catch-all that quietly buckets a
        // new variant as unsupported.
    };

    Ok(node.with_scalar("ty", ty).canonical())
}

/// Is this pair a folded-literal against an unfolded conjunction?
///
/// Returns which side did the folding, or `None` if this is an ordinary
/// constructor disagreement. Only a *boolean* literal counts: an integer or
/// string literal opposite a compound expression is a real disagreement.
fn folded_side(rust: &Node, lean: &Node) -> Option<&'static str> {
    fn is_bool_lit(n: &Node) -> bool {
        n.ctor == "lit"
            && n.children.is_empty()
            && n.scalars
                .get("p")
                .is_some_and(|p| p == r#"{"bool":true}"# || p == r#"{"bool":false}"#)
    }
    fn is_compound(n: &Node) -> bool {
        !n.children.is_empty()
    }
    if is_bool_lit(rust) && is_compound(lean) {
        Some("rust")
    } else if is_bool_lit(lean) && is_compound(rust) {
        Some("lean")
    } else {
        None
    }
}

/// Rust `Var(Action)` against the Lean literal for the environment's own
/// action EUID.
///
/// `action_lit` is the canonical `lit` scalar for that EUID, built by
/// [`action_lit_scalar`] through the same renderer the Rust tree uses, so this
/// check cannot drift from the encoding it is checking.
///
/// Returns false when no environment is in scope, and false for a literal that
/// is any entity other than this environment's action. Both refusals matter:
/// they are what stops the bucket absorbing a substitution of the wrong action.
fn is_action_substitution(rust: &Node, lean: &Node, action_lit: Option<&str>) -> bool {
    let Some(action_lit) = action_lit else {
        return false;
    };
    rust.ctor == "var"
        && rust.scalars.get("v").is_some_and(|v| v == "action")
        && lean.ctor == "lit"
        && lean.scalars.get("p").is_some_and(|p| p == action_lit)
}

/// Compare two rendered trees, returning every disagreement found.
///
/// Comparison stops descending at the first disagreement on a given subtree
/// (a shape mismatch makes its children incomparable) but continues across
/// siblings, so one run reports every independent divergence.
///
/// No environment is supplied, so `Var(Action)` against an action literal is
/// reported as a plain [`Divergence::ShapeMismatch`]. Callers that have the
/// environment should use [`compare_in_env`].
pub fn compare(rust: &Node, lean: &Node, path: &str) -> Vec<Divergence> {
    compare_in_env(rust, lean, path, None)
}

/// [`compare`], with the environment's action literal in scope so that the
/// `substituteAction` difference can be recognised as itself.
pub fn compare_in_env(
    rust: &Node,
    lean: &Node,
    path: &str,
    action_lit: Option<&str>,
) -> Vec<Divergence> {
    let mut out = Vec::new();

    if rust.ctor != lean.ctor {
        // A boolean literal against a compound expression is constant folding,
        // not a shape disagreement. The folded side is a leaf, so there is
        // nothing below it to descend into; the types are all that is left to
        // compare, and they are compared here rather than dropped.
        if let Some(folded) = folded_side(rust, lean) {
            let rust_ty = rust.scalars.get("ty").cloned().unwrap_or_default();
            let lean_ty = lean.scalars.get("ty").cloned().unwrap_or_default();
            out.push(Divergence::ConstantFoldedCondition {
                path: path.to_string(),
                folded,
                types_agree: rust_ty == lean_ty,
                rust_ty,
                lean_ty,
            });
            return out;
        }
        // Lean substituted this environment's action EUID before typechecking
        // and Rust did not. Like constant folding, the substituted side is a
        // leaf with nothing below it to descend into, so the types are all
        // that is left to compare and they are compared here.
        if is_action_substitution(rust, lean, action_lit) {
            let rust_ty = rust.scalars.get("ty").cloned().unwrap_or_default();
            let lean_ty = lean.scalars.get("ty").cloned().unwrap_or_default();
            out.push(Divergence::ActionSubstituted {
                path: path.to_string(),
                action: action_lit.unwrap_or_default().to_string(),
                types_agree: rust_ty == lean_ty,
                rust_ty,
                lean_ty,
            });
            return out;
        }
        out.push(Divergence::ShapeMismatch {
            path: path.to_string(),
            rust: rust.ctor.clone(),
            lean: lean.ctor.clone(),
        });
        return out;
    }

    // Scalars present on both sides must agree. A scalar present on only one
    // side is a shape-level disagreement about node identity.
    let keys: std::collections::BTreeSet<&String> =
        rust.scalars.keys().chain(lean.scalars.keys()).collect();
    for k in keys {
        match (rust.scalars.get(k), lean.scalars.get(k)) {
            (Some(r), Some(l)) if r != l => out.push(Divergence::OperatorMismatch {
                path: path.to_string(),
                field: k.clone(),
                rust: r.clone(),
                lean: l.clone(),
            }),
            (Some(r), None) => out.push(Divergence::OperatorMismatch {
                path: path.to_string(),
                field: k.clone(),
                rust: r.clone(),
                lean: "<absent>".to_string(),
            }),
            (None, Some(l)) => out.push(Divergence::OperatorMismatch {
                path: path.to_string(),
                field: k.clone(),
                rust: "<absent>".to_string(),
                lean: l.clone(),
            }),
            _ => {}
        }
    }

    if rust.children.len() != lean.children.len() {
        out.push(Divergence::ArityMismatch {
            path: path.to_string(),
            rust: rust.children.len(),
            lean: lean.children.len(),
        });
        return out;
    }

    for ((rk, rc), (lk, lc)) in rust.children.iter().zip(lean.children.iter()) {
        if rk != lk {
            out.push(Divergence::ShapeMismatch {
                path: format!("{path}.{rk}"),
                rust: rk.clone(),
                lean: lk.clone(),
            });
            continue;
        }
        out.extend(compare_in_env(rc, lc, &format!("{path}.{rk}"), action_lit));
    }

    out
}

/// Summary of one differential run, in the shape the fuzz target asserts on.
#[derive(Debug, Default)]
pub struct RunReport {
    pub compared: usize,
    pub divergences: Vec<Divergence>,
}

impl RunReport {
    /// Disagreements to act on: everything that is neither a harness problem
    /// nor a declared representational difference.
    pub fn findings(&self) -> Vec<&Divergence> {
        self.divergences
            .iter()
            .filter(|d| !d.is_harness_problem() && !d.is_declared_difference())
            .collect()
    }

    /// Declared representational differences, reported but not acted on.
    pub fn declared_differences(&self) -> Vec<&Divergence> {
        self.divergences
            .iter()
            .filter(|d| d.is_declared_difference())
            .collect()
    }
    pub fn harness_problems(&self) -> Vec<&Divergence> {
        self.divergences
            .iter()
            .filter(|d| d.is_harness_problem())
            .collect()
    }
}

// ---------------------------------------------------------------------------
// End-to-end driver
// ---------------------------------------------------------------------------

/// Environment key. Both sides produce this independently — Lean from
/// `env.reqty`, Rust from `RequestEnv::DeclaredAction` — so results are
/// aligned by key rather than by position in a list.
type EnvKey = (String, String, String);

fn rust_env_key(env: &cedar_policy_core::validator::types::RequestEnv<'_>) -> Option<EnvKey> {
    use cedar_policy_core::validator::types::RequestEnv;
    match env {
        RequestEnv::DeclaredAction {
            principal,
            action,
            resource,
            ..
        } => Some((
            principal.to_string(),
            // Built field by field rather than via `Display for EntityUID`,
            // which renders the eid through `Eid::escaped()`. Lean's
            // `ToString EntityUID` emits the raw eid, so an action whose eid
            // holds a control character escapes on one side only and the two
            // keys never align.
            format!(
                "{}::\"{}\"",
                action.entity_type(),
                <cedar_policy_core::ast::Eid as AsRef<str>>::as_ref(action.eid())
            ),
            resource.to_string(),
        )),
        // Partial validation is not enabled for this target; an undeclared
        // action has no Lean counterpart to align with.
        RequestEnv::UndeclaredAction => None,
    }
}

/// The canonical `lit` scalar for this environment's action EUID.
///
/// Built by handing the EUID to [`literal_json`], the same renderer that
/// produces the Rust tree's literals, rather than by formatting the EUID here.
/// A second formatting path is exactly how the eid double-escaping defect got
/// in, and reusing the renderer makes that class of drift impossible.
fn action_lit_scalar(
    env: &cedar_policy_core::validator::types::RequestEnv<'_>,
) -> Option<String> {
    use cedar_policy_core::validator::types::RequestEnv;
    match env {
        RequestEnv::DeclaredAction { action, .. } => {
            Some(canonical_scalar(&literal_json(
                &cedar_policy_core::ast::Literal::EntityUID(std::sync::Arc::new(
                    (*action).clone(),
                )),
            )))
        }
        RequestEnv::UndeclaredAction => None,
    }
}

/// The typed expression the Rust side offers for comparison, or `None` when it
/// offers none.
///
/// `Irrelevant` carries a typed expression and it is compared: Lean returns an
/// expression for most statically-false (policy, env) pairs, so dropping them
/// here would stop comparing trees the two sides both produce. Which of those
/// pairs Lean instead rejects is handled at the call site by
/// [`is_statically_false`], not by discarding the expression.
fn rust_check_expr(
    check: &cedar_policy_core::validator::typecheck::PolicyCheck,
) -> Option<&cedar_policy_core::ast::Expr<Option<Type>>> {
    use cedar_policy_core::validator::typecheck::PolicyCheck;
    match check {
        PolicyCheck::Success(e) | PolicyCheck::Irrelevant(_, e) => Some(e),
        PolicyCheck::Fail(_) => None,
    }
}

/// Whether the Rust typechecker found the policy always false for this
/// environment, from the scope or from a condition it folded to false.
///
/// This is the only thing that separates a declared
/// [`Divergence::StaticallyFalsePolicy`] from a real
/// [`Divergence::OutcomeMismatch`] when Lean reports an error, so it reads the
/// `PolicyCheck` variant rather than any property of the expression.
fn is_statically_false(check: &cedar_policy_core::validator::typecheck::PolicyCheck) -> bool {
    use cedar_policy_core::validator::typecheck::PolicyCheck;
    matches!(check, PolicyCheck::Irrelevant(_, _))
}

/// Run the typed-expression comparison for one policy set against one schema.
///
/// `vschema` and `policies` drive the Rust typechecker; `ffi_schema` and
/// `ffi_policies` are the same inputs in the form the Lean FFI takes. The
/// caller is responsible for those being the same schema and policy set —
/// this function does not and cannot check it.
///
/// Every disagreement is recorded. Nothing is discarded, and no bucket is
/// suppressed: `RunReport::findings` and `RunReport::harness_problems` split
/// the result into claims about the implementations and claims about this
/// harness.
pub fn run_typed_expr_drt(
    ffi: &cedar_lean_ffi::CedarLeanFfi,
    vschema: &cedar_policy_core::validator::ValidatorSchema,
    policies: &cedar_policy_core::ast::PolicySet,
    ffi_schema: &cedar_policy::Schema,
    ffi_policies: &cedar_policy::PolicySet,
) -> Result<RunReport, cedar_lean_ffi::FfiError> {
    use cedar_policy_core::validator::ValidationMode;
    use cedar_policy_core::validator::typecheck::Typechecker;

    let lean_results = ffi.typecheck_policy_typed(
        ffi_policies,
        ffi_schema,
        &cedar_policy::ValidationMode::Strict,
    )?;

    let mut report = RunReport::default();

    // Index the Lean side by (policy id, env key).
    let mut lean_by_key: HashMap<(String, EnvKey), &LeanTypedExprEnvResult> = HashMap::new();
    for p in &lean_results {
        for e in &p.envs {
            lean_by_key.insert((p.policy_id.clone(), e.env_key()), e);
        }
    }
    let mut seen: HashSet<(String, EnvKey)> = HashSet::new();

    let tc = Typechecker::new(vschema, ValidationMode::Strict);
    for template in policies.all_templates() {
        // `Display for PolicyID` escapes via `escape_debug`, so a policy id
        // containing control characters renders as `\\0` here and as a raw NUL
        // on the Lean side, and the two never align. Use the raw string.
        let pid = template.id().as_ref().to_string();
        for (env, check) in tc.typecheck_by_request_env(template) {
            let Some(key) = rust_env_key(&env) else {
                continue;
            };
            let full = (pid.clone(), key.clone());
            let env_str = format!("{}, {}, {}", key.0, key.1, key.2);

            let Some(lean) = lean_by_key.get(&full) else {
                report.divergences.push(Divergence::EnvUnmatched {
                    policy: pid.clone(),
                    env: env_str,
                });
                continue;
            };
            seen.insert(full);
            report.compared += 1;

            let rust_expr = rust_check_expr(&check);

            match (rust_expr, &lean.typed_expr) {
                // Both sides failed to typecheck. Agreement on rejection; the
                // reason is out of scope for this target.
                (None, None) => {}
                // Rust found the policy always false for this environment,
                // from the scope or from a condition it folded to false, and
                // Lean reported an error. Neither side offers an expression to
                // compare and both decline for the same reason, so this is
                // declared rather than reported as a disagreement. A Rust
                // SUCCESS against a Lean error does not come here and stays an
                // `OutcomeMismatch`.
                (Some(_), None) if is_statically_false(&check) => {
                    report.divergences.push(Divergence::StaticallyFalsePolicy {
                        policy: pid.clone(),
                        env: env_str,
                    });
                }
                (Some(_), None) | (None, Some(_)) => {
                    report.divergences.push(Divergence::OutcomeMismatch {
                        policy: pid.clone(),
                        env: env_str,
                        rust_ok: rust_expr.is_some(),
                        lean_ok: lean.typed_expr.is_some(),
                    });
                }
                (Some(r), Some(l)) => {
                    let root = format!("{pid}[{env_str}]");
                    let action_lit = action_lit_scalar(&env);
                    match (rust_to_node(r, &root), lean_to_node(l, &root)) {
                        (Ok(rn), Ok(ln)) => report.divergences.extend(compare_in_env(
                            &rn,
                            &ln,
                            &root,
                            action_lit.as_deref(),
                        )),
                        (Err(d), _) | (_, Err(d)) => report.divergences.push(d),
                    }
                }
            }
        }
    }

    // A (policy, env) the Lean side produced and the Rust side never visited
    // is an alignment failure, not silence.
    for (pid, key) in lean_by_key.keys() {
        if !seen.contains(&(pid.clone(), key.clone())) {
            report.divergences.push(Divergence::EnvUnmatched {
                policy: pid.clone(),
                env: format!("{}, {}, {}", key.0, key.1, key.2),
            });
        }
    }

    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    /// The Lean encoding observed from `lake env lean` on the real build:
    /// `(true && 1 < 2)` with `anyBool` annotations.
    fn lean_sample() -> Value {
        json!({"and": {
            "ty": {"bool": {"bty": "anyBool"}},
            "a": {"lit": {"ty": {"bool": {"bty": "anyBool"}}, "p": {"bool": true}}},
            "b": {"binaryApp": {
                "ty": {"bool": {"bty": "anyBool"}},
                "op": "less",
                "a": {"lit": {"ty": "int", "p": {"int": 1}}},
                "b": {"lit": {"ty": "int", "p": {"int": 2}}}}}}})
    }

    #[test]
    fn parses_the_real_lean_encoding() {
        let n = lean_to_node(&lean_sample(), "$").expect("should parse");
        assert_eq!(n.ctor, "and");
        assert_eq!(n.children.len(), 2);
    }

    /// POSITIVE CONTROL (clean case): a tree compared against itself must
    /// produce zero divergences. If this fails, every clean result is worthless.
    #[test]
    fn identical_trees_agree() {
        let a = lean_to_node(&lean_sample(), "$").unwrap();
        let b = lean_to_node(&lean_sample(), "$").unwrap();
        assert_eq!(compare(&a, &b, "$"), vec![]);
    }

    /// NEGATIVE CONTROL 1: a planted *type* divergence must be caught and
    /// classified as OPERATOR_MISMATCH on the `ty` field.
    #[test]
    fn negative_control_type_divergence_is_caught() {
        let clean = lean_to_node(&lean_sample(), "$").unwrap();
        // Plant: the inner `1` is annotated `bool` instead of `int`.
        let mut tampered = lean_sample();
        tampered["and"]["b"]["binaryApp"]["a"]["lit"]["ty"] = json!("bool");
        let tampered = lean_to_node(&tampered, "$").unwrap();

        let ds = compare(&clean, &tampered, "$");
        assert_eq!(ds.len(), 1, "expected exactly one divergence, got {ds:?}");
        assert_eq!(ds[0].bucket(), "OPERATOR_MISMATCH");
        match &ds[0] {
            Divergence::OperatorMismatch {
                path,
                field,
                rust,
                lean,
            } => {
                assert_eq!(field, "ty");
                assert_eq!(path, "$.b.a");
                assert_eq!(rust, "int");
                assert_eq!(lean, "bool");
            }
            other => panic!("wrong bucket: {other:?}"),
        }
    }

    /// NEGATIVE CONTROL 2: a planted *structural* divergence must be caught
    /// and classified as SHAPE_MISMATCH, not silently absorbed.
    #[test]
    fn negative_control_shape_divergence_is_caught() {
        let clean = lean_to_node(&lean_sample(), "$").unwrap();
        let mut tampered = lean_sample();
        // Plant: `and` becomes `or` at the root.
        let inner = tampered["and"].take();
        tampered = json!({ "or": inner });
        let tampered = lean_to_node(&tampered, "$").unwrap();

        let ds = compare(&clean, &tampered, "$");
        assert_eq!(ds.len(), 1);
        assert_eq!(ds[0].bucket(), "SHAPE_MISMATCH");
    }

    /// NEGATIVE CONTROL 3: a planted *arity* divergence must be caught.
    #[test]
    fn negative_control_arity_divergence_is_caught() {
        let clean_json = json!({"set": {"ty": "int", "ls": [
            {"lit": {"ty": "int", "p": {"int": 1}}},
            {"lit": {"ty": "int", "p": {"int": 2}}}]}});
        let short_json = json!({"set": {"ty": "int", "ls": [
            {"lit": {"ty": "int", "p": {"int": 1}}}]}});
        let clean = lean_to_node(&clean_json, "$").unwrap();
        let short = lean_to_node(&short_json, "$").unwrap();

        let ds = compare(&clean, &short, "$");
        assert_eq!(ds.len(), 1);
        assert_eq!(ds[0].bucket(), "ARITY_MISMATCH");
    }

    // -----------------------------------------------------------------
    // Cross-renderer controls
    // -----------------------------------------------------------------
    //
    // The controls above compare `lean_to_node` against itself: they establish
    // that `compare` can fire, but they do not exercise `rust_to_node` and so
    // say nothing about whether the two renderers agree.
    //
    // The controls below run BOTH renderers over the same expression. Each is
    // two-halved: the clean pair must produce zero divergences and the
    // tampered pair must produce exactly one classified divergence, asserted
    // in the same test, so a control that catches its plant has also shown the
    // correct case passing.
    //
    // These are still not an end-to-end Rust-vs-Lean run. The Lean side is a
    // JSON literal captured from `lake env lean` against this build, not a
    // live FFI call. What they establish is that the two renderers agree on
    // the observed encoding and that the comparison fires on each divergence
    // class. Whether the two typecheckers agree is not tested here and is not
    // claimed anywhere in this module.

    use cedar_policy_core::ast::{ExprBuilder, Pattern, PatternElem};
    use cedar_policy_core::expr_builder::ExprBuilder as _;
    use cedar_policy_core::validator::types::{EntityKind, EntityLUB, Type};

    fn t_bool() -> Option<Type> {
        Some(Type::primitive_boolean())
    }
    fn t_long() -> Option<Type> {
        Some(Type::primitive_long())
    }

    /// Rust side of `true && 1 < 2`, annotated to match `lean_sample()`.
    fn rust_sample() -> cedar_policy_core::ast::Expr<Option<Type>> {
        let lit_true = ExprBuilder::with_data(t_bool()).val(true);
        let one = ExprBuilder::with_data(t_long()).val(1i64);
        let two = ExprBuilder::with_data(t_long()).val(2i64);
        let cmp = ExprBuilder::with_data(t_bool()).less(one, two);
        ExprBuilder::with_data(t_bool()).and(lit_true, cmp)
    }

    fn expect_one(ds: &[Divergence], bucket: &str) {
        assert_eq!(ds.len(), 1, "expected exactly one divergence, got {ds:?}");
        assert_eq!(ds[0].bucket(), bucket, "wrong bucket: {:?}", ds[0]);
    }

    /// CROSS-RENDERER CONTROL 1 — the headline class.
    ///
    /// A type-annotation divergence must be caught. This is precisely the
    /// class that projecting both sides through an untyped expression would
    /// erase, since the two trees are structurally identical and differ only
    /// in one node's `ty`.
    #[test]
    fn cross_renderer_type_divergence_two_halved() {
        // Clean half: independently rendered Rust and Lean trees agree.
        let rust = rust_to_node(&rust_sample(), "$").expect("rust render");
        let lean = lean_to_node(&lean_sample(), "$").expect("lean parse");
        assert_eq!(
            compare(&rust, &lean, "$"),
            vec![],
            "clean half must produce no divergence"
        );

        // Broken half: the Rust `1` is annotated Bool instead of Long. Nothing
        // structural changes; only the annotation differs.
        let one = ExprBuilder::with_data(t_bool()).val(1i64);
        let two = ExprBuilder::with_data(t_long()).val(2i64);
        let cmp = ExprBuilder::with_data(t_bool()).less(one, two);
        let tampered =
            ExprBuilder::with_data(t_bool()).and(ExprBuilder::with_data(t_bool()).val(true), cmp);

        let rust_bad = rust_to_node(&tampered, "$").expect("rust render");
        let ds = compare(&rust_bad, &lean, "$");
        expect_one(&ds, "OPERATOR_MISMATCH");
        match &ds[0] {
            Divergence::OperatorMismatch {
                path,
                field,
                rust,
                lean,
            } => {
                assert_eq!(field, "ty");
                assert_eq!(path, "$.b.a");
                assert_eq!(rust, r#"{"bool":{"bty":"anyBool"}}"#);
                assert_eq!(lean, "int");
            }
            other => panic!("wrong shape: {other:?}"),
        }
    }

    /// CROSS-RENDERER CONTROL 2 — `Option<Type>` against a total `CedarType`.
    ///
    /// Lean's `TypedExpr` annotates every node with a `CedarType`; Rust's is
    /// `Option<Type>` and can be `None`. An unannotated Rust node must not
    /// silently match whatever Lean inferred. This divergence class cannot
    /// even be stated in an untyped target representation.
    #[test]
    fn cross_renderer_missing_annotation_two_halved() {
        let lean = lean_to_node(&lean_sample(), "$").expect("lean parse");

        // Clean half.
        let rust = rust_to_node(&rust_sample(), "$").expect("rust render");
        assert_eq!(compare(&rust, &lean, "$"), vec![]);

        // Broken half: the `1` carries no annotation at all.
        let one = ExprBuilder::with_data(None).val(1i64);
        let two = ExprBuilder::with_data(t_long()).val(2i64);
        let cmp = ExprBuilder::with_data(t_bool()).less(one, two);
        let tampered =
            ExprBuilder::with_data(t_bool()).and(ExprBuilder::with_data(t_bool()).val(true), cmp);

        let rust_bad = rust_to_node(&tampered, "$").expect("rust render");
        let ds = compare(&rust_bad, &lean, "$");
        expect_one(&ds, "OPERATOR_MISMATCH");
        match &ds[0] {
            Divergence::OperatorMismatch { field, rust, .. } => {
                assert_eq!(field, "ty");
                assert_eq!(rust, r#"{"__unannotated__":true}"#);
            }
            other => panic!("wrong shape: {other:?}"),
        }
    }

    /// CROSS-RENDERER CONTROL 3 — operator divergence survives the fold.
    #[test]
    fn cross_renderer_operator_divergence_two_halved() {
        let lean = lean_to_node(&lean_sample(), "$").expect("lean parse");
        assert_eq!(
            compare(&rust_to_node(&rust_sample(), "$").unwrap(), &lean, "$"),
            vec![]
        );

        let one = ExprBuilder::with_data(t_long()).val(1i64);
        let two = ExprBuilder::with_data(t_long()).val(2i64);
        // `lesseq` where Lean has `less`.
        let cmp = ExprBuilder::with_data(t_bool()).lesseq(one, two);
        let tampered =
            ExprBuilder::with_data(t_bool()).and(ExprBuilder::with_data(t_bool()).val(true), cmp);

        let ds = compare(&rust_to_node(&tampered, "$").unwrap(), &lean, "$");
        expect_one(&ds, "OPERATOR_MISMATCH");
        match &ds[0] {
            Divergence::OperatorMismatch {
                field, rust, lean, ..
            } => {
                assert_eq!(field, "op");
                assert_eq!(rust, "lessEq");
                assert_eq!(lean, "less");
            }
            other => panic!("wrong shape: {other:?}"),
        }
    }

    /// CROSS-RENDERER CONTROL 4 — the declared `Like` fold.
    ///
    /// Rust represents `like` as its own AST variant; Lean represents it as
    /// `unaryApp` with a `like` operator carrying the pattern. The fold must
    /// make the matching case agree *and* must still catch a pattern that
    /// differs.
    #[test]
    fn cross_renderer_like_fold_two_halved() {
        // Captured from `lake env lean` on this build:
        //   TypedExpr.unaryApp (.like [.star, .justChar 'a']) (.lit (.string "s") .string) (.bool .anyBool)
        let lean_like = json!({"unaryApp": {
            "ty": {"bool": {"bty": "anyBool"}},
            "op": {"like": {"p": ["star", {"justChar": {"c": 97}}]}},
            "expr": {"lit": {"ty": "string", "p": {"string": "s"}}}}});
        let lean = lean_to_node(&lean_like, "$").expect("lean parse");

        let s = ExprBuilder::with_data(Some(Type::primitive_string())).val("s");
        let pat = Pattern::from(vec![PatternElem::Wildcard, PatternElem::Char('a')]);
        let rust = ExprBuilder::with_data(t_bool()).like(s, pat);
        assert_eq!(
            compare(&rust_to_node(&rust, "$").unwrap(), &lean, "$"),
            vec![],
            "the Like fold must make the matching case agree"
        );

        // Broken half: a different pattern must still be caught.
        let s2 = ExprBuilder::with_data(Some(Type::primitive_string())).val("s");
        let pat2 = Pattern::from(vec![PatternElem::Wildcard, PatternElem::Char('b')]);
        let rust_bad = ExprBuilder::with_data(t_bool()).like(s2, pat2);
        let ds = compare(&rust_to_node(&rust_bad, "$").unwrap(), &lean, "$");
        expect_one(&ds, "OPERATOR_MISMATCH");
    }

    /// REGRESSION GUARD — entity-type field order must not manufacture a
    /// divergence.
    ///
    /// `cedar-policy-core` enables serde_json's `preserve_order`, so object
    /// key order is insertion order. Lean emits `{"path": .., "id": ..}`; the
    /// natural Rust construction order is the reverse. Without the sorted
    /// rendering in `canonical_scalar` every entity-typed node would report a
    /// phantom mismatch, and the target would look like it had found something.
    #[test]
    fn entity_type_field_order_is_not_a_divergence() {
        // Captured from `lake env lean`: note `path` precedes `id`.
        let lean_var = json!({"var": {
            "v": "principal",
            "ty": {"entity": {"ety": {"path": ["NS"], "id": "User"}}}}});
        let lean = lean_to_node(&lean_var, "$").expect("lean parse");

        let ety: cedar_policy_core::ast::EntityType = "NS::User"
            .parse::<cedar_policy_core::ast::Name>()
            .unwrap()
            .into();
        let ty = Some(Type::Entity(EntityKind::Entity(EntityLUB::single_entity(
            ety,
        ))));
        let rust = ExprBuilder::with_data(ty).var(cedar_policy_core::ast::Var::Principal);

        assert_eq!(
            compare(&rust_to_node(&rust, "$").unwrap(), &lean, "$"),
            vec![],
            "field order alone must never be reported as a divergence"
        );
    }

    /// Seventh phantom-divergence class, found by re-running the target after
    /// the survey switch was removed. `Eid::escaped()` is a Rust display
    /// convention: it renders a control character as the literal text `\u{7}`,
    /// which serde then escapes again. Lean emits the raw character and its
    /// JSON encoder escapes it once. Rendering the Rust eid through
    /// `escaped()` made every entity literal holding a control character
    /// mismatch, in the harness rather than in either typechecker.
    ///
    /// The environment-key fix (phantom class 5) addressed the same cause at a
    /// different site and did not reach this one.
    #[test]
    fn control_character_in_entity_literal_is_not_a_divergence() {
        // Lean's encoder emits the raw eid; serde_json parses "" to it.
        let lean_lit = json!({"lit": {
            "p": {"entityUID": {"ty": {"id": "a", "path": []}, "eid": "\u{7}"}},
            "ty": {"entity": {"ety": {"path": [], "id": "a"}}}}});
        let lean = lean_to_node(&lean_lit, "$").expect("lean parse");

        let uid: cedar_policy_core::ast::EntityUID = r#"a::"\u{7}""#.parse().expect("euid parse");
        let ety: cedar_policy_core::ast::EntityType =
            "a".parse::<cedar_policy_core::ast::Name>().unwrap().into();
        let ty = Some(Type::Entity(EntityKind::Entity(EntityLUB::single_entity(
            ety,
        ))));
        let rust = ExprBuilder::with_data(ty).val(uid);

        assert_eq!(
            compare(&rust_to_node(&rust, "$").unwrap(), &lean, "$"),
            vec![],
            "eid escaping alone must never be reported as a divergence"
        );
    }

    /// The other half: a genuinely different eid is still caught, so the fix
    /// above widened nothing.
    #[test]
    fn differing_entity_literal_eid_is_still_caught() {
        let lean_lit = json!({"lit": {
            "p": {"entityUID": {"ty": {"id": "a", "path": []}, "eid": "\u{7}"}},
            "ty": {"entity": {"ety": {"path": [], "id": "a"}}}}});
        let lean = lean_to_node(&lean_lit, "$").expect("lean parse");

        let uid: cedar_policy_core::ast::EntityUID = r#"a::"\u{8}""#.parse().expect("euid parse");
        let ety: cedar_policy_core::ast::EntityType =
            "a".parse::<cedar_policy_core::ast::Name>().unwrap().into();
        let ty = Some(Type::Entity(EntityKind::Entity(EntityLUB::single_entity(
            ety,
        ))));
        let rust = ExprBuilder::with_data(ty).val(uid);

        let ds = compare(&rust_to_node(&rust, "$").unwrap(), &lean, "$");
        expect_one(&ds, "OPERATOR_MISMATCH");
    }

    // -----------------------------------------------------------------
    // End-to-end: real Rust typechecker against the real Lean backend
    // -----------------------------------------------------------------

    const E2E_SCHEMA: &str = r#"
        entity User { name: String, age: Long };
        entity Account { balance: Long, owner: String };
        action transfer appliesTo {
          principal: User,
          resource: Account,
          context: { amount: Long, memo: String }
        };
    "#;

    const E2E_POLICIES: &str = r#"
        permit(principal, action == Action::"transfer", resource)
        when { context.amount < 1000 };

        permit(principal is User, action == Action::"transfer", resource)
        when { principal.name like "a*" && resource.balance >= 0 };

        forbid(principal, action == Action::"transfer", resource)
        when { principal.age < 18 || context.memo == "" };
    "#;

    fn e2e_inputs() -> (
        cedar_policy_core::validator::ValidatorSchema,
        cedar_policy_core::ast::PolicySet,
        cedar_policy::Schema,
        cedar_policy::PolicySet,
    ) {
        use std::str::FromStr;
        // Parsed twice from the same source: once into the core types the Rust
        // typechecker takes, once into the public types the FFI takes.
        let vschema =
            cedar_policy_core::validator::ValidatorSchema::from_str(E2E_SCHEMA).expect("vschema");
        let policies = cedar_policy_core::parser::parse_policyset(E2E_POLICIES).expect("policies");
        let ffi_schema = cedar_policy::Schema::from_str(E2E_SCHEMA).expect("ffi schema");
        let ffi_policies = cedar_policy::PolicySet::from_str(E2E_POLICIES).expect("ffi policies");
        (vschema, policies, ffi_schema, ffi_policies)
    }

    /// END-TO-END RUN. Calls the real Rust typechecker and the real Lean
    /// backend on the same policies, and reports whatever comes back.
    ///
    /// This test asserts that the harness ran and produced no *harness*
    /// problems. It deliberately does NOT assert that the two typecheckers
    /// agree: that is the question the target exists to ask, and baking the
    /// expected answer into an assertion would make a real disagreement look
    /// like a broken test rather than a finding.
    #[test]
    fn end_to_end_rust_vs_lean() {
        let (vschema, policies, ffi_schema, ffi_policies) = e2e_inputs();
        let ffi = cedar_lean_ffi::CedarLeanFfi::new();

        let report = run_typed_expr_drt(&ffi, &vschema, &policies, &ffi_schema, &ffi_policies)
            .expect("Lean FFI call failed");

        println!(
            "compared {} (policy, env) pairs; {} findings, {} harness problems",
            report.compared,
            report.findings().len(),
            report.harness_problems().len()
        );
        for d in &report.divergences {
            println!("  [{}] {d:?}", d.bucket());
        }

        assert!(
            report.compared > 0,
            "the run compared nothing — a vacuous pass"
        );
        assert_eq!(
            report.harness_problems().len(),
            0,
            "harness problems must be fixed before any finding is believable: {:?}",
            report.harness_problems()
        );
    }

    /// END-TO-END NEGATIVE CONTROL, two-halved.
    ///
    /// The clean half is the run above. The broken half perturbs the Rust
    /// typed expression after typechecking and shows the same comparison path
    /// reports it. Without this, a clean end-to-end run is indistinguishable
    /// from a comparison that cannot fire on real input.
    ///
    /// KNOWN ISSUE: the broken half panics through
    /// `.expect("at least one policy must typecheck on the Rust side")` on any
    /// input where every `PolicyCheck` is `Irrelevant`, because it needs one
    /// real typed expression to plant a fault into and takes the first it
    /// finds. `E2E_POLICIES` is fixed and does typecheck, so it cannot fire
    /// today; it would become reachable if these inputs were ever generated.
    /// Pre-existing and not introduced by the `rust_check_expr` seam, which
    /// keeps returning the expression `Irrelevant` carries.
    #[test]
    fn end_to_end_negative_control_two_halved() {
        use cedar_policy_core::validator::ValidationMode;
        use cedar_policy_core::validator::typecheck::{PolicyCheck, Typechecker};

        let (vschema, policies, ffi_schema, ffi_policies) = e2e_inputs();
        let ffi = cedar_lean_ffi::CedarLeanFfi::new();

        // Clean half.
        let clean =
            run_typed_expr_drt(&ffi, &vschema, &policies, &ffi_schema, &ffi_policies).expect("ffi");
        assert!(clean.compared > 0);
        let clean_findings = clean.findings().len();

        // Broken half: take one real typechecked expression from the run above
        // and compare it against a Lean tree it must not match.
        let lean_results = ffi
            .typecheck_policy_typed(
                &ffi_policies,
                &ffi_schema,
                &cedar_policy::ValidationMode::Strict,
            )
            .expect("ffi");
        let lean_tree = lean_results
            .iter()
            .flat_map(|p| p.envs.iter())
            .find_map(|e| e.typed_expr.as_ref())
            .expect("at least one policy must typecheck on the Lean side");

        let tc = Typechecker::new(&vschema, ValidationMode::Strict);
        let template = policies.all_templates().next().expect("a policy");
        let rust_expr = tc
            .typecheck_by_request_env(template)
            .find_map(|(_, c)| match c {
                PolicyCheck::Success(e) | PolicyCheck::Irrelevant(_, e) => Some(e),
                PolicyCheck::Fail(_) => None,
            })
            .expect("at least one policy must typecheck on the Rust side");

        // Plant: strip the root annotation. Structure is untouched.
        let stripped = ExprBuilder::with_data(None).and(rust_expr.clone(), rust_expr.clone());
        let rn = rust_to_node(&stripped, "$").expect("render");
        let ln = lean_to_node(lean_tree, "$").expect("parse");
        let ds = compare(&rn, &ln, "$");
        assert!(
            !ds.is_empty(),
            "the planted divergence was absorbed — the comparison cannot fire on real input"
        );

        println!(
            "clean half: {clean_findings} findings over {} pairs; broken half: {} divergences",
            clean.compared,
            ds.len()
        );
    }

    /// CONSTANT-FOLDING CONTROL, two-halved.
    ///
    /// A statically-true policy condition is folded to `lit true` by the Rust
    /// typechecker and kept as a conjunction by Lean. The clean half is that
    /// this lands in its own bucket with the two types reconciled as equal.
    /// The broken half is that a genuine constructor disagreement, and a
    /// folded pair whose types DISAGREE, are both still reported.
    #[test]
    fn constant_folded_condition_two_halved() {
        let lean_and = lean_to_node(&lean_sample(), "$").expect("lean parse");

        // Clean half: Rust folded to `true`, both sides type it anyBool.
        let rust_folded = ExprBuilder::with_data(t_bool()).val(true);
        let ds = compare(&rust_to_node(&rust_folded, "$").unwrap(), &lean_and, "$");
        assert_eq!(ds.len(), 1, "expected one divergence, got {ds:?}");
        assert_eq!(ds[0].bucket(), "CONSTANT_FOLDED_CONDITION");
        match &ds[0] {
            Divergence::ConstantFoldedCondition {
                folded,
                types_agree,
                ..
            } => {
                assert_eq!(*folded, "rust");
                assert!(types_agree, "both sides type the condition anyBool");
            }
            other => panic!("wrong shape: {other:?}"),
        }

        // Broken half 1: same folding, but the types disagree. Must still be
        // reported as a disagreement rather than reconciled away.
        let rust_folded_long = ExprBuilder::with_data(t_long()).val(true);
        let ds = compare(
            &rust_to_node(&rust_folded_long, "$").unwrap(),
            &lean_and,
            "$",
        );
        assert_eq!(ds.len(), 1);
        match &ds[0] {
            Divergence::ConstantFoldedCondition { types_agree, .. } => {
                assert!(!types_agree, "a type disagreement must not be reconciled");
            }
            other => panic!("wrong shape: {other:?}"),
        }

        // Broken half 2: a non-boolean literal against a compound expression
        // is a real shape disagreement and must NOT be absorbed into the
        // folding bucket.
        let rust_int = ExprBuilder::with_data(t_long()).val(1i64);
        let ds = compare(&rust_to_node(&rust_int, "$").unwrap(), &lean_and, "$");
        assert_eq!(ds.len(), 1);
        assert_eq!(
            ds[0].bucket(),
            "SHAPE_MISMATCH",
            "an int literal opposite a conjunction is not constant folding"
        );
    }

    /// A malformed Lean tree is a HARNESS problem, never a finding about
    /// either implementation. Fail-open here would manufacture phantom results.
    #[test]
    fn malformed_lean_json_is_a_harness_problem() {
        let bad = json!({"and": {"ty": "bool"}, "or": {"ty": "bool"}});
        let err = lean_to_node(&bad, "$").expect_err("two tags must be rejected");
        assert_eq!(err.bucket(), "MALFORMED_LEAN_JSON");
        assert!(err.is_harness_problem());
    }

    // -----------------------------------------------------------------
    // Statically-false policies (`PolicyCheck::Irrelevant`)
    // -----------------------------------------------------------------

    /// Entity types are enums because that is what the corpus case below uses;
    /// the reproducer is kept verbatim rather than minimised by guesswork.
    const SF_SCHEMA: &str = r#"
        entity a enum [""];
        action "action" appliesTo { principal: a, resource: a, context: {} };
    "#;

    /// Taken verbatim from a corpus input that produces the declared
    /// difference. Rust folds the condition to statically false and returns
    /// `PolicyCheck::Irrelevant`; Lean's `typecheckPolicy` returns an error.
    const SF_POLICY: &str = r#"forbid(principal, action in Action::"action", resource) when { ((true && ((ip("::ffff:255.255.48.48")).isMulticast())) && false) && false };"#;

    /// A statically-false policy for which Lean DOES return a typed
    /// expression. The corpus says this is the common case: of 8,976
    /// `Irrelevant` pairs, Lean returns an expression for 7,969 of them.
    const SF_COMPARED_SCHEMA: &str = r#"
        entity User { name: String };
        entity Account { balance: Long };
        action transfer appliesTo { principal: User, resource: Account };
        action close appliesTo { principal: User, resource: Account };
    "#;
    const SF_COMPARED_POLICY: &str = r#"
        permit(principal, action == Action::"transfer", resource)
        when { resource.balance < 1000 };
    "#;

    fn run_src(schema: &str, policies: &str) -> RunReport {
        use std::str::FromStr;
        let vschema =
            cedar_policy_core::validator::ValidatorSchema::from_str(schema).expect("vschema");
        let core_policies = cedar_policy_core::parser::parse_policyset(policies).expect("policies");
        let ffi_schema = cedar_policy::Schema::from_str(schema).expect("ffi schema");
        let ffi_policies = cedar_policy::PolicySet::from_str(policies).expect("ffi policies");
        let ffi = cedar_lean_ffi::CedarLeanFfi::new();
        run_typed_expr_drt(&ffi, &vschema, &core_policies, &ffi_schema, &ffi_policies)
            .expect("Lean FFI call failed")
    }

    /// Collect the Rust `PolicyCheck` for each request environment, keyed by
    /// the action in that environment.
    fn checks_by_action(
        schema: &str,
        policies: &str,
    ) -> Vec<(String, cedar_policy_core::validator::typecheck::PolicyCheck)> {
        use cedar_policy_core::validator::ValidationMode;
        use cedar_policy_core::validator::typecheck::Typechecker;
        use std::str::FromStr;
        let vschema =
            cedar_policy_core::validator::ValidatorSchema::from_str(schema).expect("vschema");
        let core_policies = cedar_policy_core::parser::parse_policyset(policies).expect("policies");
        let tc = Typechecker::new(&vschema, ValidationMode::Strict);
        let mut out = Vec::new();
        for t in core_policies.all_templates() {
            for (env, check) in tc.typecheck_by_request_env(t) {
                if let Some(k) = rust_env_key(&env) {
                    out.push((k.1, check));
                }
            }
        }
        out
    }

    const AS_SCHEMA: &str = r#"
        entity User { name: String };
        entity Account { balance: Long };
        action transfer appliesTo { principal: User, resource: Account };
        action close appliesTo { principal: User, resource: Account };
    "#;

    /// The condition mentions `action`, so the substitution reaches the typed
    /// expression instead of being confined to the scope.
    const AS_POLICY: &str = r#"
        permit(principal, action == Action::"transfer", resource)
        when { action == Action::"transfer" };
    "#;

    /// The canonical `lit` scalar for an action EUID, built the way the
    /// production helper builds it.
    fn action_lit_of(src: &str) -> String {
        let uid: cedar_policy_core::ast::EntityUID = src.parse().expect("euid parse");
        canonical_scalar(&literal_json(&Literal::EntityUID(std::sync::Arc::new(uid))))
    }

    fn action_entity_ty(name: &str) -> Option<Type> {
        let ety: cedar_policy_core::ast::EntityType = name
            .parse::<cedar_policy_core::ast::Name>()
            .unwrap()
            .into();
        Some(Type::Entity(EntityKind::Entity(EntityLUB::single_entity(
            ety,
        ))))
    }

    /// ACTION-SUBSTITUTION CONTROL, two-halved.
    ///
    /// Clean half: Rust keeps `Var(Action)` where Lean has this environment's
    /// action literal, both sides type it the same, and that lands in its own
    /// declared bucket.
    ///
    /// Three broken halves, and they are the whole reason the bucket is safe.
    /// A different action, a type disagreement, and the absence of an
    /// environment must each stay a finding, so the declaration cannot widen
    /// into "any var against any literal".
    #[test]
    fn action_substitution_two_halved() {
        let transfer = action_lit_of(r#"Action::"transfer""#);
        let lean_lit = json!({"lit": {
            "p": {"entityUID": {"ty": {"path": [], "id": "Action"}, "eid": "transfer"}},
            "ty": {"entity": {"ety": {"path": [], "id": "Action"}}}}});
        let lean = lean_to_node(&lean_lit, "$").expect("lean parse");

        let rust = ExprBuilder::with_data(action_entity_ty("Action"))
            .var(cedar_policy_core::ast::Var::Action);
        let rust_node = rust_to_node(&rust, "$").unwrap();

        // Clean half.
        let ds = compare_in_env(&rust_node, &lean, "$", Some(&transfer));
        assert_eq!(ds.len(), 1, "expected one divergence, got {ds:?}");
        assert_eq!(ds[0].bucket(), "ACTION_SUBSTITUTED");
        match &ds[0] {
            Divergence::ActionSubstituted { types_agree, .. } => {
                assert!(types_agree, "both sides type the node as the action entity");
            }
            other => panic!("wrong shape: {other:?}"),
        }
        assert!(
            ds[0].is_declared_difference(),
            "the clean case must not be a finding"
        );

        // Broken half 1: a DIFFERENT action. Substituting the wrong action is
        // exactly what this bucket must never absorb.
        let close = action_lit_of(r#"Action::"close""#);
        let ds = compare_in_env(&rust_node, &lean, "$", Some(&close));
        assert_eq!(ds.len(), 1);
        assert_eq!(
            ds[0].bucket(),
            "SHAPE_MISMATCH",
            "a literal that is not this environment's action is not the declared case"
        );
        assert!(!ds[0].is_declared_difference());

        // Broken half 2: this environment's action, but the two sides give the
        // node different types.
        let rust_wrong_ty = ExprBuilder::with_data(t_long())
            .var(cedar_policy_core::ast::Var::Action);
        let ds = compare_in_env(
            &rust_to_node(&rust_wrong_ty, "$").unwrap(),
            &lean,
            "$",
            Some(&transfer),
        );
        assert_eq!(ds.len(), 1);
        assert_eq!(ds[0].bucket(), "ACTION_SUBSTITUTED");
        match &ds[0] {
            Divergence::ActionSubstituted { types_agree, .. } => {
                assert!(!types_agree, "a type disagreement must not be reconciled");
            }
            other => panic!("wrong shape: {other:?}"),
        }
        assert!(
            !ds[0].is_declared_difference(),
            "a type disagreement stays a finding"
        );

        // Broken half 3: no environment in scope. `compare` must not guess.
        let ds = compare(&rust_node, &lean, "$");
        assert_eq!(ds.len(), 1);
        assert_eq!(
            ds[0].bucket(),
            "SHAPE_MISMATCH",
            "without an environment there is nothing to recognise the literal against"
        );
    }

    /// The substitution end to end against the real Lean backend, so Lean's
    /// substitution is observed here rather than assumed from the source.
    ///
    /// This is the test that records why the declaration exists: before it,
    /// `findings()` was non-empty on this ordinary two-action policy and the
    /// fuzz target panicked on it.
    #[test]
    fn action_substitution_is_declared_end_to_end() {
        let report = run_src(AS_SCHEMA, AS_POLICY);
        assert_eq!(
            report.harness_problems().len(),
            0,
            "harness problems must be fixed before any finding is believable: {:?}",
            report.harness_problems()
        );
        let substituted = report
            .divergences
            .iter()
            .filter(|d| d.bucket() == "ACTION_SUBSTITUTED")
            .count();
        assert!(
            substituted > 0,
            "test premise: this policy must produce the substitution, got {:?}",
            report.divergences
        );
        assert!(
            report.findings().is_empty(),
            "a declared difference must not be a finding: {:?}",
            report.findings()
        );
        assert!(
            report.declared_differences().len() >= substituted,
            "it must still be recorded and reported, not dropped"
        );
        println!(
            "end-to-end: {} pairs compared, {substituted} ACTION_SUBSTITUTED, {} findings",
            report.compared,
            report.findings().len()
        );
    }

    /// Eighth phantom-divergence class.
    ///
    /// `PolicyCheck::Irrelevant` means the Rust typechecker found the policy
    /// statically false for this environment. For some of those pairs Lean's
    /// `typecheckPolicy` returns an error. Neither side then offers a typed
    /// expression, and both decline for the same reason, so reporting it as an
    /// `OutcomeMismatch` claimed a disagreement that is not there.
    ///
    /// It is declared rather than silenced: the bucket is still recorded and
    /// still counted, it is just not a finding.
    ///
    /// Bound to the production predicate rather than re-deciding the rule in
    /// the test. A test that re-implemented `is_statically_false` would pass
    /// against a broken mapping, which is how the first attempt at this fix
    /// went wrong.
    #[test]
    fn statically_false_against_lean_error_is_a_declared_difference() {
        // The predicate itself, on real typechecker output.
        let checks = checks_by_action(SF_SCHEMA, SF_POLICY);
        let (_, check) = checks.first().expect("one request environment");
        assert!(
            is_statically_false(check),
            "test premise: this policy must be statically false on the Rust side"
        );

        // End to end against the real Lean backend, so Lean's rejection is
        // observed here rather than assumed.
        let report = run_src(SF_SCHEMA, SF_POLICY);
        assert_eq!(
            report.harness_problems().len(),
            0,
            "harness problems must be fixed before any finding is believable: {:?}",
            report.harness_problems()
        );
        assert_eq!(
            report
                .divergences
                .iter()
                .filter(|d| d.bucket() == "STATICALLY_FALSE_POLICY")
                .count(),
            1,
            "expected the declared bucket, got {:?}",
            report.divergences
        );
        assert!(
            report.findings().is_empty(),
            "a declared difference must not be a finding: {:?}",
            report.findings()
        );
        assert_eq!(
            report.declared_differences().len(),
            1,
            "it must still be recorded and reported, not dropped"
        );
    }

    /// The half that keeps the declaration from widening.
    ///
    /// Three things must survive it. A Rust SUCCESS against a Lean error is a
    /// real outcome disagreement and must stay one, which is the case the
    /// corpus cannot exercise because it contains none. The `OutcomeMismatch`
    /// reporting path must still surface as a finding in both directions. And
    /// a statically-false policy for which Lean DOES return an expression must
    /// still have its tree compared: dropping those was the refuted fix, and
    /// it cost 7,969 pairs of comparison coverage on the corpus.
    #[test]
    fn genuine_outcome_divergence_is_still_caught() {
        // A policy that typechecks is not statically false, so the declared
        // branch cannot capture it however Lean answers.
        let checks = checks_by_action(SF_COMPARED_SCHEMA, SF_COMPARED_POLICY);
        let (_, success) = checks
            .iter()
            .find(|(a, c)| a.contains("transfer") && !is_statically_false(c))
            .expect("the `transfer` environment must typecheck");
        assert!(
            rust_check_expr(success).is_some(),
            "a policy that typechecks must still offer its expression"
        );

        // The reporting path for a real outcome divergence is still live, in
        // both directions.
        for (rust_ok, lean_ok) in [(true, false), (false, true)] {
            let report = RunReport {
                compared: 1,
                divergences: vec![Divergence::OutcomeMismatch {
                    policy: "p".into(),
                    env: "a, Action::\"action\", a".into(),
                    rust_ok,
                    lean_ok,
                }],
            };
            let findings = report.findings();
            assert_eq!(
                findings.len(),
                1,
                "an outcome divergence (rust_ok={rust_ok}, lean_ok={lean_ok}) must be a finding"
            );
            assert_eq!(findings[0].bucket(), "OUTCOME_MISMATCH");
            assert!(!findings[0].is_declared_difference());
        }

        // Coverage: a statically-false pair whose Lean side DID produce an
        // expression is still compared as a tree, not declared away.
        let (_, irrelevant) = checks
            .iter()
            .find(|(a, _)| a.contains("close"))
            .expect("the `close` environment must be reachable");
        assert!(
            is_statically_false(irrelevant),
            "test premise: the `close` environment must be statically false"
        );
        assert!(
            rust_check_expr(irrelevant).is_some(),
            "a statically-false policy must keep offering its expression, or the \
             pairs Lean also types stop being compared"
        );
        let report = run_src(SF_COMPARED_SCHEMA, SF_COMPARED_POLICY);
        let close: Vec<_> = report
            .divergences
            .iter()
            .filter(|d| format!("{d:?}").contains("close"))
            .collect();
        assert!(
            !close.is_empty(),
            "the statically-false pair must still be compared, got {:?}",
            report.divergences
        );
        assert!(
            close
                .iter()
                .all(|d| d.bucket() != "STATICALLY_FALSE_POLICY"),
            "Lean produced an expression here, so this is not the declared case: {close:?}"
        );
    }

    /// A policy that typechecks cleanly under [`SF_SCHEMA`], so the Rust side
    /// returns `PolicyCheck::Success` for the single request environment.
    const OM_RUST_POLICY: &str =
        r#"permit(principal, action == Action::"action", resource) when { true };"#;

    /// The `OutcomeMismatch` arm, driven through `run_typed_expr_drt` itself.
    ///
    /// The corpus contains no pair where one side typechecks a policy the
    /// other rejects: over 26,745 compared pairs, `Success` against a Lean
    /// error and `Fail` against a Lean expression are both empty. So the arm
    /// that reports a real outcome disagreement is never exercised end to end
    /// by real input, and the rest of the suite only reaches it by building a
    /// `RunReport` directly, which tests the reporting path but not the
    /// driver's routing into it.
    ///
    /// This drives it for real. `run_typed_expr_drt` takes the Rust-side and
    /// Lean-side views as separate arguments and documents that keeping them
    /// in step is the caller's job, so the two sides are deliberately given
    /// different policies under the same id and schema: one the Rust
    /// typechecker accepts, one Lean rejects. The environment keys still
    /// align, so the pair is compared rather than reported as unmatched.
    ///
    /// What this shows is that the routing works and the arm is reachable.
    /// What it does NOT show is that the two typecheckers disagree on any
    /// real input, because the disagreement here is manufactured by feeding
    /// them different policies.
    #[test]
    fn outcome_divergence_is_reported_through_the_driver() {
        use std::str::FromStr;

        let vschema =
            cedar_policy_core::validator::ValidatorSchema::from_str(SF_SCHEMA).expect("vschema");
        let ffi_schema = cedar_policy::Schema::from_str(SF_SCHEMA).expect("ffi schema");
        // Rust sees a policy that typechecks.
        let core_policies =
            cedar_policy_core::parser::parse_policyset(OM_RUST_POLICY).expect("rust policies");
        // Lean sees one it rejects, under the same policy id.
        let ffi_policies = cedar_policy::PolicySet::from_str(SF_POLICY).expect("lean policies");

        let ffi = cedar_lean_ffi::CedarLeanFfi::new();
        let report = run_typed_expr_drt(&ffi, &vschema, &core_policies, &ffi_schema, &ffi_policies)
            .expect("Lean FFI call failed");

        // The two sides must still be aligned, or this would be testing the
        // unmatched-environment path instead of the outcome path.
        assert_eq!(
            report.harness_problems().len(),
            0,
            "the two views must stay aligned: {:?}",
            report.harness_problems()
        );
        assert_eq!(report.compared, 1, "expected one compared pair");

        let findings = report.findings();
        assert_eq!(
            findings.len(),
            1,
            "expected one finding, got {:?}",
            report.divergences
        );
        assert_eq!(findings[0].bucket(), "OUTCOME_MISMATCH");
        assert!(matches!(
            findings[0],
            Divergence::OutcomeMismatch {
                rust_ok: true,
                lean_ok: false,
                ..
            }
        ));
        assert!(
            !findings[0].is_declared_difference(),
            "a real outcome disagreement must not be declared away"
        );
    }
}
