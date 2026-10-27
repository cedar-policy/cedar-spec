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
use cedar_policy_core::ast::{AnyId, Expr, PolicySet, Template};
#[cfg(feature = "extended-like")]
use cedar_policy_core::ast::{DelimPattern, DelimPatternElem, ExprBuilder, ExprKind};
#[cfg(feature = "extended-like")]
use cedar_policy_core::expr_builder::ExprBuilder as _;
use cedar_policy_core::parser::err::{ParseError, ParseErrors, ToASTErrorKind};
use smol_str::SmolStr;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write;
use std::hash::{Hash, Hasher};
use std::mem;

// Check that two policies are equivalent, ignoring policy ids and source
// locations.  Panic if the two policies are not the same.
pub fn check_policy_equivalence(p_old: &Template, p_new: &Template) {
    // just dump to standard hashmaps to check equality without order.
    // also ignore source locations, which are not preserved in general
    let new_anno: HashMap<&AnyId, &SmolStr> =
        p_new.annotations().map(|(k, v)| (k, &v.val)).collect();
    let old_anno: HashMap<&AnyId, &SmolStr> =
        p_old.annotations().map(|(k, v)| (k, &v.val)).collect();
    similar_asserts::assert_eq!(new_anno, old_anno);
    similar_asserts::assert_eq!(p_new.effect(), p_old.effect());
    similar_asserts::assert_eq!(p_new.principal_constraint(), p_old.principal_constraint(),);
    similar_asserts::assert_eq!(p_new.action_constraint(), p_old.action_constraint(),);
    similar_asserts::assert_eq!(p_new.resource_constraint(), p_old.resource_constraint(),);
    match (p_new.non_scope_constraints(), p_old.non_scope_constraints()) {
        (Some(p_new), Some(p_old)) if !eq_shape_modulo_printing(p_new, p_old) => {
            panic!(
                "{}",
                similar_asserts::SimpleDiff::from_str(
                    &p_new.to_string(),
                    &p_old.to_string(),
                    "new",
                    "old"
                )
            )
        }
        (Some(p_new), None) => {
            panic!("New policy added non scope constraint {p_new}")
        }
        (None, Some(p_old)) => {
            panic!("New policy dropped non scope constraint {p_old}")
        }
        _ => (),
    }
}

/// `reparsed.eq_shape(original)`, except that with the `extended-like`
/// feature, `reparsed` may instead exactly match `original` after the
/// normalization that printing and re-parsing performs on delimited `like`
/// patterns (see [`normalize_delim_pattern`]). Roundtrips that don't go through
/// policy text (e.g. JSON) must match `original` itself.
fn eq_shape_modulo_printing(reparsed: &Expr, original: &Expr) -> bool {
    #[cfg(feature = "extended-like")]
    {
        reparsed.eq_shape(original) || reparsed.eq_shape(&normalize_delim_patterns(original))
    }
    #[cfg(not(feature = "extended-like"))]
    {
        reparsed.eq_shape(original)
    }
}

/// The result of printing `pattern` and parsing it back. Printing writes
/// adjacent `Wildcard`s as one `*`, and parsing pairs `*`s left to right, so
/// `[Wildcard, Wildcard]` comes back as `[Wildcard]` and
/// `[Wildcard, MultiWildcard]` (`***`) as `[MultiWildcard, Wildcard]`. The
/// pattern changes but matches the same strings.
#[cfg(feature = "extended-like")]
pub fn normalize_delim_pattern(pattern: &DelimPattern) -> DelimPattern {
    let mut out = Vec::with_capacity(pattern.len());
    // number of `*`s printed for the current run of wildcards
    let mut stars = 0;
    let mut prev_wildcard = false;
    let flush = |stars: &mut usize, out: &mut Vec<DelimPatternElem>| {
        out.extend(std::iter::repeat_n(
            DelimPatternElem::MultiWildcard,
            *stars / 2,
        ));
        if *stars % 2 == 1 {
            out.push(DelimPatternElem::Wildcard);
        }
        *stars = 0;
    };
    for elem in pattern.iter() {
        match elem {
            DelimPatternElem::Wildcard if prev_wildcard => {}
            DelimPatternElem::Wildcard => stars += 1,
            DelimPatternElem::MultiWildcard => stars += 2,
            DelimPatternElem::Char(_) => {
                flush(&mut stars, &mut out);
                out.push(*elem);
            }
        }
        prev_wildcard = matches!(elem, DelimPatternElem::Wildcard);
    }
    flush(&mut stars, &mut out);
    DelimPattern::from(out)
}

/// Apply [`normalize_delim_pattern`] to every delimited `like` in `e`
#[cfg(feature = "extended-like")]
pub fn normalize_delim_patterns(e: &Expr) -> Expr {
    use std::sync::Arc;
    let n = |e: &Arc<Expr>| Arc::new(normalize_delim_patterns(e));
    let kind = match e.expr_kind() {
        ExprKind::If {
            test_expr,
            then_expr,
            else_expr,
        } => ExprKind::If {
            test_expr: n(test_expr),
            then_expr: n(then_expr),
            else_expr: n(else_expr),
        },
        ExprKind::And { left, right } => ExprKind::And {
            left: n(left),
            right: n(right),
        },
        ExprKind::Or { left, right } => ExprKind::Or {
            left: n(left),
            right: n(right),
        },
        ExprKind::UnaryApp { op, arg } => ExprKind::UnaryApp {
            op: *op,
            arg: n(arg),
        },
        ExprKind::BinaryApp { op, arg1, arg2 } => ExprKind::BinaryApp {
            op: *op,
            arg1: n(arg1),
            arg2: n(arg2),
        },
        ExprKind::ExtensionFunctionApp { fn_name, args } => ExprKind::ExtensionFunctionApp {
            fn_name: fn_name.clone(),
            args: Arc::new(args.iter().map(normalize_delim_patterns).collect()),
        },
        ExprKind::GetAttr { expr, attr } => ExprKind::GetAttr {
            expr: n(expr),
            attr: attr.clone(),
        },
        ExprKind::HasAttr { expr, attr } => ExprKind::HasAttr {
            expr: n(expr),
            attr: attr.clone(),
        },
        ExprKind::ExtHasAttr { expr, attrs } => ExprKind::ExtHasAttr {
            expr: n(expr),
            attrs: attrs.clone(),
        },
        ExprKind::Like { expr, pattern } => ExprKind::Like {
            expr: n(expr),
            pattern: pattern.clone(),
        },
        ExprKind::LikeDelimited {
            expr,
            pattern,
            delim,
        } => ExprKind::LikeDelimited {
            expr: n(expr),
            pattern: normalize_delim_pattern(pattern),
            delim: *delim,
        },
        ExprKind::Is { expr, entity_type } => ExprKind::Is {
            expr: n(expr),
            entity_type: entity_type.clone(),
        },
        ExprKind::Set(elems) => ExprKind::Set(Arc::new(
            elems.iter().map(normalize_delim_patterns).collect(),
        )),
        ExprKind::Record(fields) => ExprKind::Record(Arc::new(
            fields
                .iter()
                .map(|(k, v)| (k.clone(), normalize_delim_patterns(v)))
                .collect(),
        )),
        // leaves: Lit, Var, Slot, Unknown (and Error, with `tolerant-ast`)
        kind => kind.clone(),
    };
    // source locations are irrelevant for `eq_shape`
    ExprBuilder::new().with_expr_kind(kind)
}

// Check that we don't see a few specific errors, which correspond to violations
// of internal invariants.
pub fn check_for_internal_errors(errs: ParseErrors) {
    assert!(
        !errs.iter().any(|e| matches!(
        e,
        ParseError::ToAST(e) if matches!(e.kind(),
            ToASTErrorKind::MembershipInvariantViolation
                | ToASTErrorKind::EmptyNodeInvariantViolation)
        )),
        "Parse errors included unexpected internal errors: {:?}",
        miette::Report::new(errs).wrap_err("unexpected internal error")
    )
}

// Exposes only the aspects of a template that are preserved through conversions
// to different representations.
// In particular, policy ids and source locations are not exposed.
#[derive(Eq, Debug)]
struct PreservedTemplate<'a> {
    template: &'a Template,
    annotations: BTreeMap<&'a AnyId, &'a SmolStr>,
}

impl PartialEq for PreservedTemplate<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.template.effect() == other.template.effect()
            && self.template.principal_constraint() == other.template.principal_constraint()
            && self.template.action_constraint() == other.template.action_constraint()
            && self.template.resource_constraint() == other.template.resource_constraint()
            && self.annotations == other.annotations
            && match (
                self.template.non_scope_constraints(),
                other.template.non_scope_constraints(),
            ) {
                (Some(s), Some(o)) => eq_shape_modulo_printing(s, o),
                (Some(_), None) | (None, Some(_)) => false,
                (None, None) => true,
            }
    }
}

impl Hash for PreservedTemplate<'_> {
    fn hash<H: Hasher>(&self, hasher: &mut H) {
        self.template.effect().hash(hasher);
        self.template.principal_constraint().hash(hasher);
        self.template.action_constraint().hash(hasher);
        self.template.resource_constraint().hash(hasher);
        mem::discriminant(&self.template.non_scope_constraints()).hash(hasher);
        if let Some(expr) = self.template.non_scope_constraints() {
            expr.hash_shape(hasher);
        }
        self.annotations.hash(hasher);
    }
}

impl<'a> From<&'a Template> for PreservedTemplate<'a> {
    fn from(value: &'a Template) -> Self {
        PreservedTemplate {
            template: value,
            annotations: value.annotations().map(|(k, v)| (k, &v.val)).collect(),
        }
    }
}

// Checks that the static policies and templates in the specified
// sets are equivalent, ignoring policy ids and source locations.
// Ignores links in the policy sets when determining equivalence.
// Panics if the two sets are not equivalent.
pub fn check_policy_set_equivalence(set1: &PolicySet, set2: &PolicySet) {
    // Convert templates in each set to preserved templates
    let t1 = set1
        .all_templates()
        .map(PreservedTemplate::from)
        .collect::<HashSet<PreservedTemplate>>();
    let t2 = set2
        .all_templates()
        .map(PreservedTemplate::from)
        .collect::<HashSet<PreservedTemplate>>();
    // Check that the sets of preserved templates are equal
    assert_eq!(
        t1,
        t2,
        "{}",
        similar_asserts::SimpleDiff::from_str(&set1.to_string(), &set2.to_string(), "LHS", "RHS",)
    );
}

/// Converts an ast policy set to Cedar text, removing linked policies.
pub fn policy_set_to_text(policy_set: &cedar_policy_core::ast::PolicySet) -> String {
    let mut res = String::new();
    let mut iter = policy_set.all_templates();
    if let Some(template) = iter.next() {
        write!(res, "{template}").unwrap();
        for template in iter {
            writeln!(&mut res).unwrap();
            write!(res, "{template}").unwrap();
        }
    }
    res
}
