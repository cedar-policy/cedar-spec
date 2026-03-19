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

//! Generators for PST (Public Syntax Tree) types.
//!
//! These generators produce `pst::Template` and related types for fuzz testing
//! PST roundtrip properties.

use crate::err::Result;
use crate::hierarchy::Hierarchy;
use crate::size_hint_utils::size_hint_for_ratio;
use arbitrary::Unstructured;
use cedar_policy_core::ast;
use cedar_policy_core::pst;
use smol_str::SmolStr;
use std::collections::BTreeMap;
use std::sync::Arc;

/// Generate an arbitrary `pst::Name` from the hierarchy's entity types.
pub fn arbitrary_pst_name(hierarchy: &Hierarchy, u: &mut Unstructured<'_>) -> Result<pst::Name> {
    let ast_uid = hierarchy.arbitrary_uid(u)?;
    let ast_et: ast::EntityType = ast_uid.entity_type().clone();
    Ok(pst::Name::from(ast::Name::from(ast_et)))
}

/// Generate an arbitrary `pst::EntityType` from the hierarchy.
pub fn arbitrary_pst_entity_type(
    hierarchy: &Hierarchy,
    u: &mut Unstructured<'_>,
) -> Result<pst::EntityType> {
    Ok(pst::EntityType::from_name(arbitrary_pst_name(
        hierarchy, u,
    )?))
}

/// Generate an arbitrary `pst::EntityUID` from the hierarchy.
pub fn arbitrary_pst_entity_uid(
    hierarchy: &Hierarchy,
    u: &mut Unstructured<'_>,
) -> Result<pst::EntityUID> {
    let ast_uid = hierarchy.arbitrary_uid(u)?;
    Ok(pst::EntityUID::from(ast_uid))
}

/// Generate an arbitrary `pst::Effect`.
pub fn arbitrary_pst_effect(u: &mut Unstructured<'_>) -> Result<pst::Effect> {
    uniform!(u, Ok(pst::Effect::Permit), Ok(pst::Effect::Forbid))
}

/// Generate an arbitrary `pst::Literal`.
pub fn arbitrary_pst_literal(
    hierarchy: &Hierarchy,
    u: &mut Unstructured<'_>,
) -> Result<pst::Literal> {
    gen!(u,
        2 => Ok(pst::Literal::Bool(u.arbitrary()?)),
        2 => Ok(pst::Literal::Long(u.arbitrary()?)),
        2 => Ok(pst::Literal::String(u.arbitrary::<SmolStr>()?)),
        1 => Ok(pst::Literal::EntityUID(arbitrary_pst_entity_uid(hierarchy, u)?))
    )
}

/// Generate an arbitrary `pst::Var`.
pub fn arbitrary_pst_var(u: &mut Unstructured<'_>) -> Result<pst::Var> {
    uniform!(
        u,
        Ok(pst::Var::Principal),
        Ok(pst::Var::Action),
        Ok(pst::Var::Resource),
        Ok(pst::Var::Context)
    )
}

/// Generate an arbitrary `pst::UnaryOp`.
pub fn arbitrary_pst_unary_op(u: &mut Unstructured<'_>) -> Result<pst::UnaryOp> {
    uniform!(
        u,
        Ok(pst::UnaryOp::Not),
        Ok(pst::UnaryOp::Neg),
        Ok(pst::UnaryOp::IsEmpty)
    )
}

/// Generate an arbitrary `pst::BinaryOp`.
pub fn arbitrary_pst_binary_op(u: &mut Unstructured<'_>) -> Result<pst::BinaryOp> {
    uniform!(
        u,
        Ok(pst::BinaryOp::Eq),
        Ok(pst::BinaryOp::NotEq),
        Ok(pst::BinaryOp::Less),
        Ok(pst::BinaryOp::LessEq),
        Ok(pst::BinaryOp::Greater),
        Ok(pst::BinaryOp::GreaterEq),
        Ok(pst::BinaryOp::And),
        Ok(pst::BinaryOp::Or),
        Ok(pst::BinaryOp::Add),
        Ok(pst::BinaryOp::Sub),
        Ok(pst::BinaryOp::Mul),
        Ok(pst::BinaryOp::In),
        Ok(pst::BinaryOp::Contains),
        Ok(pst::BinaryOp::ContainsAll),
        Ok(pst::BinaryOp::ContainsAny),
        Ok(pst::BinaryOp::GetTag),
        Ok(pst::BinaryOp::HasTag)
    )
}

/// Generate an arbitrary `pst::PatternElem`.
pub fn arbitrary_pst_pattern_elem(u: &mut Unstructured<'_>) -> Result<pst::PatternElem> {
    gen!(u,
        3 => Ok(pst::PatternElem::Char(u.arbitrary()?)),
        1 => Ok(pst::PatternElem::Wildcard)
    )
}

/// Generate an arbitrary `pst::Expr` with bounded depth.
pub fn arbitrary_pst_expr(
    hierarchy: &Hierarchy,
    max_depth: usize,
    max_width: usize,
    u: &mut Unstructured<'_>,
) -> Result<pst::Expr> {
    if max_depth == 0 {
        // Base case: only leaf expressions
        gen!(u,
            3 => Ok(pst::Expr::Literal(arbitrary_pst_literal(hierarchy, u)?)),
            2 => Ok(pst::Expr::Var(arbitrary_pst_var(u)?))
        )
    } else {
        gen!(u,
            2 => Ok(pst::Expr::Literal(arbitrary_pst_literal(hierarchy, u)?)),
            2 => Ok(pst::Expr::Var(arbitrary_pst_var(u)?)),
            1 => {
                let op = arbitrary_pst_unary_op(u)?;
                let expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                Ok(pst::Expr::UnaryOp { op, expr })
            },
            2 => {
                let op = arbitrary_pst_binary_op(u)?;
                let left = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                let right = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                Ok(pst::Expr::BinaryOp { op, left, right })
            },
            1 => {
                let expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                let attr: SmolStr = u.arbitrary()?;
                Ok(pst::Expr::GetAttr { expr, attr })
            },
            1 => {
                let expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                let attr: SmolStr = u.arbitrary()?;
                Ok(pst::Expr::HasAttr { expr, attrs: nonempty::nonempty![attr] })
            },
            1 => {
                let expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                let mut pattern = vec![];
                u.arbitrary_loop(Some(0), Some(max_width as u32), |u| {
                    pattern.push(arbitrary_pst_pattern_elem(u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(pst::Expr::Like { expr, pattern })
            },
            1 => {
                let expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                let entity_type = arbitrary_pst_entity_type(hierarchy, u)?;
                let in_expr = if u.ratio(1, 3)? {
                    Some(Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?))
                } else {
                    None
                };
                Ok(pst::Expr::Is { expr, entity_type, in_expr })
            },
            1 => {
                let cond = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                let then_expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                let else_expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                Ok(pst::Expr::IfThenElse { cond, then_expr, else_expr })
            },
            1 => {
                let mut elems = vec![];
                u.arbitrary_loop(Some(0), Some(max_width as u32), |u| {
                    elems.push(Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?));
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(pst::Expr::Set(elems))
            },
            1 => {
                let mut map = BTreeMap::new();
                u.arbitrary_loop(Some(0), Some(max_width as u32), |u| {
                    let key: String = u.arbitrary()?;
                    let val = Arc::new(arbitrary_pst_expr(hierarchy, max_depth - 1, max_width, u)?);
                    map.insert(key, val);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(pst::Expr::Record(map))
            }
        )
    }
}

/// Generate an arbitrary `pst::Clause` (without slots in the expression).
pub fn arbitrary_pst_clause(
    hierarchy: &Hierarchy,
    max_depth: usize,
    max_width: usize,
    u: &mut Unstructured<'_>,
) -> Result<pst::Clause> {
    let expr = Arc::new(arbitrary_pst_expr(hierarchy, max_depth, max_width, u)?);
    uniform!(
        u,
        Ok(pst::Clause::When(expr.clone())),
        Ok(pst::Clause::Unless(expr))
    )
}

/// Generate an arbitrary `pst::EntityOrSlot`.
/// If `slot` is `Some`, the result may be a slot; if `None`, entity only.
fn arbitrary_pst_entity_or_slot(
    hierarchy: &Hierarchy,
    slot: Option<pst::SlotId>,
    u: &mut Unstructured<'_>,
) -> Result<pst::EntityOrSlot> {
    match slot {
        Some(s) if u.ratio(1, 2)? => Ok(pst::EntityOrSlot::Slot(s)),
        _ => Ok(pst::EntityOrSlot::Entity(arbitrary_pst_entity_uid(
            hierarchy, u,
        )?)),
    }
}

/// Generate an arbitrary `pst::PrincipalConstraint`.
/// If `use_slot` is true, constraints may contain `?principal` slots.
pub fn arbitrary_pst_principal_constraint(
    hierarchy: &Hierarchy,
    use_slot: bool,
    u: &mut Unstructured<'_>,
) -> Result<pst::PrincipalConstraint> {
    let slot = if use_slot {
        Some(pst::SlotId::Principal)
    } else {
        None
    };
    if u.ratio(1, 5)? {
        Ok(pst::PrincipalConstraint::Any)
    } else {
        gen!(u,
            2 => Ok(pst::PrincipalConstraint::Eq(arbitrary_pst_entity_or_slot(hierarchy, slot, u)?)),
            1 => Ok(pst::PrincipalConstraint::In(arbitrary_pst_entity_or_slot(hierarchy, slot, u)?)),
            1 => Ok(pst::PrincipalConstraint::Is(arbitrary_pst_entity_type(hierarchy, u)?)),
            1 => Ok(pst::PrincipalConstraint::IsIn(
                arbitrary_pst_entity_type(hierarchy, u)?,
                arbitrary_pst_entity_or_slot(hierarchy, slot, u)?,
            ))
        )
    }
}

/// Generate an arbitrary `pst::ResourceConstraint`.
/// If `use_slot` is true, constraints may contain `?resource` slots.
pub fn arbitrary_pst_resource_constraint(
    hierarchy: &Hierarchy,
    use_slot: bool,
    u: &mut Unstructured<'_>,
) -> Result<pst::ResourceConstraint> {
    let slot = if use_slot {
        Some(pst::SlotId::Resource)
    } else {
        None
    };
    if u.ratio(1, 5)? {
        Ok(pst::ResourceConstraint::Any)
    } else {
        gen!(u,
            2 => Ok(pst::ResourceConstraint::Eq(arbitrary_pst_entity_or_slot(hierarchy, slot, u)?)),
            1 => Ok(pst::ResourceConstraint::In(arbitrary_pst_entity_or_slot(hierarchy, slot, u)?)),
            1 => Ok(pst::ResourceConstraint::Is(arbitrary_pst_entity_type(hierarchy, u)?)),
            1 => Ok(pst::ResourceConstraint::IsIn(
                arbitrary_pst_entity_type(hierarchy, u)?,
                arbitrary_pst_entity_or_slot(hierarchy, slot, u)?,
            ))
        )
    }
}

/// Generate an arbitrary `pst::ActionConstraint`.
pub fn arbitrary_pst_action_constraint(
    hierarchy: &Hierarchy,
    u: &mut Unstructured<'_>,
) -> Result<pst::ActionConstraint> {
    if u.ratio(1, 10)? {
        Ok(pst::ActionConstraint::Any)
    } else if u.ratio(1, 3)? {
        Ok(pst::ActionConstraint::Eq(arbitrary_pst_entity_uid(
            hierarchy, u,
        )?))
    } else {
        let mut uids = vec![];
        u.arbitrary_loop(Some(0), Some(3), |u| {
            uids.push(arbitrary_pst_entity_uid(hierarchy, u)?);
            Ok(std::ops::ControlFlow::Continue(()))
        })?;
        Ok(pst::ActionConstraint::In(uids))
    }
}

/// Generate an arbitrary `pst::Template` (static, no slots).
pub fn arbitrary_pst_template(
    hierarchy: &Hierarchy,
    max_depth: usize,
    max_width: usize,
    u: &mut Unstructured<'_>,
) -> Result<pst::Template> {
    arbitrary_pst_template_with_slots(hierarchy, max_depth, max_width, 0, u)
}

/// Generate an arbitrary `pst::Template` with `num_slots` slots (0, 1, or 2).
/// - 0: no slots (static policy)
/// - 1: either `?principal` or `?resource` slot
/// - 2: both `?principal` and `?resource` slots
pub fn arbitrary_pst_slotted_template(
    hierarchy: &Hierarchy,
    max_depth: usize,
    max_width: usize,
    num_slots: usize,
    u: &mut Unstructured<'_>,
) -> Result<pst::Template> {
    assert!(num_slots <= 2, "num_slots must be 0, 1, or 2");
    arbitrary_pst_template_with_slots(hierarchy, max_depth, max_width, num_slots, u)
}

fn arbitrary_pst_template_with_slots(
    hierarchy: &Hierarchy,
    max_depth: usize,
    max_width: usize,
    num_slots: usize,
    u: &mut Unstructured<'_>,
) -> Result<pst::Template> {
    let (principal_slot, resource_slot) = match num_slots {
        0 => (false, false),
        1 => {
            if u.ratio(1, 2)? {
                (true, false)
            } else {
                (false, true)
            }
        }
        _ => (true, true),
    };

    let id = pst::PolicyID(u.arbitrary::<SmolStr>()?);
    let effect = arbitrary_pst_effect(u)?;
    let principal = arbitrary_pst_principal_constraint(hierarchy, principal_slot, u)?;
    let action = arbitrary_pst_action_constraint(hierarchy, u)?;
    let resource = arbitrary_pst_resource_constraint(hierarchy, resource_slot, u)?;

    let mut template = pst::Template::new(id, effect, principal, action, resource);

    // Generate 0-3 clauses
    let mut clauses = vec![];
    u.arbitrary_loop(Some(0), Some(3), |u| {
        clauses.push(arbitrary_pst_clause(hierarchy, max_depth, max_width, u)?);
        Ok(std::ops::ControlFlow::Continue(()))
    })?;
    template = template
        .try_with_clauses(clauses)
        .map_err(|_| crate::err::Error::TooDeep)?;

    // Generate 0-2 annotations with valid Cedar identifiers
    let mut annotations = BTreeMap::new();
    u.arbitrary_loop(Some(0), Some(2), |u| {
        // Use simple valid identifiers for annotation keys
        let key = format!("ann{}", annotations.len());
        let val: SmolStr = u.arbitrary()?;
        annotations.insert(key, val);
        Ok(std::ops::ControlFlow::Continue(()))
    })?;
    template = template.with_annotations(annotations);

    Ok(template)
}

/// Size hint for PST template generation.
pub fn arbitrary_pst_template_size_hint(depth: usize) -> (usize, Option<usize>) {
    arbitrary::size_hint::and_all(&[
        <SmolStr as arbitrary::Arbitrary>::size_hint(depth), // id
        (1, Some(1)),                                        // effect
        arbitrary::size_hint::and(
            size_hint_for_ratio(1, 5),
            Hierarchy::arbitrary_uid_size_hint(depth),
        ), // principal
        arbitrary::size_hint::and(
            size_hint_for_ratio(1, 10),
            Hierarchy::arbitrary_uid_size_hint(depth),
        ), // action
        arbitrary::size_hint::and(
            size_hint_for_ratio(1, 5),
            Hierarchy::arbitrary_uid_size_hint(depth),
        ), // resource
        (1, None),                                           // clauses
    ])
}
