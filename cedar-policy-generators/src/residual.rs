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

//! Generation of arbitrary TPE residuals, by translating an arbitrary expression.
//!
//! Every node is annotated `Bool`, so the residuals are ill-typed in general. That is fine for
//! concrete evaluation, which is what these are generated for: the model's `Residual.evaluate`
//! ignores annotations, and Rust reaches the same answer through `Expr`, which has none. A target
//! that partially evaluates these would need real annotations, since partial evaluation reads
//! them, and would want a generator that produces them rather than this translation.

use crate::expr::ExprGenerator;
use arbitrary::{Result, Unstructured};
use cedar_policy_core::ast::{Expr, ExprKind, Value};
use cedar_policy_core::tpe::residual::{Residual, ResidualKind};
use cedar_policy_core::validator::types::Type;
use std::collections::BTreeMap;
use std::sync::Arc;

impl<'a> ExprGenerator<'a> {
    /// Generate an arbitrary residual, annotating every node `Bool`.
    ///
    /// Incorrect type annotations can cause trouble for TPE, but this is
    /// currently only used to test residual evaluation, which never looks at
    /// the types in either Rust of Lean.
    pub fn generate_residual(
        &self,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<Residual> {
        let e = self.generate_expr(max_depth, u)?;
        residual_of_expr(e, u)
    }
}

fn residual_of_expr(e: Expr, u: &mut Unstructured<'_>) -> Result<Residual> {
    if u.ratio(1, 12)? {
        // `Residual::Error` is not in `Expr`, so we would never test it just translating from expressions.
        // We inject it randomly instead.
        return Ok(Residual::Error(Type::primitive_boolean()));
    }
    let kind = match e.into_expr_kind() {
        // A literal is already a value, so it becomes `Concrete` rather than a `ResidualKind`.
        ExprKind::Lit(l) => {
            return Ok(Residual::Concrete {
                value: Value::from(l.clone()),
                ty: Type::primitive_boolean(),
            });
        }
        ExprKind::Var(v) => ResidualKind::Var(v),
        ExprKind::If {
            test_expr,
            then_expr,
            else_expr,
        } => ResidualKind::If {
            test_expr: Arc::new(residual_of_expr(Arc::unwrap_or_clone(test_expr), u)?),
            then_expr: Arc::new(residual_of_expr(Arc::unwrap_or_clone(then_expr), u)?),
            else_expr: Arc::new(residual_of_expr(Arc::unwrap_or_clone(else_expr), u)?),
        },
        ExprKind::And { left, right } => ResidualKind::And {
            left: Arc::new(residual_of_expr(Arc::unwrap_or_clone(left), u)?),
            right: Arc::new(residual_of_expr(Arc::unwrap_or_clone(right), u)?),
        },
        ExprKind::Or { left, right } => ResidualKind::Or {
            left: Arc::new(residual_of_expr(Arc::unwrap_or_clone(left), u)?),
            right: Arc::new(residual_of_expr(Arc::unwrap_or_clone(right), u)?),
        },
        ExprKind::UnaryApp { op, arg } => ResidualKind::UnaryApp {
            op,
            arg: Arc::new(residual_of_expr(Arc::unwrap_or_clone(arg), u)?),
        },
        ExprKind::BinaryApp { op, arg1, arg2 } => ResidualKind::BinaryApp {
            op,
            arg1: Arc::new(residual_of_expr(Arc::unwrap_or_clone(arg1), u)?),
            arg2: Arc::new(residual_of_expr(Arc::unwrap_or_clone(arg2), u)?),
        },
        ExprKind::GetAttr { expr, attr } => ResidualKind::GetAttr {
            expr: Arc::new(residual_of_expr(Arc::unwrap_or_clone(expr), u)?),
            attr: attr.clone(),
        },
        ExprKind::HasAttr { expr, attr } => ResidualKind::HasAttr {
            expr: Arc::new(residual_of_expr(Arc::unwrap_or_clone(expr), u)?),
            attr: attr.clone(),
        },
        ExprKind::Like { expr, pattern } => ResidualKind::Like {
            expr: Arc::new(residual_of_expr(Arc::unwrap_or_clone(expr), u)?),
            pattern: pattern.clone(),
        },
        ExprKind::Is { expr, entity_type } => ResidualKind::Is {
            expr: Arc::new(residual_of_expr(Arc::unwrap_or_clone(expr), u)?),
            entity_type: entity_type.clone(),
        },
        ExprKind::Set(items) => ResidualKind::Set(Arc::new(
            Arc::unwrap_or_clone(items)
                .into_iter()
                .map(|i| residual_of_expr(i, u))
                .collect::<Result<Vec<_>>>()?,
        )),
        ExprKind::Record(fields) => ResidualKind::Record(Arc::new(
            Arc::unwrap_or_clone(fields)
                .into_iter()
                .map(|(k, v)| Ok((k.clone(), residual_of_expr(v, u)?)))
                .collect::<Result<BTreeMap<_, _>>>()?,
        )),
        ExprKind::ExtensionFunctionApp { fn_name, args } => ResidualKind::ExtensionFunctionApp {
            fn_name: fn_name.clone(),
            args: Arc::new(
                Arc::unwrap_or_clone(args)
                    .into_iter()
                    .map(|a| residual_of_expr(a, u))
                    .collect::<Result<Vec<_>>>()?,
            ),
        },
        // We can't translate these, but on the principal that it's better not to error when generating
        // inputs, we'll use `true` as a place holder.
        ExprKind::Unknown(_) | ExprKind::Slot(_) => {
            return Ok(Residual::Concrete {
                value: Value::from(true),
                ty: Type::primitive_boolean(),
            })
        }
    };
    Ok(Residual::Partial {
        kind,
        ty: Type::primitive_boolean(),
    })
}
