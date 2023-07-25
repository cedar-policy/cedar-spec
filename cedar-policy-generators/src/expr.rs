use crate::abac::{AvailableExtensionFunctions, ConstantPool};
use crate::err::{while_doing, Error, Result};
use crate::hierarchy::{generate_uid_with_type, Hierarchy};
use crate::schema::{arbitrary_specified_uid_without_schema, uid_for_action_name, Schema};
use crate::settings::ABACSettings;
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_range};
use crate::{accum, gen, gen_inner, uniform};
use arbitrary::{Arbitrary, Unstructured};
use cedar_policy_core::ast;
use smol_str::SmolStr;

/// Struct for generating expressions
#[derive(Debug)]
pub struct ExprGenerator<'a> {
    /// Schema for generated expressions to conform to
    pub schema: &'a Schema,
    /// General settings for ABAC generation, many of which affect expression generation
    pub settings: &'a ABACSettings,
    /// Constant pool to use when needed
    pub constant_pool: &'a ConstantPool,
    /// data on available extension functions
    pub ext_funcs: &'a AvailableExtensionFunctions,
    /// If this is present, any literal UIDs included in generated `Expr`s will
    /// (usually) exist in the hierarchy.
    pub hierarchy: Option<&'a Hierarchy>,
}

impl<'a> ExprGenerator<'a> {
    /// get a (fully general) arbitrary expression conforming to the schema, but
    /// no attempt to match types.
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate(&mut self, max_depth: usize, u: &mut Unstructured<'_>) -> Result<ast::Expr> {
        if max_depth == 0 {
            // no recursion allowed: just generate a literal
            self.generate_literal_or_var(u)
        } else {
            gen!(u,
            2 => {
                // a literal or variable
                self.generate_literal_or_var(u)
            },
            1 => {
                // == expression
                Ok(ast::Expr::is_eq(
                    self.generate(max_depth - 1, u)?,
                    self.generate(max_depth - 1, u)?,
                ))
            },
            1 => {
                // not expression
                Ok(ast::Expr::not(self.generate(max_depth - 1, u)?))
            },
            1 => {
                // any other expression
                gen!(u,
                    2 => Ok(ast::Expr::ite(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    2 => Ok(ast::Expr::and(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    2 => Ok(ast::Expr::or(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::less(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::lesseq(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::greater(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::greatereq(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::add(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::sub(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => {
                        // arbitrary expression, which may be a constant
                        let expr = self.generate(max_depth - 1, u)?;
                        // arbitrary constant integer
                        let c = self.constant_pool.arbitrary_int_constant(u)?;
                        Ok(ast::Expr::mul(expr, c))
                    },
                    1 => {
                        // negation expression
                        Ok(ast::Expr::neg(self.generate(max_depth - 1, u)?))
                    },
                    6 => Ok(ast::Expr::is_in(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains_all(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains_any(
                        self.generate(max_depth - 1, u)?,
                        self.generate(max_depth - 1, u)?,
                    )),
                    2 => {
                        if self.settings.enable_like {
                            Ok(ast::Expr::like(
                                self.generate(max_depth - 1, u)?,
                                self.constant_pool.arbitrary_pattern_literal(u)?,
                            ))
                        } else {
                            Err(Error::LikeDisabled)
                        }
                    },
                    1 => {
                        let mut l = Vec::new();
                        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                            l.push(self.generate(max_depth - 1, u)?);
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                        Ok(ast::Expr::set(l))
                    },
                    1 => {
                        let mut r = Vec::new();
                        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                            let (attr_name, _) = self.schema.arbitrary_attr(u)?;
                            r.push((
                                attr_name.clone(),
                                self.generate(max_depth - 1, u)?,
                            ));
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                        Ok(ast::Expr::record(r))
                    },
                    1 => {
                        if !self.settings.enable_extensions {
                            return Err(Error::ExtensionsDisabled);
                        };
                        let func = self.ext_funcs.arbitrary_all(u)?;
                        let arity = if !self.settings.enable_arbitrary_func_call
                            || u.ratio::<u8>(9, 10)?
                        {
                            // 90% of the time respect the correct arity, but sometimes don't
                            func.parameter_types.len()
                        } else {
                            u.int_in_range::<usize>(0..=4)?
                        };
                        let fn_name = if !self.settings.enable_arbitrary_func_call
                            || u.ratio::<u8>(9, 10)?
                        {
                            // 90% of the time choose an existing extension function, but sometimes don't
                            func.name.clone()
                        } else {
                            u.arbitrary()?
                        };
                        Ok(ast::Expr::call_extension_fn(
                            fn_name,
                            (0..arity)
                                .map(|_| self.generate(max_depth - 1, u))
                                .collect::<Result<_>>()?,
                        ))
                    },
                    7 => {
                        let attr_name = gen!(u,
                            1 => {
                                let s: String = u.arbitrary()?;
                                SmolStr::from(s)
                            },
                            6 => self.schema.arbitrary_attr(u)?.0.clone());
                        let e = self.generate(max_depth - 1, u)?;
                        // We should be able to have an arbitrary expression
                        // as the base of an `GetAttr` operation.
                        // However, in one case this will fail to parse
                        // after being pretty-printed: the case where the
                        // base is a string literal (e.g.,
                        // "c"["attr_name"]).
                        // So when we get a string lit, compose a record out
                        // of it to recover gracefully.
                        let e = if let ast::ExprKind::Lit(ast::Literal::String(ref s)) =
                            e.expr_kind()
                        {
                            ast::Expr::record([((s).clone(), e)])
                        } else {
                            e
                        };
                        Ok(ast::Expr::get_attr(e, attr_name))
                    },
                    4 => {
                        let attr_name = uniform!(u,
                           self.schema.arbitrary_attr(u)?.0.clone(),
                            {
                                let s: String = u.arbitrary()?;
                                SmolStr::from(s)
                            });
                        Ok(ast::Expr::has_attr(
                            self.generate(max_depth - 1, u)?,
                            attr_name,
                        ))
                    })
            })
        }
    }

    /// get a (fully general) arbitrary constant, as an expression.
    #[allow(dead_code)]
    pub fn generate_const_expr(&self, u: &mut Unstructured<'_>) -> Result<ast::Expr> {
        gen!(u,
        4 => self.generate_literal(u),
        1 => {
            let mut l = Vec::new();
            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                l.push(self.generate_const_expr(u)?);
                Ok(std::ops::ControlFlow::Continue(()))
            })?;
            Ok(ast::Expr::set(l))
        },
        1 => {
            let mut r = Vec::new();
            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                let (attr_name, _) = self.schema.arbitrary_attr(u)?;
                r.push((attr_name.clone(), self.generate_const_expr(u)?));
                Ok(std::ops::ControlFlow::Continue(()))
            })?;
            Ok(ast::Expr::record(r))
        })
    }

    /// get a literal value or variable of an arbitrary type.
    /// This function is guaranteed to not recurse, directly or indirectly.
    fn generate_literal_or_var(&self, u: &mut Unstructured<'_>) -> Result<ast::Expr> {
        if u.ratio(1, 4)? {
            Ok(ast::Expr::var(u.arbitrary()?))
        } else {
            self.generate_literal(u)
        }
    }

    /// get a literal value of an arbitrary type.
    /// This function is guaranteed to not recurse, directly or indirectly.
    fn generate_literal(&self, u: &mut Unstructured<'_>) -> Result<ast::Expr> {
        gen!(u,
        11 => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
        10 => Ok(ast::Expr::val(
            self.constant_pool.arbitrary_int_constant(u)?,
        )),
        10 => Ok(ast::Expr::val(
            self.constant_pool.arbitrary_string_constant(u)?,
        )),
        20 => Ok(ast::Expr::val(self.generate_uid(u)?)),
        4 => Ok(ast::Expr::val(
            arbitrary_specified_uid_without_schema(u)?,
        )))
    }

    /// get a UID of a type declared in the schema -- may be a principal,
    /// action, or resource UID. For actions, it will be an action declared in
    /// the schema.
    pub fn generate_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        uniform!(
            u,
            self.arbitrary_principal_uid(u),
            self.arbitrary_action_uid(u),
            self.arbitrary_resource_uid(u)
        )
    }
    /// size hint for generate_uid()
    #[allow(dead_code)]
    pub fn generate_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_range(0, 2),
            arbitrary::size_hint::or_all(&[
                Self::arbitrary_principal_uid_size_hint(depth),
                Self::arbitrary_action_uid_size_hint(depth),
                Self::arbitrary_resource_uid_size_hint(depth),
            ]),
        )
    }

    /// get a UID of a type that could be used as a `principal` for some action in the schema.
    pub fn arbitrary_principal_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        self.arbitrary_uid_with_type(
            u.choose(&self.schema.principal_types)
                .map_err(|e| while_doing("choosing a principal type", e))?,
            u,
        )
    }
    /// size hint for arbitrary_principal_uid()
    pub fn arbitrary_principal_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_choose(None),
            Self::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    /// get an arbitrary action UID from the schema.
    ///
    /// This doesn't reference the `Hierarchy`, because we assume that all
    /// actions are defined in the schema, and we just give you one of the
    /// actions from the schema.
    pub fn arbitrary_action_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        let action = u
            .choose(&self.schema.actions_eids)
            .map_err(|e| while_doing("choosing an action", e))?;
        Ok(uid_for_action_name(
            self.schema.namespace.clone(),
            action.clone(),
        ))
    }
    /// size hint for arbitrary_action_uid()
    pub fn arbitrary_action_uid_size_hint(_depth: usize) -> (usize, Option<usize>) {
        size_hint_for_choose(None)
    }

    /// get a UID of a type that could be used as a `resource` for some action in the schema.
    pub fn arbitrary_resource_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        self.arbitrary_uid_with_type(
            u.choose(&self.schema.resource_types)
                .map_err(|e| while_doing("choosing a resource type", e))?,
            u,
        )
    }
    /// size hint for arbitrary_resource_uid()
    pub fn arbitrary_resource_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_choose(None),
            Self::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    /// generate a UID with the given typename
    pub fn arbitrary_uid_with_type(
        &self,
        ty: &ast::Name,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        match self.hierarchy {
            None => generate_uid_with_type(ty.clone(), EntityUIDGenMode::default(), u),
            Some(hierarchy) => hierarchy.arbitrary_uid_with_type(ty, u),
        }
    }
    /// size hint for arbitrary_uid_with_type()
    pub fn arbitrary_uid_with_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::or(
            <ast::Eid as Arbitrary>::size_hint(depth),
            Hierarchy::arbitrary_uid_with_type_size_hint(depth),
        )
    }
}
