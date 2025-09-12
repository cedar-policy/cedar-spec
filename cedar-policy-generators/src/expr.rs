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

use crate::abac::{
    AttrValue, AvailableExtensionFunctions, ConstantPool, QualifiedType, Type, UnknownPool,
};
use crate::collections::HashMap;
use crate::err::{while_doing, Error, Result};
use crate::hierarchy::{generate_uid_with_type, Hierarchy};
use crate::schema::{attrs_from_attrs_or_context, uid_for_action_name, Schema};
use crate::settings::ABACSettings;
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_range, size_hint_for_ratio};
use crate::{accum, gen, gen_inner, uniform};
use arbitrary::{Arbitrary, MaxRecursionReached, Unstructured};
use cedar_policy_core::ast;
use cedar_policy_core::validator::json_schema::{EntityTypeKind, StandardEntityType};
use smol_str::SmolStr;
use std::collections::BTreeMap;

/// Struct for generating expressions
#[derive(Debug)]
pub struct ExprGenerator<'a> {
    /// Schema for generated expressions to conform to
    pub schema: &'a Schema,
    /// General settings for ABAC generation, many of which affect expression generation
    pub settings: &'a ABACSettings,
    /// Constant pool to use when needed
    pub constant_pool: &'a ConstantPool,
    /// Unknown pool to use when needed
    pub unknown_pool: &'a UnknownPool,
    /// data on available extension functions
    pub ext_funcs: &'a AvailableExtensionFunctions,
    /// If this is present, any literal UIDs included in generated `Expr`s will
    /// (usually) exist in the hierarchy.
    pub hierarchy: Option<&'a Hierarchy>,
}

impl ExprGenerator<'_> {
    /// get a (fully general) arbitrary expression conforming to the schema, but
    /// no attempt to match types.
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_expr(
        &mut self,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
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
                    self.generate_expr(max_depth - 1, u)?,
                    self.generate_expr(max_depth - 1, u)?,
                ))
            },
            1 => {
                // not expression
                Ok(ast::Expr::not(self.generate_expr(max_depth - 1, u)?))
            },
            1 => {
                // any other expression
                gen!(u,
                    2 => Ok(ast::Expr::ite(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    2 => Ok(ast::Expr::and(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    2 => Ok(ast::Expr::or(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::less(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::lesseq(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::greater(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::greatereq(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::add(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::sub(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::mul(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => {
                        // negation expression
                        Ok(ast::Expr::neg(self.generate_expr(max_depth - 1, u)?))
                    },
                    6 => Ok(ast::Expr::is_in(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains_all(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::contains_any(
                        self.generate_expr(max_depth - 1, u)?,
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    1 => Ok(ast::Expr::is_empty(
                        self.generate_expr(max_depth - 1, u)?,
                    )),
                    2 => {
                        if self.settings.enable_like {
                            Ok(ast::Expr::like(
                                self.generate_expr(max_depth - 1, u)?,
                                self.constant_pool.arbitrary_pattern_literal(u)?,
                            ))
                        } else {
                            Err(Error::LikeDisabled)
                        }
                    },
                    1 => {
                            Ok(ast::Expr::is_entity_type(
                                self.generate_expr(max_depth - 1, u)?,
                                u.choose(&self.schema.entity_types)?.clone(),
                            ))
                    },
                    1 => {
                        let mut l = Vec::new();
                        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                            l.push(self.generate_expr(max_depth - 1, u)?);
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                        Ok(ast::Expr::set(l))
                    },
                    1 => {
                        let mut r = HashMap::new();
                        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                            let attr_name = self.schema.arbitrary_attr(u)?;
                            r.insert(
                                attr_name,
                                self.generate_expr(max_depth - 1, u)?,
                            );
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                        Ok(ast::Expr::record(r).expect("can't have duplicate keys because `r` was already a HashMap"))
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
                                .map(|_| self.generate_expr(max_depth - 1, u))
                                .collect::<Result<_>>()?,
                        ))
                    },
                    7 => {
                        let attr_name = gen!(u,
                            1 => {
                                let s: String = u.arbitrary()?;
                                SmolStr::from(s)
                            },
                            6 => self.schema.arbitrary_attr(u)?);
                        let e = self.generate_expr(max_depth - 1, u)?;
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
                                .expect("can't have duplicate keys because there is only one key")
                        } else {
                            e
                        };
                        Ok(ast::Expr::get_attr(e, attr_name))
                    },
                    4 => {
                        let attr_name = uniform!(u,
                           self.schema.arbitrary_attr(u)?,
                            {
                                let s: String = u.arbitrary()?;
                                SmolStr::from(s)
                            });
                        Ok(ast::Expr::has_attr(
                            self.generate_expr(max_depth - 1, u)?,
                            attr_name,
                        ))
                    },
                    4 => {
                        let tag_name = uniform!(u,
                            self.generate_expr(max_depth - 1, u)?,
                            ast::Expr::val(self.schema.arbitrary_attr(u)?)
                        );
                        let e = self.generate_expr(max_depth - 1, u)?;
                        Ok(ast::Expr::has_tag(e, tag_name))
                    }
                )
            })
        }
    }

    /// get an arbitrary expression of a given type conforming to the schema
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_expr_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        if self.should_generate_unknown(max_depth, u)? {
            let v = self.generate_value_for_type(target_type, max_depth, u)?;
            let name = self.unknown_pool.alloc(target_type.clone(), v);
            let unknown_type: Option<ast::Type> = target_type.clone().try_into().ok();
            match unknown_type {
                Some(ty) => Ok(ast::Expr::unknown(ast::Unknown::new_with_type(name, ty))),
                None => Ok(ast::Expr::unknown(ast::Unknown::new_untyped(name))),
            }
        } else {
            match target_type {
                Type::Bool => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do a literal
                        Ok(ast::Expr::val(u.arbitrary::<bool>()?))
                    } else {
                        gen!(u,
                        // bool literal
                        2 => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
                        // == expression, where types on both sides match
                        5 => {
                            let ty: Type = u.arbitrary()?;
                            Ok(ast::Expr::is_eq(
                                self.generate_expr_for_type(&ty, max_depth - 1, u)?,
                                self.generate_expr_for_type(&ty, max_depth - 1, u)?,
                            ))
                        },
                        // == expression, where types do not match
                        2 => {
                            let ty1: Type = u.arbitrary()?;
                            let ty2: Type = u.arbitrary()?;
                            Ok(ast::Expr::is_eq(
                                self.generate_expr_for_type(
                                    &ty1,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &ty2,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        },
                        // not expression
                        5 => Ok(ast::Expr::not(self.generate_expr_for_type(
                            &Type::bool(),
                            max_depth - 1,
                            u,
                        )?)),
                        // if-then-else expression, where both arms are bools
                        5 => Ok(ast::Expr::ite(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // && expression
                        5 => Ok(ast::Expr::and(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // || expression
                        5 => Ok(ast::Expr::or(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // < expression
                        1 => Ok(ast::Expr::less(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // <= expression
                        1 => Ok(ast::Expr::lesseq(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // > expression
                        1 => Ok(ast::Expr::greater(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // >= expression
                        1 => Ok(ast::Expr::greatereq(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // in expression, non-set form
                        11 => {
                            let ety1 = u.choose(self.schema.entity_types())?;
                            let ety2 = u.choose(self.schema.entity_types())?;
                            Ok(ast::Expr::is_in(
                            self.generate_expr_for_type(
                                &Type::Entity(ety1.clone()),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::Entity(ety2.clone()),
                                max_depth - 1,
                                u,
                            )?,
                        ))},
                        // in expression, set form
                        2 => {
                            let ety1 = u.choose(self.schema.entity_types())?;
                            let ety2 = u.choose(self.schema.entity_types())?;
                            Ok(ast::Expr::is_in(
                            self.generate_expr_for_type(
                                &Type::Entity(ety1.clone()),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                               &Type::set_of(Type::Entity(ety2.clone())),
                                max_depth - 1,
                                u,
                            )?,
                        ))},
                        // contains() on a set
                        2 => {
                            let element_ty = u.arbitrary()?;
                            let element = self.generate_expr_for_type(
                                &element_ty,
                                max_depth - 1,
                                u,
                            )?;
                            let set = self.generate_expr_for_type(
                                &Type::set_of(element_ty),
                                max_depth - 1,
                                u,
                            )?;
                            Ok(ast::Expr::contains(set, element))
                        },
                        // containsAll()
                        1 => Ok(ast::Expr::contains_all(
                            // doesn't require the input sets to have the same element type
                            self.generate_expr_for_type(
                                &Type::set_of(u.arbitrary()?),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::set_of(u.arbitrary()?),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // containsAny()
                        1 => Ok(ast::Expr::contains_any(
                            // doesn't require the input sets to have the same element type
                            self.generate_expr_for_type(
                                &Type::set_of(u.arbitrary()?),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::set_of(u.arbitrary()?),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // isEmpty()
                        1 => Ok(ast::Expr::is_empty(
                            self.generate_expr_for_type(
                                &Type::set_of(u.arbitrary()?),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // like
                        2 => {
                            if self.settings.enable_like {
                                Ok(ast::Expr::like(
                                    self.generate_expr_for_type(
                                        &Type::string(),
                                        max_depth - 1,
                                        u,
                                    )?,
                                    self.constant_pool.arbitrary_pattern_literal(u)?,
                                ))
                            } else {
                                Err(Error::LikeDisabled)
                            }
                        },
                        // is
                        2 => {
                            let ety_l = u.choose(&self.schema.entity_types)?.clone();
                            let ety_r = u.choose(&self.schema.entity_types)?.clone();
                                Ok(ast::Expr::is_entity_type(
                                    self.generate_expr_for_type(
                                        &Type::Entity(ety_l),
                                        max_depth - 1,
                                        u,
                                    )?,
                                    ety_r,
                                ))
                        },
                        // extension function that returns bool
                        2 => self.generate_ext_func_call_for_type(
                            &Type::bool(),
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with type bool
                        1 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_type(
                                &Type::Bool,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name.clone(),
                            ))
                        },
                        // getting an attr (on a record) with type bool
                        1 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &record_type_with_attr(
                                        attr_name.clone(),
                                        Type::Bool,
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an entity tag with type bool
                        1 => {
                            let entity_type = self.schema.arbitrary_entity_type_with_tag_type(
                                &Type::Bool,
                                u,
                            )?;
                            Ok(ast::Expr::get_tag(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &Type::String,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        },
                        // has expression on an entity, for a (possibly optional) attribute the entity does have in the schema
                        2 => {
                            let (entity_name, entity_type) = self
                                .schema
                                .schema
                                .entity_types
                                .iter()
                                .nth(
                                    u.choose_index(self.schema.entity_types.len())
                                        .expect("Failed to select entity index."),
                                )
                                .expect("Failed to select entity from map.");
                            let attr_names: Vec<&SmolStr> = match &entity_type.kind {
                                // Generate an empty vec here so that we fail fast
                                EntityTypeKind::Enum { .. } => vec![],
                                EntityTypeKind::Standard(StandardEntityType { shape, ..}) => attrs_from_attrs_or_context(&self.schema.schema, shape)
                                .attrs
                                .keys()
                                .collect::<Vec<_>>()
                            };
                            let attr_name = SmolStr::clone(u.choose(&attr_names)?);
                            Ok(ast::Expr::has_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(ast::EntityType::from(ast::Name::from(entity_name.clone())).qualify_with(self.schema.namespace())),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // has expression on an entity, for an arbitrary attribute name
                        1 => Ok(ast::Expr::has_attr(
                            self.generate_expr_for_type(
                                &Type::Entity(u.choose(self.schema.entity_types())?.clone()),
                                max_depth - 1,
                                u,
                            )?,
                            self.constant_pool.arbitrary_string_constant(u)?,
                        )),
                        // hasTag expression on an entity, for an arbitrary tag name
                        1 => Ok(ast::Expr::has_tag(
                            self.generate_expr_for_type(
                                &Type::Entity(u.choose(self.schema.entity_types())?.clone()),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::string(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // has expression on a record
                        2 => Ok(ast::Expr::has_attr(
                            self.generate_expr_for_type(
                                &Type::arbitrary_record(u, self.settings.max_width)?,
                                max_depth - 1,
                                u,
                            )?,
                            self.constant_pool.arbitrary_string_constant(u)?,
                        )))
                    }
                }
                Type::Long => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do a literal
                        Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_int_constant(u)?,
                        ))
                    } else {
                        gen!(u,
                        // int literal. weighted highly because all the other choices
                        // are recursive, and we don't want a scenario where we have,
                        // say, a 90% chance to recurse every time
                        16 => Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_int_constant(u)?,
                        )),
                        // if-then-else expression, where both arms are longs
                        5 => Ok(ast::Expr::ite(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // + expression
                        1 => Ok(ast::Expr::add(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // - expression
                        1 => Ok(ast::Expr::sub(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // * expression
                        1 => Ok(ast::Expr::mul(
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::long(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // negation expression
                        1 => Ok(ast::Expr::neg(self.generate_expr_for_type(
                            &Type::long(),
                            max_depth - 1,
                            u,
                        )?)),
                        // extension function that returns a long
                        1 => self.generate_ext_func_call_for_type(
                            &Type::long(),
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with type long
                        4 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_type(
                                &Type::Long,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name.clone(),
                            ))
                        },
                        // getting an attr (on a record) with type long
                        4 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &record_type_with_attr(
                                        attr_name.clone(),
                                        Type::Long,
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an entity tag with type long
                        3 => {
                            let entity_type = self.schema.arbitrary_entity_type_with_tag_type(
                                &Type::Long,
                                u,
                            )?;
                            Ok(ast::Expr::get_tag(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &Type::String,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        })
                    }
                }
                Type::String => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do a literal
                        Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_string_constant(u)?,
                        ))
                    } else {
                        gen!(u,
                        // string literal. weighted highly because all the other choices
                        // are recursive, and we don't want a scenario where we have, say,
                        // a 90% chance to recurse every time
                        16 => Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_string_constant(u)?,
                        )),
                        // if-then-else expression, where both arms are strings
                        5 => Ok(ast::Expr::ite(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::string(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::string(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns a string
                        1 => self.generate_ext_func_call_for_type(
                            &Type::string(),
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with type string
                        4 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_type(
                                &Type::String,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name.clone(),
                            ))
                        },
                        // getting an attr (on a record) with type string
                        4 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &record_type_with_attr(
                                        attr_name.clone(),
                                        Type::String,
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an entity tag with type string
                        3 => {
                            let entity_type = self.schema.arbitrary_entity_type_with_tag_type(
                                &Type::String,
                                u,
                            )?;
                            Ok(ast::Expr::get_tag(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &Type::String,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        })
                    }
                }
                Type::Set(target_element_ty) => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do empty-set
                        Ok(ast::Expr::set(vec![]))
                    } else {
                        gen!(u,
                        // set literal
                        6 => {
                            let mut l = Vec::new();
                            u.arbitrary_loop(
                                Some(0),
                                Some(self.settings.max_width as u32),
                                |u| {
                                    l.push(self.generate_expr_for_type(
                                        &target_element_ty,
                                        max_depth - 1,
                                        u,
                                    )?);
                                    Ok(std::ops::ControlFlow::Continue(()))
                                },
                            )?;
                            Ok(ast::Expr::set(l))
                        },
                        // if-then-else expression, where both arms are (appropriate) sets
                        2 => Ok(ast::Expr::ite(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns an (appropriate) set
                        1 => self.generate_ext_func_call_for_type(
                            target_type,
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with the appropriate set type
                        4 => {
                            let (entity_type, attr_name) =
                                self.schema.arbitrary_attr_for_type(target_type, u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name.clone(),
                            ))
                        },
                        // getting an attr (on a record) with the appropriate set type
                        3 => {
                            let attr_name: SmolStr =
                                self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &record_type_with_attr(attr_name.clone(), target_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an entity tag with the appropriate set type
                        3 => {
                            let entity_type = self.schema.arbitrary_entity_type_with_tag_type(
                                target_type,
                                u,
                            )?;
                            Ok(ast::Expr::get_tag(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &Type::String,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        })
                    }
                }
                Type::Record(m) => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed
                        Err(Error::TooDeep)
                    } else {
                        gen!(u,
                        // record literal
                        2 => {
                            let mut r = HashMap::new();
                            for (a, qt) in m {
                                if qt.required {
                                    r.insert(a.clone(), self.generate_expr_for_type(&qt.ty, max_depth-1, u)?);
                                } else {
                                    if u.ratio(1, 2)? {
                                        r.insert(a.clone(), self.generate_expr_for_type(&qt.ty, max_depth-1, u)?);
                                    }
                                }
                            }
                            Ok(ast::Expr::record(r).expect("can't have duplicate keys because `r` was already a HashMap"))
                        },
                        // if-then-else expression, where both arms are records
                        2 => Ok(ast::Expr::ite(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns a record
                        1 => self.generate_ext_func_call_for_type(
                            target_type,
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with type record
                        4 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_type(
                                &Type::Record(BTreeMap::default()),
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name.clone(),
                            ))
                        },
                        // getting an attr (on a record) with type record
                        3 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &record_type_with_attr(
                                        attr_name.clone(),
                                        Type::Record(BTreeMap::default()),
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an entity tag with type record
                        3 => {
                            let entity_type = self.schema.arbitrary_entity_type_with_tag_type(
                                target_type,
                                u,
                            )?;
                            Ok(ast::Expr::get_tag(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &Type::String,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        })
                    }
                }
                Type::Entity(ety) => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do `principal`, `action`, or `resource`
                        Ok(ast::Expr::var(*u.choose(&[
                            ast::Var::Principal,
                            ast::Var::Action,
                            ast::Var::Resource,
                        ])?))
                    } else {
                        gen!(u,
                        // UID literal, that exists
                        11 => Ok(ast::Expr::val(self.arbitrary_uid_with_type(ety, u)?)),
                        // UID literal, that doesn't exist
                        2 => Ok(ast::Expr::val(u.arbitrary::<ast::EntityUID>()?)),
                        // `principal`
                        6 => Ok(ast::Expr::var(ast::Var::Principal)),
                        // `action`
                        6 => Ok(ast::Expr::var(ast::Var::Action)),
                        // `resource`
                        6 => Ok(ast::Expr::var(ast::Var::Resource)),
                        // if-then-else expression, where both arms are entities
                        2 => Ok(ast::Expr::ite(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns an entity
                        1 => self.generate_ext_func_call_for_type(
                            target_type,
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with type entity
                        6 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_type(
                                &Type::Entity(u.choose(&self.schema.entity_types)?.clone()),
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name.clone(),
                            ))
                        },
                        // getting an attr (on a record) with type entity
                        5 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &record_type_with_attr(
                                        attr_name.clone(),
                                        Type::Entity(
                                            u.choose(&self.schema.entity_types)?.clone(),
                                        ),
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an entity tag with type entity
                        5 => {
                            let entity_type = self.schema.arbitrary_entity_type_with_tag_type(
                                &Type::Entity(u.choose(&self.schema.entity_types)?.clone()),
                                u,
                            )?;
                            Ok(ast::Expr::get_tag(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &Type::String,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        })
                    }
                }
                Type::IPAddr | Type::Decimal | Type::DateTime | Type::Duration => {
                    if !self.settings.enable_extensions {
                        return Err(Error::ExtensionsDisabled);
                    };
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just call the constructor
                        // Invariant (MethodStyleArgs), Function Style, no worries
                        self.arbitrary_ext_constructor_call_for_type(
                            target_type,
                            ast::Expr::val,
                            ast::Expr::call_extension_fn,
                            u,
                        )
                    } else {
                        gen!(u,
                        // if-then-else expression, where both arms are extension types
                        2 => Ok(ast::Expr::ite(
                            self.generate_expr_for_type(
                                &Type::bool(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                target_type,
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns an extension type
                        9 => self.generate_ext_func_call_for_type(
                            target_type,
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with extension type
                        2 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_type(
                                target_type,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type.clone()),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name.clone(),
                            ))
                        },
                        // getting an attr (on a record) with extension type
                        2 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_type(
                                    &record_type_with_attr(
                                        attr_name.clone(),
                                        target_type.clone(),
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an entity tag with extension type
                        5 => {
                            let entity_type = self.schema.arbitrary_entity_type_with_tag_type(
                                target_type,
                                u,
                            )?;
                            Ok(ast::Expr::get_tag(
                                self.generate_expr_for_type(
                                    &Type::Entity(entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                self.generate_expr_for_type(
                                    &Type::String,
                                    max_depth - 1,
                                    u,
                                )?,
                            ))
                        })
                    }
                }
            }
        }
    }

    /// get an arbitrary constant of a given type, as an expression.
    #[allow(dead_code)]
    fn generate_const_expr_for_type(
        &self,
        target_type: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        match target_type {
            Type::Bool => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
            Type::Long => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_int_constant(u)?,
            )),
            Type::String => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_string_constant(u)?,
            )),
            Type::Set(el_ty) => {
                let mut l = Vec::new();
                u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                    l.push(self.generate_const_expr_for_type(el_ty, u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::set(l))
            }
            Type::Record(m) => {
                let mut r = HashMap::new();
                for (a, qt) in m {
                    if qt.required {
                        r.insert(a.clone(), self.generate_const_expr_for_type(&qt.ty, u)?);
                    } else {
                        if u.ratio(1, 2)? {
                            r.insert(a.clone(), self.generate_const_expr_for_type(&qt.ty, u)?);
                        }
                    }
                }
                Ok(ast::Expr::record(r)
                    .expect("can't have duplicate keys because `r` was already a HashMap"))
            }
            Type::Entity(ety) => {
                gen!(u,
                // UID literal, that exists
                3 => Ok(ast::Expr::val(self.arbitrary_uid_with_type(ety, u)?)),
                // UID literal, that doesn't exist
                1 => Ok(ast::Expr::val(u.arbitrary::<ast::EntityUID>()?))
                )
            }
            Type::IPAddr | Type::Decimal | Type::DateTime | Type::Duration => {
                unimplemented!("constant expression of type ipaddr or decimal")
            }
        }
    }

    /// internal helper function: get an extension-function-call expression that
    /// returns the given type
    ///
    /// `max_depth`: maximum depth of each argument expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    fn generate_ext_func_call_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        let func = self.ext_funcs.arbitrary_for_type(target_type, u)?;
        assert_eq!(&func.return_ty, target_type);
        let args = func
            .parameter_types
            .iter()
            .map(|param_ty| self.generate_expr_for_type(param_ty, max_depth, u))
            .collect::<Result<_>>()?;
        Ok(ast::Expr::call_extension_fn(func.name.clone(), args))
    }

    /// Generate a call for an extension constructor producing `target_type`.
    /// This functions is used to produce either `AttrValue`
    /// extension constructors, or `Expr` extension constructors, by passing `mk_str`
    /// and `mk_ext` functions that build string literals and extension function
    /// calls for these types.
    fn arbitrary_ext_constructor_call_for_type<E>(
        &self,
        target_type: &Type,
        mk_str: fn(SmolStr) -> E,
        mk_ext: fn(ast::Name, Vec<E>) -> E,
        u: &mut Unstructured<'_>,
    ) -> Result<E> {
        let func = self
            .ext_funcs
            .arbitrary_constructor_for_type(target_type, u)?;
        assert_eq!(&func.return_ty, target_type);
        assert!(
            func.name.is_unqualified(),
            "Expected that all extension functions would be unqualified, but {func_name} is not.",
            func_name = func.name
        );
        let name_as_ref = func.name.basename_as_ref().as_ref();
        let args = match name_as_ref {
            "ip" => vec![mk_str(self.constant_pool.arbitrary_ip_str(u)?)],
            "decimal" => vec![mk_str(self.constant_pool.arbitrary_decimal_str(u)?)],
            "datetime" => vec![mk_str(self.constant_pool.arbitrary_datetime_str(u)?)],
            "offset" => {
                let base_datetime_str = self.constant_pool.arbitrary_datetime_str(u)?;
                let offset_duration_str = self.constant_pool.arbitrary_duration_str(u)?;
                vec![
                    mk_ext(
                        ast::Name::parse_unqualified_name("datetime")
                            .expect("should be a valid identifier"),
                        vec![mk_str(base_datetime_str)],
                    ),
                    mk_ext(
                        ast::Name::parse_unqualified_name("duration")
                            .expect("should be a valid identifier"),
                        vec![mk_str(offset_duration_str)],
                    ),
                ]
            }
            "duration" => vec![mk_str(self.constant_pool.arbitrary_duration_str(u)?)],
            _ => unreachable!("unhandled extension constructor {name_as_ref}"),
        };
        assert_eq!(
            args.len(),
            func.parameter_types.len(),
            "Generated wrong number of args for {name_as_ref} extension constructor"
        );

        Ok(mk_ext(func.name.clone(), args))
    }

    /// get an AttrValue of the given type which conforms to this schema
    ///
    /// If `hierarchy` is present, any literal UIDs included in the AttrValue
    /// will (usually) exist in the hierarchy.
    ///
    /// `max_depth`: maximum depth of the attribute value expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_attr_value_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<AttrValue> {
        match target_type {
            Type::Bool => {
                // the only valid bool-typed attribute value is a bool literal
                Ok(AttrValue::BoolLit(u.arbitrary()?))
            }
            Type::Long => {
                // the only valid long-typed attribute value is an int literal
                Ok(AttrValue::IntLit(
                    self.constant_pool.arbitrary_int_constant(u)?,
                ))
            }
            Type::String => {
                // the only valid string-typed attribute value is a string literal
                Ok(AttrValue::StringLit(
                    self.constant_pool.arbitrary_string_constant(u)?,
                ))
            }
            Type::Entity(ety) => {
                // the only valid entity-typed attribute value is a UID literal
                Ok(AttrValue::UIDLit(self.arbitrary_uid_with_type(ety, u)?))
            }
            Type::IPAddr | Type::Decimal | Type::DateTime | Type::Duration => {
                // the only valid extension-typed attribute value is a call of an extension constructor with return the type returned
                if max_depth == 0 {
                    return Err(Error::TooDeep);
                }
                self.arbitrary_ext_constructor_call_for_type(
                    target_type,
                    AttrValue::StringLit,
                    |fn_name, args| AttrValue::ExtFuncCall { fn_name, args },
                    u,
                )
            }
            Type::Set(target_element_ty) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(AttrValue::Set(vec![]))
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.generate_attr_value_for_type(
                            &target_element_ty,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(AttrValue::Set(l))
                }
            }
            Type::Record(m) => {
                let mut r = HashMap::new();
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty record
                    Ok(AttrValue::Record(HashMap::new()))
                } else {
                    for (attr, qt) in m {
                        if qt.required {
                            r.insert(
                                attr.clone(),
                                self.generate_attr_value_for_type(&qt.ty, max_depth - 1, u)?,
                            );
                        } else {
                            if u.ratio(1, 2)? {
                                r.insert(
                                    attr.clone(),
                                    self.generate_attr_value_for_type(&qt.ty, max_depth - 1, u)?,
                                );
                            }
                        }
                    }
                    Ok(AttrValue::Record(r))
                }
            }
        }
    }

    /// size hint for arbitrary_attr_value_for_type()
    #[allow(dead_code)]
    pub fn generate_attr_value_for_type_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        arbitrary::size_hint::try_recursion_guard(depth, |depth| {
            Ok(arbitrary::size_hint::and(
                size_hint_for_range(0, 7),
                arbitrary::size_hint::or_all(&[
                    <bool as Arbitrary>::size_hint(depth),
                    ConstantPool::arbitrary_int_constant_size_hint(depth),
                    ConstantPool::arbitrary_string_constant_size_hint(depth),
                    ExprGenerator::generate_uid_size_hint(depth),
                    arbitrary::size_hint::and_all(&[
                        AvailableExtensionFunctions::arbitrary_constructor_for_type_size_hint(
                            depth,
                        ),
                        size_hint_for_ratio(9, 10),
                        size_hint_for_range(0, 4),
                        Self::generate_attr_value_for_type_size_hint(depth)?,
                    ]),
                    (1, None), // not sure how to hint for arbitrary_loop()
                    (1, None), // not sure how to hint for arbitrary_loop()
                    (1, None), // not sure how to hint for arbitrary_loop()
                ]),
            ))
        })
    }

    /// size hint for generate_attr_value_for_schematype()
    #[allow(dead_code)]
    pub fn generate_attr_value_for_schematype_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        arbitrary::size_hint::try_recursion_guard(depth, |depth| {
            Ok(arbitrary::size_hint::or_all(&[
                Self::generate_attr_value_for_type_size_hint(depth)?,
                (1, None), // not sure how to hint for arbitrary_loop()
                Self::arbitrary_uid_with_type_size_hint(depth),
                Self::generate_attr_value_for_type_size_hint(depth)?,
            ]))
        })
    }

    /// generate an arbitrary `Value` of the given `target_type`
    pub fn generate_value_for_type(
        &self,
        target_type: &Type,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Value> {
        use ast::Value;
        match target_type {
            Type::Bool => {
                // the only valid bool-typed attribute value is a bool literal
                let b: bool = u.arbitrary()?;
                Ok(Value::from(b))
            }
            Type::Long => {
                // the only valid long-typed attribute value is an int literal
                Ok(Value::from(self.constant_pool.arbitrary_int_constant(u)?))
            }
            Type::String => {
                // the only valid string-typed attribute value is a string literal
                Ok(Value::from(
                    self.constant_pool.arbitrary_string_constant(u)?,
                ))
            }
            Type::Entity(ety) => {
                // the only valid entity-typed attribute value is a UID literal
                Ok(Value::from(self.arbitrary_uid_with_type(ety, u)?))
            }
            Type::Set(target_element_ty) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(Value::empty_set(None))
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.generate_value_for_type(
                            &target_element_ty,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(Value::set(l, None))
                }
            }
            Type::Record(m) => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty record
                    Ok(Value::empty_record(None))
                } else {
                    let mut r = HashMap::new();
                    for (a, qt) in m {
                        if qt.required {
                            r.insert(
                                a.clone(),
                                self.generate_value_for_type(&qt.ty, max_depth - 1, u)?,
                            );
                        } else {
                            if u.ratio(1, 2)? {
                                r.insert(
                                    a.clone(),
                                    self.generate_value_for_type(&qt.ty, max_depth - 1, u)?,
                                );
                            }
                        }
                    }
                    Ok(Value::record(r, None))
                }
            }
            _ => Err(Error::ExtensionsDisabled),
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
            let mut r = HashMap::new();
            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                let attr_name = self.schema.arbitrary_attr(u)?;
                r.insert(attr_name, self.generate_const_expr(u)?);
                Ok(std::ops::ControlFlow::Continue(()))
            })?;
            Ok(ast::Expr::record(r).expect("can't have duplicate keys because `r` was already a HashMap"))
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
        4 => Ok(ast::Expr::val(u.arbitrary::<ast::EntityUID>()?))
        )
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
                .map_err(|e| while_doing("choosing a principal type".into(), e))?,
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
            .map_err(|e| while_doing("choosing an action".into(), e))?;
        Ok(uid_for_action_name(
            self.schema.namespace.as_ref(),
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
                .map_err(|e| while_doing("choosing a resource type".into(), e))?,
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
        ty: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        match self.hierarchy {
            None => generate_uid_with_type(ty.clone(), &self.schema.get_uid_enum_choices(ty), u),
            Some(hierarchy) => hierarchy.arbitrary_uid_with_type(Some(self.schema), ty, u),
        }
    }
    /// size hint for arbitrary_uid_with_type()
    pub fn arbitrary_uid_with_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::or(
            <ast::Eid as Arbitrary>::size_hint(depth),
            Hierarchy::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    /// Decide if we should fill the current AST node w/ an unknown
    /// We want the chance of generating an unknown to go up the lower in the
    /// AST we are.
    fn should_generate_unknown(&self, max_depth: usize, u: &mut Unstructured<'_>) -> Result<bool> {
        if self.settings.enable_unknowns {
            let chance = self.settings.max_depth - max_depth;
            let choice = u.int_in_range::<usize>(0..=self.settings.max_depth)?;
            Ok(choice <= chance)
        } else {
            Ok(false)
        }
    }
}

/// internal helper function, get a [`abac::Type`] representing a Record
/// with (at least) one attribute of the specified name and type.
fn record_type_with_attr(attr_name: SmolStr, attr_type: Type) -> Type {
    Type::Record(BTreeMap::from_iter([(
        attr_name,
        QualifiedType {
            ty: attr_type,
            required: true,
        },
    )]))
}
