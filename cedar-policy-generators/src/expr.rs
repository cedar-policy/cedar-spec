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

use crate::abac::{AttrValue, AvailableExtensionFunctions, ConstantPool, Type, UnknownPool};
use crate::collections::HashMap;
use crate::err::{while_doing, Error, Result};
use crate::hierarchy::{
    arbitrary_specified_uid, generate_uid_with_type, EntityUIDGenMode, Hierarchy,
};
use crate::schema::{
    attrs_from_attrs_or_context, entity_type_name_to_schema_type, uid_for_action_name, Schema,
};
use crate::settings::ABACSettings;
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_range, size_hint_for_ratio};
use crate::{accum, gen, gen_inner, uniform};
use arbitrary::{Arbitrary, Unstructured};
use cedar_policy_core::ast::{self, Id};
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
    /// For any entity UIDs that are generated as part of the expression.
    /// As of this writing, this is only used when `hierarchy` is `None`.
    pub uid_gen_mode: EntityUIDGenMode,
}

impl<'a> ExprGenerator<'a> {
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
                            let (attr_name, _) = self.schema.arbitrary_attr(u)?;
                            r.insert(
                                attr_name.clone(),
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
                            6 => self.schema.arbitrary_attr(u)?.0.clone());
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
                           self.schema.arbitrary_attr(u)?.0.clone(),
                            {
                                let s: String = u.arbitrary()?;
                                SmolStr::from(s)
                            });
                        Ok(ast::Expr::has_attr(
                            self.generate_expr(max_depth - 1, u)?,
                            attr_name,
                        ))
                    })
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
                        11 => Ok(ast::Expr::is_in(
                            self.generate_expr_for_type(
                                &Type::entity(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::entity(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // in expression, set form
                        2 => Ok(ast::Expr::is_in(
                            self.generate_expr_for_type(
                                &Type::entity(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::set_of(Type::entity()),
                                max_depth - 1,
                                u,
                            )?,
                        )),
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
                                Ok(ast::Expr::is_entity_type(
                                    self.generate_expr_for_type(
                                        &Type::entity(),
                                        max_depth - 1,
                                        u,
                                    )?,
                                    u.choose(&self.schema.entity_types)?.clone(),
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
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_schematype(
                                cedar_policy_validator::SchemaTypeVariant::Boolean,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an attr (on a record) with type bool
                        1 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        cedar_policy_validator::SchemaTypeVariant::Boolean,
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
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
                            let attr_names: Vec<&SmolStr> =
                                attrs_from_attrs_or_context(&self.schema.schema, &entity_type.shape)
                                    .attrs
                                    .keys()
                                    .collect::<Vec<_>>();
                            let attr_name = SmolStr::clone(u.choose(&attr_names)?);
                            Ok(ast::Expr::has_attr(
                                self.generate_expr_for_schematype(
                                    &cedar_policy_validator::SchemaType::Type(
                                        cedar_policy_validator::SchemaTypeVariant::Entity {
                                            // This does not use an explicit namespace because entity types
                                            // implicitly use the schema namespace if an explicit one is not
                                            // provided.
                                            name: ast::Name::from(entity_name.clone()).into(),
                                        }
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // has expression on an entity, for an arbitrary attribute name
                        1 => Ok(ast::Expr::has_attr(
                            self.generate_expr_for_type(
                                &Type::entity(),
                                max_depth - 1,
                                u,
                            )?,
                            self.constant_pool.arbitrary_string_constant(u)?,
                        )),
                        // has expression on a record
                        2 => Ok(ast::Expr::has_attr(
                            self.generate_expr_for_type(
                                &Type::record(),
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
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_schematype(
                                cedar_policy_validator::SchemaTypeVariant::Long,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an attr (on a record) with type long
                        4 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        cedar_policy_validator::SchemaTypeVariant::Long,
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
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
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_schematype(
                                cedar_policy_validator::SchemaTypeVariant::String,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an attr (on a record) with type string
                        4 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        cedar_policy_validator::SchemaTypeVariant::String,
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
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
                            let target_element_ty = target_element_ty
                                .as_ref()
                                .map_or_else(|| u.arbitrary(), |ty| Ok((*ty).clone()))?;
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
                                self.generate_expr_for_schematype(
                                    &entity_type_name_to_schema_type(entity_type),
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
                            let attr_ty: cedar_policy_validator::SchemaType<ast::Name> =
                                match self.schema.try_into_schematype(target_type, u)? {
                                    Some(schematy) => schematy,
                                    None => return Err(Error::IncorrectFormat {
                                        doing_what: format!("target_type {target_type:?} not supported in this position"),
                                    })
                                };
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &record_schematype_with_attr(attr_name.clone(), attr_ty),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        })
                    }
                }
                Type::Record => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed
                        Err(Error::TooDeep)
                    } else {
                        gen!(u,
                        // record literal
                        2 => {
                            let mut r = HashMap::new();
                            u.arbitrary_loop(
                                Some(0),
                                Some(self.settings.max_width as u32),
                                |u| {
                                    let attr_val = self.generate_expr_for_type(
                                        &u.arbitrary()?,
                                        max_depth - 1,
                                        u,
                                    )?;
                                    r.insert(
                                        self.constant_pool.arbitrary_string_constant(u)?,
                                        attr_val,
                                    );
                                    Ok(std::ops::ControlFlow::Continue(()))
                                },
                            )?;
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
                                &Type::record(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::record(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns a record
                        1 => self.generate_ext_func_call_for_type(
                            &Type::record(),
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with type record
                        4 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_schematype(
                                cedar_policy_validator::SchemaTypeVariant::Record {
                                    // TODO: should we put in some other attributes that appear in schema?
                                    attributes: BTreeMap::new(),
                                    additional_attributes: true,
                                },
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an attr (on a record) with type record
                        3 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        cedar_policy_validator::SchemaTypeVariant::Record {
                                            attributes: BTreeMap::new(),
                                            additional_attributes: true,
                                        },
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        })
                    }
                }
                Type::Entity => {
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
                        11 => Ok(ast::Expr::val(self.generate_uid(u)?)),
                        // UID literal, that doesn't exist
                        2 => Ok(ast::Expr::val(
                            arbitrary_specified_uid(u)?,
                        )),
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
                                &Type::entity(),
                                max_depth - 1,
                                u,
                            )?,
                            self.generate_expr_for_type(
                                &Type::entity(),
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns an entity
                        1 => self.generate_ext_func_call_for_type(
                            &Type::entity(),
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with type entity
                        6 => {
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_schematype(
                                entity_type_name_to_schema_type(u.choose(&self.schema.entity_types)?),
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an attr (on a record) with type entity
                        5 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        entity_type_name_to_schema_type(
                                            u.choose(&self.schema.entity_types)?,
                                        ),
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        })
                    }
                }
                Type::IPAddr | Type::Decimal => {
                    if !self.settings.enable_extensions {
                        return Err(Error::ExtensionsDisabled);
                    };
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just call the constructor
                        // Invariant (MethodStyleArgs), Function Style, no worries
                        let constructor = self
                            .ext_funcs
                            .arbitrary_constructor_for_type(target_type, u)?;
                        let args = vec![ast::Expr::val(match target_type {
                            Type::IPAddr => self.constant_pool.arbitrary_ip_str(u)?,
                            Type::Decimal => self.constant_pool.arbitrary_decimal_str(u)?,
                            _ => unreachable!("ty is deemed to be an extension type"),
                        })];
                        Ok(ast::Expr::call_extension_fn(constructor.name.clone(), args))
                    } else {
                        let type_name: Id = match target_type {
                            Type::IPAddr => "ipaddr".parse::<Id>().unwrap(),
                            Type::Decimal => "decimal".parse().unwrap(),
                            _ => unreachable!("target type is deemed to be an extension type!"),
                        };
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
                            let (entity_type, attr_name) = self.schema.arbitrary_attr_for_schematype(
                                cedar_policy_validator::SchemaTypeVariant::Extension {
                                    name: type_name,
                                },
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        },
                        // getting an attr (on a record) with type extension type
                        2 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.generate_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        cedar_policy_validator::SchemaTypeVariant::Extension {
                                            name: type_name,
                                        },
                                    ),
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        })
                    }
                }
            }
        }
    }

    /// get an arbitrary expression of a given schematype conforming to the schema
    ///
    /// If `hierarchy` is present, any literal UIDs included in the Expr will
    /// (usually) exist in the hierarchy.
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_expr_for_schematype(
        &self,
        target_type: &cedar_policy_validator::SchemaType<ast::Name>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        use cedar_policy_validator::SchemaType;
        use cedar_policy_validator::SchemaTypeVariant;
        match target_type {
            SchemaType::TypeDef { type_name } => self.generate_expr_for_schematype(
                self.schema
                    .schema
                    .common_types
                    .get(&type_name.clone().try_into().unwrap())
                    .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
                max_depth,
                u,
            ),
            SchemaType::Type(SchemaTypeVariant::Boolean) => {
                self.generate_expr_for_type(&Type::bool(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::Long) => {
                self.generate_expr_for_type(&Type::long(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::String) => {
                self.generate_expr_for_type(&Type::string(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::Set {
                element: element_ty,
            }) => {
                if max_depth == 0 || u.len() < 10 {
                    // no recursion allowed, so, just do empty-set
                    Ok(ast::Expr::set(vec![]))
                } else {
                    gen!(u,
                    // set literal
                    6 => {
                        let mut l = Vec::new();
                        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                            l.push(self.generate_expr_for_schematype(
                                element_ty,
                                max_depth - 1,
                                u,
                            )?);
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                        Ok(ast::Expr::set(l))
                    },
                    // if-then-else expression, where both arms are (appropriate) sets
                    2 => Ok(ast::Expr::ite(
                        self.generate_expr_for_type(
                            &Type::bool(),
                            max_depth - 1,
                            u,
                        )?,
                        self.generate_expr_for_schematype(
                            element_ty,
                            max_depth - 1,
                            u,
                        )?,
                        self.generate_expr_for_schematype(
                            element_ty,
                            max_depth - 1,
                            u,
                        )?,
                    )),
                    // extension function that returns an (appropriate) set
                    1 => self.generate_ext_func_call_for_schematype(
                        element_ty,
                        max_depth - 1,
                        u,
                    ),
                    // getting an attr (on an entity) with the appropriate set type
                    4 => {
                        let (entity_type, attr_name) =
                            self.schema.arbitrary_attr_for_schematype(target_type.clone(), u)?;
                        Ok(ast::Expr::get_attr(
                            self.generate_expr_for_schematype(
                                &entity_type_name_to_schema_type(&entity_type),
                                max_depth - 1,
                                u,
                            )?,
                            attr_name,
                        ))
                    },
                    // getting an attr (on a record) with the appropriate set type
                    3 => {
                        let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                        let record_expr = self.generate_expr_for_schematype(
                            &record_schematype_with_attr(
                                attr_name.clone(),
                                target_type.clone(),
                            ),
                            max_depth - 1,
                            u,
                        )?;
                        Ok(ast::Expr::get_attr(record_expr, attr_name))
                    })
                }
            }
            SchemaType::Type(SchemaTypeVariant::Record {
                attributes,
                additional_attributes,
            }) => {
                if max_depth == 0 || u.len() < 10 {
                    // no recursion allowed
                    Err(Error::TooDeep)
                } else {
                    gen!(u,
                    // record literal
                    2 => {
                        let mut r: HashMap<SmolStr, ast::Expr> = HashMap::new();
                        if *additional_attributes {
                            // maybe add some additional attributes with arbitrary types
                            u.arbitrary_loop(
                                None,
                                Some(self.settings.max_width as u32),
                                |u| {
                                    let attr_type = if self.settings.enable_extensions {
                                        u.arbitrary()?
                                    } else {
                                        Type::arbitrary_nonextension(u)?
                                    };
                                    let attr_name = {
                                        let s: String = u.arbitrary()?;
                                        SmolStr::from(s)
                                    };
                                    r.insert(
                                        attr_name,
                                        self.generate_expr_for_type(
                                            &attr_type,
                                            max_depth - 1,
                                            u,
                                        )?,
                                    );
                                    Ok(std::ops::ControlFlow::Continue(()))
                                },
                            )?;
                        }
                        for (attr, ty) in attributes {
                            // now add the actual optional and required attributes, with the
                            // correct types.
                            // Doing this second ensures that we overwrite any "additional"
                            // attributes so that they definitely have the required type, in
                            // case we got a name collision between an explicitly specified
                            // attribute and one of the "additional" ones we added.
                            if ty.required || u.ratio::<u8>(1, 2)? {
                                let attr_val = self.generate_expr_for_schematype(
                                    &ty.ty,
                                    max_depth - 1,
                                    u,
                                )?;
                                r.insert(attr.clone(), attr_val);
                            }
                        }
                        Ok(ast::Expr::record(r).expect("can't have duplicate keys because `r` was already a HashMap"))
                    },
                    // `context`, if `context` is an appropriate record type
                    // TODO: Check if the `context` is the appropriate type, and
                    // return it if it is.
                    14 => Err(Error::TooDeep),
                    // if-then-else expression, where both arms are (appropriate) records
                    2 => Ok(ast::Expr::ite(
                        self.generate_expr_for_type(
                            &Type::bool(),
                            max_depth - 1,
                            u,
                        )?,
                        self.generate_expr_for_schematype(
                            target_type,
                            max_depth - 1,
                            u,
                        )?,
                        self.generate_expr_for_schematype(
                            target_type,
                            max_depth - 1,
                            u,
                        )?,
                    )),
                    // extension function that returns an appropriate record
                    1 => self.generate_ext_func_call_for_schematype(
                        target_type,
                        max_depth - 1,
                        u,
                    ),
                    // getting an attr (on an entity) with an appropriate record type
                    4 => {
                        let (entity_type, attr_name) =
                            self.schema.arbitrary_attr_for_schematype(target_type.clone(), u)?;
                        Ok(ast::Expr::get_attr(
                            self.generate_expr_for_schematype(
                                &entity_type_name_to_schema_type(&entity_type),
                                max_depth - 1,
                                u,
                            )?,
                            attr_name,
                        ))
                    },
                    // getting an attr (on a record) with an appropriate record type
                    3 => {
                        let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                        Ok(ast::Expr::get_attr(
                            self.generate_expr_for_schematype(
                                &record_schematype_with_attr(
                                    attr_name.clone(),
                                    target_type.clone(),
                                ),
                                max_depth - 1,
                                u,
                            )?,
                            attr_name,
                        ))
                    })
                }
            }
            SchemaType::Type(SchemaTypeVariant::Entity { name }) => {
                if max_depth == 0 || u.len() < 10 {
                    // no recursion allowed, so, just do `principal`, `action`, or `resource`
                    Ok(ast::Expr::var(*u.choose(&[
                        ast::Var::Principal,
                        ast::Var::Action,
                        ast::Var::Resource,
                    ])?))
                } else {
                    gen!(u,
                    // UID literal
                    13 => {
                        let entity_type_name = ast::EntityType::from(name.qualify_with(self.schema.namespace()));
                        Ok(ast::Expr::val(self.arbitrary_uid_with_type(
                            &entity_type_name, u,
                        )?))
                    },
                    // `principal`
                    6 => Ok(ast::Expr::var(ast::Var::Principal)),
                    // `action`
                    6 => Ok(ast::Expr::var(ast::Var::Action)),
                    // `resource`
                    6 => Ok(ast::Expr::var(ast::Var::Resource)),
                    // if-then-else expression, where both arms are entities with the appropriate type
                    2 => Ok(ast::Expr::ite(
                        self.generate_expr_for_type(
                            &Type::bool(),
                            max_depth - 1,
                            u,
                        )?,
                        self.generate_expr_for_schematype(
                            target_type,
                            max_depth - 1,
                            u,
                        )?,
                        self.generate_expr_for_schematype(
                            target_type,
                            max_depth - 1,
                            u,
                        )?,
                    )),
                    // extension function that returns an entity
                    1 => {
                        // TODO: this doesn't guarantee it returns the _correct_ entity type
                        self.generate_ext_func_call_for_type(
                            &Type::entity(),
                            max_depth - 1,
                            u,
                        )
                    },
                    // getting an attr (on an entity) with the appropriate entity type
                    6 => {
                        let (entity_type, attr_name) =
                            self.schema.arbitrary_attr_for_schematype(target_type.clone(), u)?;
                        Ok(ast::Expr::get_attr(
                            self.generate_expr_for_schematype(
                                &entity_type_name_to_schema_type(&entity_type),
                                max_depth - 1,
                                u,
                            )?,
                            attr_name,
                        ))
                    },
                    // getting an attr (on a record) with the appropriate entity type
                    5 => {
                        let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                        Ok(ast::Expr::get_attr(
                            self.generate_expr_for_schematype(
                                &record_schematype_with_attr(
                                    attr_name.clone(),
                                    target_type.clone(),
                                ),
                                max_depth - 1,
                                u,
                            )?,
                            attr_name,
                        ))
                    })
                }
            }
            SchemaType::Type(SchemaTypeVariant::Extension { name }) => match name.as_ref() {
                "ipaddr" => self.generate_expr_for_type(&Type::ipaddr(), max_depth, u),
                "decimal" => self.generate_expr_for_type(&Type::decimal(), max_depth, u),
                _ => panic!("unrecognized extension type: {name:?}"),
            },
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
                    let el = match el_ty {
                        None => self.generate_const_expr(u)?,
                        Some(el_ty) => self.generate_const_expr_for_type(el_ty, u)?,
                    };
                    l.push(el);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::set(l))
            }
            Type::Record => {
                let mut r = HashMap::new();
                u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                    let (attr_name, _) = self.schema.arbitrary_attr(u)?;
                    r.insert(attr_name.clone(), self.generate_const_expr(u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::record(r)
                    .expect("can't have duplicate keys because `r` was already a HashMap"))
            }
            Type::Entity => {
                gen!(u,
                // UID literal, that exists
                3 => Ok(ast::Expr::val(self.generate_uid(u)?)),
                // UID literal, that doesn't exist
                1 => Ok(ast::Expr::val(
                    arbitrary_specified_uid(u)?,
                )))
            }
            Type::IPAddr | Type::Decimal => {
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

    /// internal helper function: get an extension-function-call expression that
    /// returns the given schematype
    ///
    /// `max_depth`: maximum depth of each argument expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    fn generate_ext_func_call_for_schematype(
        &self,
        target_type: &cedar_policy_validator::SchemaType<ast::Name>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        use cedar_policy_validator::SchemaType;
        use cedar_policy_validator::SchemaTypeVariant;
        match target_type {
            SchemaType::TypeDef { type_name } => self.generate_ext_func_call_for_schematype(
                self.schema
                    .schema
                    .common_types
                    .get(&type_name.clone().try_into().unwrap())
                    .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
                max_depth,
                u,
            ),
            SchemaType::Type(ty) => match ty {
                SchemaTypeVariant::Boolean => {
                    self.generate_ext_func_call_for_type(&Type::bool(), max_depth, u)
                }
                SchemaTypeVariant::Long => {
                    self.generate_ext_func_call_for_type(&Type::long(), max_depth, u)
                }
                SchemaTypeVariant::String => {
                    self.generate_ext_func_call_for_type(&Type::string(), max_depth, u)
                }
                SchemaTypeVariant::Extension { name } => match name.as_ref() {
                    "ipaddr" => self.generate_ext_func_call_for_type(&Type::ipaddr(), max_depth, u),
                    "decimal" => {
                        self.generate_ext_func_call_for_type(&Type::decimal(), max_depth, u)
                    }
                    _ => panic!("unrecognized extension type: {name:?}"),
                },
                // no existing extension functions return set type
                SchemaTypeVariant::Set { .. } => Err(Error::EmptyChoose {
                    doing_what: "getting an extension function returning set type".into(),
                }),
                // no existing extension functions return record type
                SchemaTypeVariant::Record { .. } => Err(Error::EmptyChoose {
                    doing_what: "getting an extension function returning record type".into(),
                }),
                // no existing extension functions return entity type
                SchemaTypeVariant::Entity { .. } => Err(Error::EmptyChoose {
                    doing_what: "getting an extension function returning entity type".into(),
                }),
            },
        }
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
            Type::Entity => {
                // the only valid entity-typed attribute value is a UID literal
                Ok(AttrValue::UIDLit(self.generate_uid(u)?))
            }
            Type::IPAddr | Type::Decimal => {
                // the only valid extension-typed attribute value is a call of an extension constructor with return the type returned
                if max_depth == 0 {
                    return Err(Error::TooDeep);
                }
                let func = self
                    .ext_funcs
                    .arbitrary_constructor_for_type(target_type, u)?;
                assert_eq!(&func.return_ty, target_type);
                let args = func
                    .parameter_types
                    .iter()
                    .map(|_| match target_type {
                        Type::IPAddr => self
                            .constant_pool
                            .arbitrary_ip_str(u)
                            .map(AttrValue::StringLit),
                        Type::Decimal => self
                            .constant_pool
                            .arbitrary_decimal_str(u)
                            .map(AttrValue::StringLit),
                        _ => unreachable!("target_type should only be one of these two"),
                    })
                    .collect::<Result<_>>()?;
                Ok(AttrValue::ExtFuncCall {
                    fn_name: func.name.clone(),
                    args,
                })
            }
            Type::Set(target_element_ty) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(AttrValue::Set(vec![]))
                } else {
                    let mut l = Vec::new();
                    let target_element_ty = match target_element_ty {
                        None => {
                            if self.settings.enable_extensions {
                                u.arbitrary()?
                            } else {
                                Type::arbitrary_nonextension(u)?
                            }
                        }
                        Some(ty) => *ty.clone(),
                    };
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
            Type::Record => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty record
                    Ok(AttrValue::Record(HashMap::new()))
                } else {
                    let mut r = HashMap::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        let (attr_name, attr_ty) = self.schema.arbitrary_attr(u)?.clone();
                        let attr_val =
                            self.generate_attr_value_for_schematype(&attr_ty, max_depth - 1, u)?;
                        r.insert(attr_name, attr_val);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(AttrValue::Record(r))
                }
            }
        }
    }

    /// size hint for arbitrary_attr_value_for_type()
    #[allow(dead_code)]
    pub fn generate_attr_value_for_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::recursion_guard(depth, |depth| {
            arbitrary::size_hint::and(
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
                        Self::generate_attr_value_for_type_size_hint(depth),
                    ]),
                    (1, None), // not sure how to hint for arbitrary_loop()
                    (1, None), // not sure how to hint for arbitrary_loop()
                    (1, None), // not sure how to hint for arbitrary_loop()
                ]),
            )
        })
    }

    /// get an AttrValue of the given SchemaType which conforms to this schema
    ///
    /// `max_depth`: maximum depth of the attribute value expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn generate_attr_value_for_schematype(
        &self,
        target_type: &cedar_policy_validator::SchemaType<ast::Name>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<AttrValue> {
        use cedar_policy_validator::SchemaType;
        use cedar_policy_validator::SchemaTypeVariant;
        match target_type {
            SchemaType::TypeDef { type_name } => self.generate_attr_value_for_schematype(
                self.schema
                    .schema
                    .common_types
                    .get(&type_name.clone().try_into().unwrap())
                    .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
                max_depth,
                u,
            ),
            SchemaType::Type(SchemaTypeVariant::Boolean) => {
                self.generate_attr_value_for_type(&Type::bool(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::Long) => {
                self.generate_attr_value_for_type(&Type::long(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::String) => {
                self.generate_attr_value_for_type(&Type::string(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::Set {
                element: element_ty,
            }) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(AttrValue::Set(vec![]))
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.generate_attr_value_for_schematype(
                            element_ty,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(AttrValue::Set(l))
                }
            }
            SchemaType::Type(SchemaTypeVariant::Record {
                attributes,
                additional_attributes,
            }) => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: quit here
                    Err(Error::TooDeep)
                } else {
                    let mut r = HashMap::new();
                    if *additional_attributes {
                        // maybe add some "additional" attributes not mentioned in schema
                        u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                            let (attr_name, attr_ty) = self.schema.arbitrary_attr(u)?.clone();
                            let attr_val = self.generate_attr_value_for_schematype(
                                &attr_ty,
                                max_depth - 1,
                                u,
                            )?;
                            r.insert(attr_name, attr_val);
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                    }
                    // now add all the explicitly specified required and
                    // optional attributes.
                    // Doing this second ensures that we overwrite any
                    // "additional" attributes so that they definitely have the
                    // required type, in case we got a name collision between an
                    // explicitly specified attribute and one of the
                    // "additional" ones we added.
                    for (attr_name, attr_ty) in attributes.iter() {
                        // if the attribute is optional, flip a coin to decide
                        // whether to add it. (but if we added an attribute of
                        // the same name as an "additional" attribute above,
                        // then we definitely need to add it here so that it has
                        // the correct type)
                        if attr_ty.required || r.contains_key(attr_name) || u.ratio::<u8>(1, 2)? {
                            let attr_val = self.generate_attr_value_for_schematype(
                                &attr_ty.ty,
                                max_depth - 1,
                                u,
                            )?;
                            r.insert(
                                attr_name.parse().expect(
                                    "all attribute names in the schema should be valid identifiers",
                                ),
                                attr_val,
                            );
                        }
                    }
                    Ok(AttrValue::Record(r))
                }
            }
            SchemaType::Type(SchemaTypeVariant::Entity { name }) => {
                // the only valid entity-typed attribute value is a UID literal
                let entity_type_name =
                    ast::EntityType::from(name.qualify_with(self.schema.namespace()));
                Ok(AttrValue::UIDLit(
                    self.arbitrary_uid_with_type(&entity_type_name, u)?,
                ))
            }
            SchemaType::Type(SchemaTypeVariant::Extension { .. })
                if !self.settings.enable_extensions =>
            {
                panic!("shouldn't have SchemaTypeVariant::Extension with extensions disabled")
            }
            SchemaType::Type(SchemaTypeVariant::Extension { name }) => match name.as_ref() {
                "ipaddr" => self.generate_attr_value_for_type(&Type::ipaddr(), max_depth, u),
                "decimal" => self.generate_attr_value_for_type(&Type::decimal(), max_depth, u),
                _ => unimplemented!("extension type {name:?}"),
            },
        }
    }

    /// size hint for generate_attr_value_for_schematype()
    #[allow(dead_code)]
    pub fn generate_attr_value_for_schematype_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::recursion_guard(depth, |depth| {
            arbitrary::size_hint::or_all(&[
                Self::generate_attr_value_for_type_size_hint(depth),
                (1, None), // not sure how to hint for arbitrary_loop()
                Self::arbitrary_uid_with_type_size_hint(depth),
                Self::generate_attr_value_for_type_size_hint(depth),
            ])
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
            Type::Entity => {
                // the only valid entity-typed attribute value is a UID literal
                Ok(Value::from(self.generate_uid(u)?))
            }
            Type::Set(target_element_ty) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(Value::empty_set(None))
                } else {
                    let mut l = Vec::new();
                    let target_element_ty = match target_element_ty {
                        None => {
                            if self.settings.enable_extensions {
                                u.arbitrary()?
                            } else {
                                Type::arbitrary_nonextension(u)?
                            }
                        }
                        Some(ty) => *ty.clone(),
                    };
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
            Type::Record => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty record
                    Ok(Value::empty_record(None))
                } else {
                    let mut r = HashMap::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        let (attr_name, attr_ty) = self.schema.arbitrary_attr(u)?.clone();
                        let attr_val =
                            self.generate_value_for_schematype(&attr_ty, max_depth - 1, u)?;
                        r.insert(attr_name, attr_val);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(Value::record(r, None))
                }
            }
            _ => Err(Error::ExtensionsDisabled),
        }
    }

    /// generate an arbitrary `Value` of the given `target_type`
    fn generate_value_for_schematype(
        &self,
        target_type: &cedar_policy_validator::SchemaType<ast::Name>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Value> {
        use ast::Value;
        use cedar_policy_validator::SchemaType;
        use cedar_policy_validator::SchemaTypeVariant;
        match target_type {
            SchemaType::TypeDef { type_name } => self.generate_value_for_schematype(
                self.schema
                    .schema
                    .common_types
                    .get(&type_name.clone().try_into().unwrap())
                    .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
                max_depth,
                u,
            ),
            SchemaType::Type(SchemaTypeVariant::Boolean) => {
                self.generate_value_for_type(&Type::bool(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::Long) => {
                self.generate_value_for_type(&Type::long(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::String) => {
                self.generate_value_for_type(&Type::string(), max_depth, u)
            }
            SchemaType::Type(SchemaTypeVariant::Set {
                element: element_ty,
            }) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(Value::empty_set(None))
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.generate_value_for_schematype(element_ty, max_depth - 1, u)?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(Value::set(l, None))
                }
            }
            SchemaType::Type(SchemaTypeVariant::Record {
                attributes,
                additional_attributes,
            }) => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: quit here
                    Err(Error::TooDeep)
                } else {
                    let mut r = HashMap::new();
                    if *additional_attributes {
                        // maybe add some "additional" attributes not mentioned in schema
                        u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                            let (attr_name, attr_ty) = self.schema.arbitrary_attr(u)?.clone();
                            let attr_val =
                                self.generate_value_for_schematype(&attr_ty, max_depth - 1, u)?;
                            r.insert(attr_name, attr_val);
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                    }
                    // now add all the explicitly specified required and
                    // optional attributes.
                    // Doing this second ensures that we overwrite any
                    // "additional" attributes so that they definitely have the
                    // required type, in case we got a name collision between an
                    // explicitly specified attribute and one of the
                    // "additional" ones we added.
                    for (attr_name, attr_ty) in attributes.iter() {
                        // if the attribute is optional, flip a coin to decide
                        // whether to add it. (but if we added an attribute of
                        // the same name as an "additional" attribute above,
                        // then we definitely need to add it here so that it has
                        // the correct type)
                        if attr_ty.required || r.contains_key(attr_name) || u.ratio::<u8>(1, 2)? {
                            let attr_val =
                                self.generate_value_for_schematype(&attr_ty.ty, max_depth - 1, u)?;
                            r.insert(
                                attr_name.parse().expect(
                                    "all attribute names in the schema should be valid identifiers",
                                ),
                                attr_val,
                            );
                        }
                    }
                    Ok(Value::record(r, None))
                }
            }
            SchemaType::Type(SchemaTypeVariant::Entity { name }) => {
                // the only valid entity-typed attribute value is a UID literal

                // The namespace for the entity type is the namespace of the
                // SchemaType if one is present. Otherwise, it is the schema
                // namespace if that is present. The type is unqualified if
                // neither is present.
                let entity_type_name =
                    ast::EntityType::from(name.qualify_with(self.schema.namespace()));
                let euid = self.arbitrary_uid_with_type(&entity_type_name, u)?;
                Ok(Value::from(euid))
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
                let (attr_name, _) = self.schema.arbitrary_attr(u)?;
                r.insert(attr_name.clone(), self.generate_const_expr(u)?);
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
        4 => Ok(ast::Expr::val(
            arbitrary_specified_uid(u)?,
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
            None => generate_uid_with_type(ty.clone(), &self.uid_gen_mode, u),
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

/// internal helper function, get a SchemaType representing a Record with (at
/// least) one attribute of the specified name and SchemaType.
fn record_schematype_with_attr<N>(
    attr_name: SmolStr,
    attr_type: impl Into<cedar_policy_validator::SchemaType<N>>,
) -> cedar_policy_validator::SchemaType<N> {
    cedar_policy_validator::SchemaType::Type(cedar_policy_validator::SchemaTypeVariant::Record {
        attributes: [(
            attr_name,
            cedar_policy_validator::TypeOfAttribute {
                ty: attr_type.into(),
                required: true,
            },
        )]
        .into_iter()
        .collect(),
        additional_attributes: true,
    })
}
