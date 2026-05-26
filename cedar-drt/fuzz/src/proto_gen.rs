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

//! Generators that directly produce `proto::models::*` types.
//!
//! The goal is to generate protobuf messages that are "semi-valid" — they use
//! valid Cedar identifiers and structurally sound messages, but may exercise
//! edge cases in the proto→domain conversion that the domain→proto path never
//! produces.

use cedar_policy::proto::models;
use cedar_policy_core::ast;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Pool of extension function names.
const EXT_FNS: &[(&[&str], &str)] = &[
    (&[], "ip"),
    (&[], "decimal"),
    (&[], "datetime"),
    (&[], "duration"),
];

/// Configuration and generator for proto model types.
#[derive(Debug, Clone)]
pub struct ModelGenerator {
    /// Maximum depth for expression trees.
    pub max_expr_depth: usize,
    /// Maximum depth for schema type trees.
    pub max_type_depth: usize,
    /// Maximum number of templates in a policy set.
    pub max_templates: usize,
    /// Maximum number of entity declarations in a schema.
    pub max_entity_decls: usize,
    /// Maximum number of action declarations in a schema.
    pub max_action_decls: usize,
    /// Maximum number of entities in an entity set.
    pub max_entities: usize,
    /// Maximum number of attributes/context entries per item.
    pub max_attrs: usize,
    /// Maximum namespace path length.
    pub max_namespace_depth: usize,
    /// Range for literal integer values.
    pub int_min: i64,
    pub int_max: i64,
    /// Maximum number of elements in a set/like-pattern.
    pub max_list_elems: usize,
    /// Maximum number of ancestors per entity.
    pub max_ancestors: usize,
    /// Maximum number of annotations per template.
    pub max_annotations: usize,
    /// Pool of identifiers to pick from (increases collision chance).
    /// If empty, always generates fresh identifiers.
    pub ident_pool: Vec<String>,
    /// Pool of string constants (for EIDs, string literals).
    /// If empty, always generates fresh strings.
    pub string_pool: Vec<String>,
    /// Pool of integer constants.
    /// If empty, generates from int_min..=int_max.
    pub int_pool: Vec<i64>,
}

impl Default for ModelGenerator {
    fn default() -> Self {
        Self {
            max_expr_depth: 3,
            max_type_depth: 2,
            max_templates: 4,
            max_entity_decls: 4,
            max_action_decls: 3,
            max_entities: 5,
            max_attrs: 3,
            max_namespace_depth: 2,
            int_min: -1000,
            int_max: 1000,
            max_list_elems: 4,
            max_ancestors: 3,
            max_annotations: 2,
            ident_pool: Vec::new(),
            string_pool: Vec::new(),
            int_pool: Vec::new(),
        }
    }
}

impl ModelGenerator {
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a `ModelGenerator` with pools populated from arbitrary data.
    /// This gives the fuzzer control over pool contents while ensuring
    /// value reuse across the generated model.
    pub fn arbitrary(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let ident_pool: Vec<String> = (0..u.int_in_range(2..=8)?)
            .map(|_| {
                let id: ast::UnreservedId = u.arbitrary()?;
                Ok(id.to_string())
            })
            .collect::<arbitrary::Result<Vec<_>>>()?;
        let string_pool: Vec<String> = (0..u.int_in_range(2..=6)?)
            .map(|_| u.arbitrary())
            .collect::<arbitrary::Result<Vec<_>>>()?;
        let int_pool: Vec<i64> = (0..u.int_in_range(2..=6)?)
            .map(|_| u.arbitrary())
            .collect::<arbitrary::Result<Vec<_>>>()?;
        Ok(Self {
            ident_pool,
            string_pool,
            int_pool,
            ..Self::default()
        })
    }

    /// Pick an identifier from the pool, or generate a fresh one.
    fn pick_ident<'a>(&self, u: &mut Unstructured<'a>) -> arbitrary::Result<String> {
        if !self.ident_pool.is_empty() && u.ratio(3, 4)? {
            Ok(u.choose(&self.ident_pool)?.clone())
        } else {
            let id: ast::UnreservedId = u.arbitrary()?;
            Ok(id.to_string())
        }
    }

    /// Pick a string from the pool, or generate a fresh one.
    fn pick_string<'a>(&self, u: &mut Unstructured<'a>) -> arbitrary::Result<String> {
        if !self.string_pool.is_empty() && u.ratio(3, 4)? {
            Ok(u.choose(&self.string_pool)?.clone())
        } else {
            u.arbitrary()
        }
    }

    /// Pick an integer from the pool, or generate one in range.
    fn pick_int<'a>(&self, u: &mut Unstructured<'a>) -> arbitrary::Result<i64> {
        if !self.int_pool.is_empty() && u.ratio(3, 4)? {
            Ok(*u.choose(&self.int_pool)?)
        } else {
            u.int_in_range(self.int_min..=self.int_max)
        }
    }

    pub fn arbitrary_model_name<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::Name> {
        let id = self.pick_ident(u)?;
        let path_len: usize = u.int_in_range(0..=self.max_namespace_depth)?;
        let mut path = Vec::with_capacity(path_len);
        for _ in 0..path_len {
            path.push(self.pick_ident(u)?);
        }
        Ok(models::Name { id, path })
    }

    pub fn arbitrary_model_entity_uid<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::EntityUid> {
        let ty = Some(self.arbitrary_model_name(u)?);
        let eid = self.pick_string(u)?;
        Ok(models::EntityUid { ty, eid })
    }

    pub fn arbitrary_model_expr<'a>(
        &self,
        u: &mut Unstructured<'a>,
        max_depth: usize,
    ) -> arbitrary::Result<models::Expr> {
        use models::expr;

        if max_depth == 0 {
            let choice: u8 = u.int_in_range(0..=4)?;
            let expr_kind = match choice {
                0 => expr::ExprKind::Lit(expr::Literal {
                    lit: Some(expr::literal::Lit::B(u.arbitrary()?)),
                }),
                1 => expr::ExprKind::Lit(expr::Literal {
                    lit: Some(expr::literal::Lit::I(self.pick_int(u)?)),
                }),
                2 => expr::ExprKind::Lit(expr::Literal {
                    lit: Some(expr::literal::Lit::S(self.pick_string(u)?)),
                }),
                3 => expr::ExprKind::Lit(expr::Literal {
                    lit: Some(expr::literal::Lit::Euid(
                        self.arbitrary_model_entity_uid(u)?,
                    )),
                }),
                _ => expr::ExprKind::Var(u.int_in_range(0..=3)?),
            };
            return Ok(models::Expr {
                expr_kind: Some(expr_kind),
            });
        }

        let choice: u8 = u.int_in_range(0..=14)?;
        let d = max_depth - 1;
        let expr_kind = match choice {
            0 => {
                let lit_choice: u8 = u.int_in_range(0..=3)?;
                let lit = match lit_choice {
                    0 => expr::literal::Lit::B(u.arbitrary()?),
                    1 => expr::literal::Lit::I(self.pick_int(u)?),
                    2 => expr::literal::Lit::S(self.pick_string(u)?),
                    _ => expr::literal::Lit::Euid(self.arbitrary_model_entity_uid(u)?),
                };
                expr::ExprKind::Lit(expr::Literal { lit: Some(lit) })
            }
            1 => expr::ExprKind::Var(u.int_in_range(0..=3)?),
            2 => expr::ExprKind::Slot(u.int_in_range(0..=1)?),
            3 => expr::ExprKind::If(Box::new(expr::If {
                test_expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                then_expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                else_expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
            })),
            4 => expr::ExprKind::And(Box::new(expr::And {
                left: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                right: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
            })),
            5 => expr::ExprKind::Or(Box::new(expr::Or {
                left: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                right: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
            })),
            6 => expr::ExprKind::UApp(Box::new(expr::UnaryApp {
                op: u.int_in_range(0..=2)?,
                expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
            })),
            7 => expr::ExprKind::BApp(Box::new(expr::BinaryApp {
                op: u.int_in_range(0..=11)?,
                left: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                right: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
            })),
            8 => {
                let (path, id) = u.choose(EXT_FNS)?;
                let num_args: usize = u.int_in_range(1..=self.max_list_elems)?;
                let args = (0..num_args)
                    .map(|_| self.arbitrary_model_expr(u, d))
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                expr::ExprKind::ExtApp(expr::ExtensionFunctionApp {
                    fn_name: Some(models::Name {
                        id: id.to_string(),
                        path: path.iter().map(|s| s.to_string()).collect(),
                    }),
                    args,
                })
            }
            9 => expr::ExprKind::GetAttr(Box::new(expr::GetAttr {
                expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                attr: self.pick_ident(u)?,
            })),
            10 => expr::ExprKind::HasAttr(Box::new(expr::HasAttr {
                expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                attr: self.pick_ident(u)?,
            })),
            11 => {
                let num_elems: usize = u.int_in_range(0..=self.max_list_elems)?;
                let pattern = (0..num_elems)
                    .map(|_| {
                        let is_wildcard: bool = u.arbitrary()?;
                        let data = if is_wildcard {
                            Some(expr::like::pattern_elem::Data::Wildcard(0))
                        } else {
                            Some(expr::like::pattern_elem::Data::C(self.pick_string(u)?))
                        };
                        Ok(expr::like::PatternElem { data })
                    })
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                expr::ExprKind::Like(Box::new(expr::Like {
                    expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                    pattern,
                }))
            }
            12 => expr::ExprKind::Is(Box::new(expr::Is {
                expr: Some(Box::new(self.arbitrary_model_expr(u, d)?)),
                entity_type: Some(self.arbitrary_model_name(u)?),
            })),
            13 => {
                let num_elems: usize = u.int_in_range(0..=self.max_list_elems)?;
                let elements = (0..num_elems)
                    .map(|_| self.arbitrary_model_expr(u, d))
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                expr::ExprKind::Set(expr::Set { elements })
            }
            _ => {
                let num_items: usize = u.int_in_range(0..=self.max_attrs)?;
                let items = (0..num_items)
                    .map(|_| Ok((self.pick_ident(u)?, self.arbitrary_model_expr(u, d)?)))
                    .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
                expr::ExprKind::Record(expr::Record { items })
            }
        };
        Ok(models::Expr {
            expr_kind: Some(expr_kind),
        })
    }

    pub fn arbitrary_model_entity_reference<'a>(
        &self,
        u: &mut Unstructured<'a>,
        allow_slot: bool,
    ) -> arbitrary::Result<models::EntityReference> {
        use models::entity_reference;
        let data = if allow_slot && u.ratio(1, 4)? {
            Some(entity_reference::Data::Slot(0))
        } else {
            Some(entity_reference::Data::Euid(
                self.arbitrary_model_entity_uid(u)?,
            ))
        };
        Ok(models::EntityReference { data })
    }

    pub fn arbitrary_model_principal_or_resource_constraint<'a>(
        &self,
        u: &mut Unstructured<'a>,
        allow_slot: bool,
    ) -> arbitrary::Result<models::PrincipalOrResourceConstraint> {
        use models::principal_or_resource_constraint::*;
        let choice: u8 = u.int_in_range(0..=4)?;
        let data = match choice {
            0 => Data::Any(0),
            1 => Data::In(InMessage {
                er: Some(self.arbitrary_model_entity_reference(u, allow_slot)?),
            }),
            2 => Data::Eq(EqMessage {
                er: Some(self.arbitrary_model_entity_reference(u, allow_slot)?),
            }),
            3 => Data::Is(IsMessage {
                entity_type: Some(self.arbitrary_model_name(u)?),
            }),
            _ => Data::IsIn(IsInMessage {
                er: Some(self.arbitrary_model_entity_reference(u, allow_slot)?),
                entity_type: Some(self.arbitrary_model_name(u)?),
            }),
        };
        Ok(models::PrincipalOrResourceConstraint { data: Some(data) })
    }

    pub fn arbitrary_model_action_constraint<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::ActionConstraint> {
        use models::action_constraint::*;
        let choice: u8 = u.int_in_range(0..=2)?;
        let data = match choice {
            0 => Data::Any(0),
            1 => {
                let num: usize = u.int_in_range(1..=self.max_list_elems)?;
                let euids = (0..num)
                    .map(|_| self.arbitrary_model_entity_uid(u))
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                Data::In(InMessage { euids })
            }
            _ => Data::Eq(EqMessage {
                euid: Some(self.arbitrary_model_entity_uid(u)?),
            }),
        };
        Ok(models::ActionConstraint { data: Some(data) })
    }

    pub fn arbitrary_model_template_body<'a>(
        &self,
        u: &mut Unstructured<'a>,
        allow_slots: bool,
    ) -> arbitrary::Result<models::TemplateBody> {
        let id = format!("policy{}", u.int_in_range(0..=99)?);
        let num_annotations: usize = u.int_in_range(0..=self.max_annotations)?;
        let annotations = (0..num_annotations)
            .map(|_| Ok((self.pick_ident(u)?, self.pick_ident(u)?)))
            .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
        let effect = u.int_in_range(0..=1)?;
        let principal_constraint =
            Some(self.arbitrary_model_principal_or_resource_constraint(u, allow_slots)?);
        let action_constraint = Some(self.arbitrary_model_action_constraint(u)?);
        let resource_constraint =
            Some(self.arbitrary_model_principal_or_resource_constraint(u, allow_slots)?);
        let non_scope_constraints = Some(self.arbitrary_model_expr(u, self.max_expr_depth)?);

        Ok(models::TemplateBody {
            id,
            annotations,
            effect,
            principal_constraint,
            action_constraint,
            resource_constraint,
            non_scope_constraints,
        })
    }

    pub fn arbitrary_model_policy_link<'a>(
        &self,
        u: &mut Unstructured<'a>,
        template_id: &str,
        is_template_link: bool,
    ) -> arbitrary::Result<models::Policy> {
        let link_id = if is_template_link {
            Some(format!("link{}", u.int_in_range(0..=99)?))
        } else {
            None
        };
        Ok(models::Policy {
            template_id: template_id.to_string(),
            link_id,
            is_template_link,
            principal_euid: Some(self.arbitrary_model_entity_uid(u)?),
            resource_euid: Some(self.arbitrary_model_entity_uid(u)?),
        })
    }

    pub fn arbitrary_model_policy_set<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::PolicySet> {
        let num_templates: usize = u.int_in_range(1..=self.max_templates)?;
        let mut templates = Vec::with_capacity(num_templates);
        let mut links = Vec::new();

        for _ in 0..num_templates {
            let has_slots: bool = u.arbitrary()?;
            let template = self.arbitrary_model_template_body(u, has_slots)?;
            let tid = template.id.clone();
            templates.push(template);

            if has_slots {
                links.push(self.arbitrary_model_policy_link(u, &tid, true)?);
            } else {
                links.push(self.arbitrary_model_policy_link(u, &tid, false)?);
            }
        }

        Ok(models::PolicySet { templates, links })
    }

    pub fn arbitrary_model_request<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::Request> {
        let num_context: usize = u.int_in_range(0..=self.max_attrs)?;
        let context = (0..num_context)
            .map(|_| {
                Ok((
                    self.pick_ident(u)?,
                    self.arbitrary_model_expr(u, self.max_expr_depth)?,
                ))
            })
            .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
        Ok(models::Request {
            principal: Some(self.arbitrary_model_entity_uid(u)?),
            action: Some(self.arbitrary_model_entity_uid(u)?),
            resource: Some(self.arbitrary_model_entity_uid(u)?),
            context,
        })
    }

    pub fn arbitrary_model_entity<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::Entity> {
        let num_attrs: usize = u.int_in_range(0..=self.max_attrs)?;
        let attrs = (0..num_attrs)
            .map(|_| Ok((self.pick_ident(u)?, self.arbitrary_model_expr(u, 1)?)))
            .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
        let num_ancestors: usize = u.int_in_range(0..=self.max_ancestors)?;
        let ancestors = (0..num_ancestors)
            .map(|_| self.arbitrary_model_entity_uid(u))
            .collect::<arbitrary::Result<Vec<_>>>()?;
        let num_tags: usize = u.int_in_range(0..=self.max_attrs)?;
        let tags = (0..num_tags)
            .map(|_| Ok((self.pick_ident(u)?, self.arbitrary_model_expr(u, 1)?)))
            .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
        Ok(models::Entity {
            uid: Some(self.arbitrary_model_entity_uid(u)?),
            attrs,
            ancestors,
            tags,
        })
    }

    pub fn arbitrary_model_entities<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::Entities> {
        let num: usize = u.int_in_range(0..=self.max_entities)?;
        let entities = (0..num)
            .map(|_| self.arbitrary_model_entity(u))
            .collect::<arbitrary::Result<Vec<_>>>()?;
        Ok(models::Entities { entities })
    }

    pub fn arbitrary_model_type<'a>(
        &self,
        u: &mut Unstructured<'a>,
        max_depth: usize,
    ) -> arbitrary::Result<models::Type> {
        use models::r#type;
        if max_depth == 0 {
            let prim = u.int_in_range(0..=2)?;
            return Ok(models::Type {
                data: Some(r#type::Data::Prim(prim)),
            });
        }
        let choice: u8 = u.int_in_range(0..=4)?;
        let data = match choice {
            0 => r#type::Data::Prim(u.int_in_range(0..=2)?),
            1 => r#type::Data::SetElem(Box::new(self.arbitrary_model_type(u, max_depth - 1)?)),
            2 => r#type::Data::Entity(self.arbitrary_model_name(u)?),
            3 => {
                let num_attrs: usize = u.int_in_range(0..=self.max_attrs)?;
                let attrs = (0..num_attrs)
                    .map(|_| {
                        Ok((
                            self.pick_ident(u)?,
                            models::AttributeType {
                                attr_type: Some(self.arbitrary_model_type(u, max_depth - 1)?),
                                is_required: u.arbitrary()?,
                            },
                        ))
                    })
                    .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
                r#type::Data::Record(r#type::Record { attrs })
            }
            _ => r#type::Data::Ext(self.arbitrary_model_name(u)?),
        };
        Ok(models::Type { data: Some(data) })
    }

    pub fn arbitrary_model_schema<'a>(
        &self,
        u: &mut Unstructured<'a>,
    ) -> arbitrary::Result<models::Schema> {
        let num_entity_decls: usize = u.int_in_range(1..=self.max_entity_decls)?;
        let entity_decls = (0..num_entity_decls)
            .map(|_| {
                let num_attrs: usize = u.int_in_range(0..=self.max_attrs)?;
                let attributes = (0..num_attrs)
                    .map(|_| {
                        Ok((
                            self.pick_ident(u)?,
                            models::AttributeType {
                                attr_type: Some(self.arbitrary_model_type(u, self.max_type_depth)?),
                                is_required: u.arbitrary()?,
                            },
                        ))
                    })
                    .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
                let num_descendants: usize = u.int_in_range(0..=2)?;
                let descendants = (0..num_descendants)
                    .map(|_| self.arbitrary_model_name(u))
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                let tags = if u.ratio(1, 3)? {
                    Some(self.arbitrary_model_type(u, 1)?)
                } else {
                    None
                };
                Ok(models::EntityDecl {
                    name: Some(self.arbitrary_model_name(u)?),
                    descendants,
                    attributes,
                    tags,
                    enum_choices: vec![],
                })
            })
            .collect::<arbitrary::Result<Vec<_>>>()?;

        let num_action_decls: usize = u.int_in_range(1..=self.max_action_decls)?;
        let action_decls = (0..num_action_decls)
            .map(|_| {
                let num_context: usize = u.int_in_range(0..=2)?;
                let context = (0..num_context)
                    .map(|_| {
                        Ok((
                            self.pick_ident(u)?,
                            models::AttributeType {
                                attr_type: Some(self.arbitrary_model_type(u, self.max_type_depth)?),
                                is_required: u.arbitrary()?,
                            },
                        ))
                    })
                    .collect::<arbitrary::Result<std::collections::HashMap<_, _>>>()?;
                let num_principal_types: usize = u.int_in_range(1..=2)?;
                let principal_types = (0..num_principal_types)
                    .map(|_| self.arbitrary_model_name(u))
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                let num_resource_types: usize = u.int_in_range(1..=2)?;
                let resource_types = (0..num_resource_types)
                    .map(|_| self.arbitrary_model_name(u))
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                let num_descendants: usize = u.int_in_range(0..=2)?;
                let descendants = (0..num_descendants)
                    .map(|_| self.arbitrary_model_entity_uid(u))
                    .collect::<arbitrary::Result<Vec<_>>>()?;
                Ok(models::ActionDecl {
                    name: Some(self.arbitrary_model_entity_uid(u)?),
                    descendants,
                    context,
                    principal_types,
                    resource_types,
                })
            })
            .collect::<arbitrary::Result<Vec<_>>>()?;

        Ok(models::Schema {
            entity_decls,
            action_decls,
        })
    }
}

// --- Wrapper types for use as fuzz target inputs ---

/// Fuzz input: a protobuf PolicySet model.
#[derive(Debug, Clone)]
pub struct ProtoPolicySetInput {
    pub policy_set: models::PolicySet,
}

impl<'a> Arbitrary<'a> for ProtoPolicySetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let g = ModelGenerator::arbitrary(u)?;
        Ok(Self {
            policy_set: g.arbitrary_model_policy_set(u)?,
        })
    }
}

/// Fuzz input: a protobuf Schema model.
#[derive(Debug, Clone)]
pub struct ProtoSchemaInput {
    pub schema: models::Schema,
}

impl<'a> Arbitrary<'a> for ProtoSchemaInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let g = ModelGenerator::arbitrary(u)?;
        Ok(Self {
            schema: g.arbitrary_model_schema(u)?,
        })
    }
}

/// Fuzz input: a protobuf Entity model.
#[derive(Debug, Clone)]
pub struct ProtoEntityInput {
    pub entity: models::Entity,
}

impl<'a> Arbitrary<'a> for ProtoEntityInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let g = ModelGenerator::arbitrary(u)?;
        Ok(Self {
            entity: g.arbitrary_model_entity(u)?,
        })
    }
}
