/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
    ABACPolicy, ABACRequest, AvailableExtensionFunctions, ConstantPool, Type, UnknownPool,
};
use crate::collections::{HashMap, HashSet};
use crate::err::{while_doing, Error, Result};
use crate::expr::ExprGenerator;
use crate::hierarchy::{
    EntityUIDGenMode, Hierarchy, HierarchyGenerator, HierarchyGeneratorMode, NumEntities,
};
use crate::policy::{ActionConstraint, GeneratedPolicy, PrincipalOrResourceConstraint};
use crate::request::Request;
use crate::settings::ABACSettings;
use crate::size_hint_utils::{size_hint_for_choose, size_hint_for_range, size_hint_for_ratio};
use crate::{accum, gen, gen_inner, uniform};
use arbitrary::{self, Arbitrary, Unstructured};
use cedar_policy_core::ast::{self, Effect, Id, Name, PolicyID};
use cedar_policy_core::extensions::Extensions;
use cedar_policy_validator::{
    ActionType, ApplySpec, AttributesOrContext, EntityType, SchemaError, SchemaFragment,
    SchemaType, SchemaTypeVariant, TypeOfAttribute, ValidatorSchema,
};
use smol_str::{SmolStr, ToSmolStr};
use std::collections::BTreeMap;

/// Contains the schema, but also pools of constants etc
#[derive(Debug, Clone)]
pub struct Schema {
    /// actual underlying schema
    pub schema: cedar_policy_validator::NamespaceDefinition,
    /// Namespace for the schema, as an `ast::Name`
    pub namespace: Option<ast::Name>,
    /// settings
    pub settings: ABACSettings,
    /// constant pool
    pub constant_pool: ConstantPool,
    /// unknown pool
    pub unknown_pool: UnknownPool,
    /// data on available extension functions
    ext_funcs: AvailableExtensionFunctions,
    /// list of all entity types that are declared in the schema. Note that this
    /// may contain an entity type that is not in `principal_types` or
    /// `resource_types`.
    pub entity_types: Vec<ast::Name>,
    /// list of entity types that occur as a valid principal for at least one
    /// action in the `schema`
    pub principal_types: Vec<ast::Name>,
    /// list of Eids that exist as a non-`None` actions name for an action in
    /// the schema.
    pub actions_eids: Vec<ast::Eid>,
    /// list of entity types that occur as a valid resource for at least one
    /// action in the `schema`
    pub resource_types: Vec<ast::Name>,
    /// list of (attribute, type) pairs that occur in the `schema`
    attributes: Vec<(SmolStr, cedar_policy_validator::SchemaType)>,
    /// map from type to (entity type, attribute name) pairs indicating
    /// attributes in the `schema` that have that type.
    /// note that we can't make a similar map for SchemaType because it isn't
    /// Hash or Ord
    attributes_by_type: HashMap<Type, Vec<(ast::Name, SmolStr)>>,
}

/// internal helper function, basically `impl Arbitrary for AttributesOrContext`
fn arbitrary_attrspec(
    settings: &ABACSettings,
    entity_types: &[ast::Name],
    u: &mut Unstructured<'_>,
) -> Result<AttributesOrContext> {
    let attr_names: Vec<ast::Id> = u
        .arbitrary()
        .map_err(|e| while_doing("generating attribute names for an attrspec".into(), e))?;
    Ok(AttributesOrContext(cedar_policy_validator::SchemaType::Type(
        cedar_policy_validator::SchemaTypeVariant::Record {
            attributes: attr_names
                .into_iter()
                .map(|attr| {
                    let mut ty = arbitrary_typeofattribute_with_bounded_depth(
                        settings,
                        entity_types,
                        settings.max_depth,
                        u,
                    )?;
                    if !settings.enable_extensions {
                        // can't have extension types. regenerate until morale improves
                        while ty.ty.is_extension().expect("DRT does not generate schema type using type defs, so `is_extension` should be `Some`") {
                            ty = arbitrary_typeofattribute_with_bounded_depth(
                                settings,
                                entity_types,
                                settings.max_depth,
                                u,
                            )?;
                        }
                    }
                    Ok((AsRef::<str>::as_ref(&attr).into(), ty))
                })
                .collect::<Result<_>>()?,
            additional_attributes: if settings.enable_additional_attributes {
                u.arbitrary()?
            } else {
                false
            },
        },
    )))
}
/// size hint for arbitrary_attrspec
fn arbitrary_attrspec_size_hint(depth: usize) -> (usize, Option<usize>) {
    arbitrary::size_hint::recursion_guard(depth, |depth| {
        arbitrary::size_hint::and_all(&[
            <Vec<ast::Id> as Arbitrary>::size_hint(depth),
            arbitrary_typeofattribute_size_hint(depth),
            <bool as Arbitrary>::size_hint(depth),
        ])
    })
}

/// internal helper function, an alternative to the `Arbitrary` impl for
/// `TypeOfAttribute` that implements a bounded maximum depth.
/// For instance, if `max_depth` is 3, then Set types (or Record types)
/// won't be nested more than 3 deep.
///
/// For unbounded depth, use the actual `Arbitrary` instance which is
/// auto-derived.
///
/// Note that the actual `Arbitrary` instance doesn't respect
/// settings.enable_additional_attributes; it always behaves as if that setting
/// is `true` (ie, it may generate `additional_attributes` as either `true` or
/// `false`).
fn arbitrary_typeofattribute_with_bounded_depth(
    settings: &ABACSettings,
    entity_types: &[ast::Name],
    max_depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<TypeOfAttribute> {
    Ok(TypeOfAttribute {
        ty: arbitrary_schematype_with_bounded_depth(settings, entity_types, max_depth, u)?,
        required: u.arbitrary()?,
    })
}
/// size hint for arbitrary_typeofattribute_with_bounded_depth
fn arbitrary_typeofattribute_size_hint(depth: usize) -> (usize, Option<usize>) {
    arbitrary::size_hint::and(
        arbitrary_schematype_size_hint(depth),
        <bool as Arbitrary>::size_hint(depth),
    )
}

/// internal helper function, an alternative to the `Arbitrary` impl for
/// `SchemaType` that implements a bounded maximum depth.
/// For instance, if `max_depth` is 3, then Set types (or Record types)
/// won't be nested more than 3 deep.
///
/// For unbounded depth, use the actual `Arbitrary` instance which is
/// auto-derived.
///
/// Note that the actual `Arbitrary` instance doesn't respect
/// settings.enable_additional_attributes; it always behaves as if that setting
/// is `true` (ie, it may generate `additional_attributes` as either `true` or
/// `false`).
pub fn arbitrary_schematype_with_bounded_depth(
    settings: &ABACSettings,
    entity_types: &[ast::Name],
    max_depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<cedar_policy_validator::SchemaType> {
    Ok(SchemaType::Type(uniform!(
        u,
        SchemaTypeVariant::String,
        SchemaTypeVariant::Long,
        SchemaTypeVariant::Boolean,
        {
            if max_depth == 0 {
                // can't recurse; we arbitrarily choose Set<Long> in this case
                SchemaTypeVariant::Set {
                    element: Box::new(SchemaType::Type(SchemaTypeVariant::Long)),
                }
            } else {
                SchemaTypeVariant::Set {
                    element: Box::new(arbitrary_schematype_with_bounded_depth(
                        settings,
                        entity_types,
                        max_depth - 1,
                        u,
                    )?),
                }
            }
        },
        {
            if max_depth == 0 {
                // can't recurse; use empty-record
                SchemaTypeVariant::Record {
                    attributes: BTreeMap::new(),
                    additional_attributes: if settings.enable_additional_attributes {
                        u.arbitrary()?
                    } else {
                        false
                    },
                }
            } else {
                SchemaTypeVariant::Record {
                    attributes: {
                        let attr_names: HashSet<String> = u
                            .arbitrary()
                            .map_err(|e| while_doing("generating attribute names".into(), e))?;
                        attr_names
                            .into_iter()
                            .map(|attr_name| {
                                Ok((
                                    attr_name.into(),
                                    arbitrary_typeofattribute_with_bounded_depth(
                                        settings,
                                        entity_types,
                                        max_depth - 1,
                                        u,
                                    )?,
                                ))
                            })
                            .collect::<Result<BTreeMap<_, _>>>()?
                    },
                    additional_attributes: if settings.enable_additional_attributes {
                        u.arbitrary()?
                    } else {
                        false
                    },
                }
            }
        },
        entity_type_name_to_schema_type_variant(u.choose(entity_types)?),
        SchemaTypeVariant::Extension {
            name: "ipaddr".parse().unwrap(),
        },
        SchemaTypeVariant::Extension {
            name: "decimal".parse().unwrap(),
        }
    )))
}

/// Convert a `Name` representing an entity type into the corresponding
/// `SchemaTypeVariant` for an entity reference with that entity type.
pub fn entity_type_name_to_schema_type_variant(
    name: &ast::Name,
) -> cedar_policy_validator::SchemaTypeVariant {
    cedar_policy_validator::SchemaTypeVariant::Entity { name: name.clone() }
}

/// Convert a `Name` representing an entity type into the corresponding
/// SchemaType for an entity reference with that entity type.
pub fn entity_type_name_to_schema_type(name: &ast::Name) -> cedar_policy_validator::SchemaType {
    SchemaType::Type(entity_type_name_to_schema_type_variant(name))
}

/// size hint for arbitrary_schematype_with_bounded_depth
fn arbitrary_schematype_size_hint(depth: usize) -> (usize, Option<usize>) {
    // assume it's similar to the unbounded-depth version
    <cedar_policy_validator::SchemaType as Arbitrary>::size_hint(depth)
}

/// internal helper function, get the EntityUID corresponding to the given action
pub fn uid_for_action_name(namespace: Option<ast::Name>, action_name: ast::Eid) -> ast::EntityUID {
    let entity_type =
        build_qualified_entity_type_name(namespace, "Action".parse().expect("valid id"));
    ast::EntityUID::from_components(entity_type, action_name, None)
}

/// internal helper function, convert a SchemaType to a Type (loses some
/// information)
fn schematype_to_type(
    schema: &cedar_policy_validator::NamespaceDefinition,
    schematy: &cedar_policy_validator::SchemaType,
) -> Type {
    match schematy {
        SchemaType::TypeDef { type_name } => schematype_to_type(
            schema,
            schema
                .common_types
                .get(&type_name.clone().try_into().unwrap())
                .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
        ),
        SchemaType::Type(ty) => match ty {
            SchemaTypeVariant::Boolean => Type::bool(),
            SchemaTypeVariant::Long => Type::long(),
            SchemaTypeVariant::String => Type::string(),
            SchemaTypeVariant::Set { element } => Type::set_of(schematype_to_type(schema, element)),
            SchemaTypeVariant::Record { .. } => Type::record(),
            SchemaTypeVariant::Entity { .. } => Type::entity(),
            SchemaTypeVariant::Extension { name } => match name.as_ref() {
                "ipaddr" => Type::ipaddr(),
                "decimal" => Type::decimal(),
                _ => panic!("unrecognized extension type: {name:?}"),
            },
        },
    }
}

/// Get an arbitrary namespace for a schema. The namespace may be absent.
fn arbitrary_namespace(u: &mut Unstructured<'_>) -> Result<Option<ast::Name>> {
    u.arbitrary()
        .map_err(|e| while_doing("generating namespace".into(), e))
}

/// Given an (optional) namespace and a type base name, build a fully
/// qualified `Name`.
pub(crate) fn build_qualified_entity_type_name(
    namespace: Option<ast::Name>,
    name: ast::Name,
) -> ast::Name {
    match build_qualified_entity_type(namespace, Some(name)) {
        ast::EntityType::Specified(type_name) => type_name,
        ast::EntityType::Unspecified => {
            panic!("Should not have built an unspecified type from `Some(name)`.")
        }
    }
}

/// Information about attributes from the schema
pub(crate) struct Attributes<'a> {
    /// the actual attributes
    pub attrs: &'a BTreeMap<SmolStr, TypeOfAttribute>,
    /// whether `additional_attributes` is set
    pub additional_attrs: bool,
}

/// Given an `AttributesOrContext`, get the actual attributes map from it, and whether it has `additional_attributes` set
pub(crate) fn attrs_from_attrs_or_context<'a>(
    schema: &'a cedar_policy_validator::NamespaceDefinition,
    attrsorctx: &'a AttributesOrContext,
) -> Attributes<'a> {
    match &attrsorctx.0 {
        SchemaType::TypeDef { type_name } => match schema.common_types.get(&type_name.clone().try_into().unwrap()).unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")) {
            SchemaType::TypeDef { .. } => panic!("common type `{type_name}` refers to another common type, which is not allowed as of this writing?"),
            SchemaType::Type(SchemaTypeVariant::Record { attributes, additional_attributes }) => Attributes { attrs: attributes, additional_attrs: *additional_attributes },
        SchemaType::Type(ty) => panic!("expected attributes or context to be a record, got {ty:?}"),
        }
        SchemaType::Type(SchemaTypeVariant::Record { attributes, additional_attributes }) => Attributes { attrs: attributes, additional_attrs: *additional_attributes },
        SchemaType::Type(ty) => panic!("expected attributes or context to be a record, got {ty:?}"),
    }
}

/// Given an (optional) namespace and a type base name, build a fully qualified
/// `EntityType`.
///
/// If `basename` is `None`, then this builds an unspecified entity type. Use
/// `build_qualified_entity_type_name` if `basename` is not `None`.
fn build_qualified_entity_type(
    namespace: Option<ast::Name>,
    basename: Option<ast::Name>,
) -> ast::EntityType {
    match basename {
        Some(basename) => {
            ast::EntityType::Specified(basename.prefix_namespace_if_unqualified(namespace))
        }
        None => ast::EntityType::Unspecified,
    }
}

/// Given a `SchemaType`, return all (attribute, type) pairs that occur inside it
fn attrs_in_schematype(
    schema: &cedar_policy_validator::NamespaceDefinition,
    schematype: &cedar_policy_validator::SchemaType,
) -> Box<dyn Iterator<Item = (SmolStr, cedar_policy_validator::SchemaType)>> {
    match schematype {
        cedar_policy_validator::SchemaType::Type(variant) => match variant {
            SchemaTypeVariant::Boolean => Box::new(std::iter::empty()),
            SchemaTypeVariant::Long => Box::new(std::iter::empty()),
            SchemaTypeVariant::String => Box::new(std::iter::empty()),
            SchemaTypeVariant::Entity { .. } => Box::new(std::iter::empty()),
            SchemaTypeVariant::Extension { .. } => Box::new(std::iter::empty()),
            SchemaTypeVariant::Set { element } => attrs_in_schematype(schema, element),
            SchemaTypeVariant::Record { attributes, .. } => {
                let toplevel = attributes
                    .iter()
                    .map(|(k, v)| (k.clone(), v.ty.clone()))
                    .collect::<Vec<_>>();
                let recursed = toplevel
                    .iter()
                    .flat_map(|(_, v)| attrs_in_schematype(schema, v))
                    .collect::<Vec<_>>();
                Box::new(toplevel.into_iter().chain(recursed))
            }
        },
        cedar_policy_validator::SchemaType::TypeDef { type_name } => attrs_in_schematype(
            schema,
            schema
                .common_types
                .get(&type_name.clone().try_into().unwrap())
                .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
        ),
    }
}

/// Build `attributes_by_type` from other components of `Schema`
fn build_attributes_by_type<'a>(
    schema: &cedar_policy_validator::NamespaceDefinition,
    entity_types: impl IntoIterator<Item = (&'a Id, &'a cedar_policy_validator::EntityType)>,
    namespace: Option<&ast::Name>,
) -> HashMap<Type, Vec<(ast::Name, SmolStr)>> {
    let triples = entity_types
        .into_iter()
        .map(|(name, et)| {
            (
                build_qualified_entity_type_name(namespace.cloned(), name.clone().into()),
                attrs_from_attrs_or_context(schema, &et.shape),
            )
        })
        .flat_map(|(tyname, attributes)| {
            attributes.attrs.iter().map(move |(attr_name, ty)| {
                (
                    schematype_to_type(schema, &ty.ty),
                    (tyname.clone(), attr_name.clone()),
                )
            })
        });
    let mut hm: HashMap<Type, Vec<(ast::Name, SmolStr)>> = HashMap::new();
    for (ty, pair) in triples {
        hm.entry(ty).or_default().push(pair);
    }
    hm
}

// Common type bindings
#[derive(Debug)]
struct Bindings {
    // Bindings from `SchemaType` to a list of `Id`
    // The `ids` field ensures that `Id`s are unique
    // Note that `SchemaType`s should not contain any common type references
    bindings: BTreeMap<SchemaType, Vec<Id>>,
    // The set of `Id`s used in the bindings
    ids: HashSet<SmolStr>,
}

impl Bindings {
    fn new() -> Self {
        Self {
            bindings: BTreeMap::new(),
            ids: HashSet::new(),
        }
    }

    // Add a `SchemaType` and `Id` binding
    // Note that this function always succeeds even if the `Id` already exists
    // Under that situation, we create a new `Id` based on the existing `Id`
    fn add_binding(&mut self, binding: (SchemaType, Id)) {
        let (ty, id) = binding;
        // create a new id when the provided id has been used
        let new_id = if self.ids.contains(id.as_ref()) {
            let mut new_id = id.to_string();
            while self.ids.contains(new_id.as_str()) {
                new_id.push('_');
            }
            new_id.parse().unwrap()
        } else {
            id
        };

        self.ids.insert(new_id.clone().to_smolstr());
        if let Some(binding_for_ty) = self.bindings.get_mut(&ty) {
            binding_for_ty.push(new_id);
        } else {
            self.bindings.insert(ty, vec![new_id]);
        }
    }

    // Replace types with common type references
    // We only replace smaller types in composite types like sets and records
    // to avoid circularity
    // This function is a no-op for other types
    fn rewrite_type(&self, u: &mut Unstructured<'_>, ty: &SchemaType) -> Result<SchemaType> {
        match ty {
            SchemaType::TypeDef { .. } => unreachable!("common type references shouldn't be here"),
            SchemaType::Type(SchemaTypeVariant::Set { element }) => {
                Ok(SchemaType::Type(SchemaTypeVariant::Set {
                    element: Box::new(if let Some(ids) = self.bindings.get(element) {
                        SchemaType::TypeDef {
                            type_name: Name::unqualified_name(u.choose(ids)?.clone()),
                        }
                    } else {
                        self.rewrite_type(u, element)?
                    }),
                }))
            }
            SchemaType::Type(SchemaTypeVariant::Record {
                attributes,
                additional_attributes,
            }) => Ok(SchemaType::Type(SchemaTypeVariant::Record {
                attributes: BTreeMap::from_iter(
                    attributes
                        .iter()
                        .map(|(attr, attr_ty)| {
                            Ok((
                                attr.to_owned(),
                                TypeOfAttribute {
                                    ty: self.rewrite_type(u, &attr_ty.ty)?,
                                    required: attr_ty.required.to_owned(),
                                },
                            ))
                        })
                        .collect::<Result<Vec<_>>>()?,
                ),
                additional_attributes: additional_attributes.to_owned(),
            })),
            _ => Ok(ty.clone()),
        }
    }

    // Replace attribute types in an entity type with common types
    fn rewrite_entity_type(&self, u: &mut Unstructured<'_>, et: &EntityType) -> Result<EntityType> {
        let ty = &et.shape.0;
        Ok(EntityType {
            member_of_types: et.member_of_types.clone(),
            shape: AttributesOrContext(self.rewrite_record_type(u, ty)?),
        })
    }

    // Replace attribute types in a record type with common types
    fn rewrite_record_type(&self, u: &mut Unstructured<'_>, ty: &SchemaType) -> Result<SchemaType> {
        let new_ty = if let Some(ids) = self.bindings.get(ty) {
            SchemaType::TypeDef {
                type_name: Name::unqualified_name(u.choose(ids)?.clone()),
            }
        } else {
            self.rewrite_type(u, ty)?
        };
        Ok(new_ty)
    }

    // Generate common types based on the bindings
    // For a binding `ty` to `[id_1, id_2, ..., id_n]`
    // We create common types as follows
    // ```
    // type id_1 = id_2;
    // type id_2 = id_3;
    // ...
    // type id_n = rewrite_type(ty)
    // ```
    fn to_common_types(&self, u: &mut Unstructured<'_>) -> Result<HashMap<Id, SchemaType>> {
        let mut common_types = HashMap::new();
        for (ty, ids) in &self.bindings {
            if ids.len() == 1 {
                common_types.insert(ids.first().unwrap().clone(), self.rewrite_type(u, ty)?);
            } else if ids.len() > 1 {
                // ids[0] -> ids[1] -> ... -> ids[n]
                for i in 0..(ids.len() - 1) {
                    common_types.insert(
                        ids[i].clone(),
                        SchemaType::TypeDef {
                            type_name: Name::unqualified_name(ids[i + 1].clone()),
                        },
                    );
                    common_types.insert(ids[ids.len() - 1].clone(), self.rewrite_type(u, ty)?);
                }
            }
        }
        Ok(common_types)
    }
}

// Bind types to random ids recursively
fn bind_type(ty: &SchemaType, u: &mut Unstructured<'_>, bindings: &mut Bindings) -> Result<()> {
    // flip a coin to decide if we should create a binding for the top-level type
    if u.ratio(1, 2)? {
        bindings.add_binding((ty.clone(), u.arbitrary()?));
    }
    match ty {
        SchemaType::Type(cedar_policy_validator::SchemaTypeVariant::Set { element }) => {
            bind_type(element, u, bindings)?;
        }
        SchemaType::Type(cedar_policy_validator::SchemaTypeVariant::Record {
            attributes,
            additional_attributes: _,
        }) => {
            attributes
                .iter()
                .map(|(_, attr_ty)| bind_type(&attr_ty.ty, u, bindings))
                .collect::<Result<Vec<()>>>()?;
        }
        SchemaType::TypeDef { .. } => unreachable!("common type references shouldn't exist here"),
        _ => {}
    };
    Ok(())
}

impl Schema {
    /// Add common types to the existing schema and return a new schema
    pub fn add_common_types(
        &self,
        u: &mut Unstructured<'_>,
    ) -> Result<cedar_policy_validator::NamespaceDefinition> {
        let attribute_types = &self.attributes;
        let mut bindings = Bindings::new();
        for (_, ty) in attribute_types {
            bind_type(ty, u, &mut bindings)?;
        }

        let common_types = bindings.to_common_types(u)?;
        let entity_types: HashMap<Id, EntityType> = HashMap::from_iter(
            self.schema
                .entity_types
                .iter()
                .map(|(id, et)| Ok((id.clone(), bindings.rewrite_entity_type(u, et)?)))
                .collect::<Result<Vec<_>>>()?,
        );
        let actions = HashMap::from_iter(
            self.schema
                .actions
                .iter()
                .map(|(id, ty)| {
                    Ok((
                        id.to_owned(),
                        ActionType {
                            attributes: ty.attributes.to_owned(),
                            member_of: ty.member_of.clone(),
                            applies_to: match &ty.applies_to {
                                Some(applies) => Some(ApplySpec {
                                    resource_types: applies.resource_types.clone(),
                                    principal_types: applies.principal_types.clone(),
                                    context: AttributesOrContext(
                                        bindings.rewrite_record_type(u, &applies.context.0)?,
                                    ),
                                }),
                                None => None,
                            },
                        },
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        );
        Ok(cedar_policy_validator::NamespaceDefinition {
            common_types: common_types.into(),
            entity_types: entity_types.into(),
            actions: actions.into(),
        })
    }
    /// Get a slice of all of the entity types in this schema
    pub fn entity_types(&self) -> &[ast::Name] {
        &self.entity_types
    }

    /// Create an arbitrary `Schema` based on (compatible with) the given Validator `NamespaceDefinition`.
    pub fn from_nsdef(
        nsdef: cedar_policy_validator::NamespaceDefinition,
        namespace: Option<Name>,
        settings: ABACSettings,
        u: &mut Unstructured<'_>,
    ) -> Result<Schema> {
        let mut principal_types = HashSet::new();
        let mut resource_types = HashSet::new();
        for atype in nsdef.actions.values() {
            if let Some(applyspec) = atype.applies_to.as_ref() {
                if let Some(ptypes) = applyspec.principal_types.as_ref() {
                    principal_types.extend(ptypes.iter());
                }
                if let Some(rtypes) = applyspec.resource_types.as_ref() {
                    resource_types.extend(rtypes.iter());
                }
            }
        }
        let mut attributes = Vec::new();
        for schematype in nsdef
            .common_types
            .values()
            .chain(nsdef.entity_types.values().map(|etype| &etype.shape.0))
        {
            attributes.extend(attrs_in_schematype(&nsdef, schematype));
        }
        let attributes_by_type =
            build_attributes_by_type(&nsdef, &nsdef.entity_types, namespace.as_ref());
        Ok(Schema {
            namespace,
            constant_pool: u
                .arbitrary()
                .map_err(|e| while_doing("generating constant pool".into(), e))?,
            unknown_pool: UnknownPool::default(),
            ext_funcs: AvailableExtensionFunctions::create(&settings),
            settings,
            entity_types: nsdef
                .entity_types
                .keys()
                .map(|k| k.clone().into())
                .collect(),
            principal_types: principal_types.into_iter().cloned().collect(),
            actions_eids: nsdef.actions.keys().cloned().map(ast::Eid::new).collect(),
            resource_types: resource_types.into_iter().cloned().collect(),
            attributes,
            attributes_by_type,
            schema: nsdef,
        })
    }

    /// Create an arbitrary `Schema` based on (compatible with) the given Validator `SchemaFragment`.
    pub fn from_schemafrag(
        schemafrag: cedar_policy_validator::SchemaFragment,
        settings: ABACSettings,
        u: &mut Unstructured<'_>,
    ) -> Result<Schema> {
        let mut nsdefs = schemafrag.0.into_iter();
        match nsdefs.next() {
            None => panic!("Empty SchemaFragment not supported in this method"),
            Some((ns, nsdef)) => match nsdefs.next() {
                Some(_) => unimplemented!(
                    "SchemaFragment with multiple namespaces not yet supported in this method"
                ),
                None => Self::from_nsdef(nsdef, ns, settings, u),
            },
        }
    }

    /// Get an `ExprGenerator` for generating expressions that conform to this `Schema`.
    ///
    /// If `hierarchy` is present, any literal UIDs included in generated `Expr`s will
    /// (usually) exist in the hierarchy.
    pub fn exprgenerator<'s>(&'s self, hierarchy: Option<&'s Hierarchy>) -> ExprGenerator<'s> {
        ExprGenerator {
            schema: self,
            settings: &self.settings,
            constant_pool: &self.constant_pool,
            unknown_pool: &self.unknown_pool,
            ext_funcs: &self.ext_funcs,
            hierarchy,
            uid_gen_mode: EntityUIDGenMode::default(),
        }
    }

    /// Get an arbitrary `Schema`.
    pub fn arbitrary(settings: ABACSettings, u: &mut Unstructured<'_>) -> Result<Schema> {
        let namespace = arbitrary_namespace(u)?;

        // first generate the pool of names. we generate a set (so there are no
        // duplicates), but then convert it to a Vec (because we want them
        // ordered, even though we want the order to be arbitrary)
        let entity_type_ids: HashSet<ast::Id> = u
            .arbitrary()
            .map_err(|e| while_doing("generating entity type ids".into(), e))?;
        let entity_type_ids: Vec<ast::Id> = if entity_type_ids.is_empty() {
            // we want there to be at least one valid Name
            vec!["a".parse().expect("should be a valid Name")]
        } else {
            entity_type_ids.into_iter().collect()
        };
        // Qualify the entity type ids with the schema namespace. When the ids
        // are written as part of entity type declarations in the schema, the
        // namespace will not be included, but we want to know it when
        // constructing schema types for attributes based on the declared entity
        // types.
        let entity_type_names: Vec<ast::Name> = entity_type_ids
            .iter()
            .map(|id| build_qualified_entity_type_name(namespace.clone(), id.clone().into()))
            .collect();

        // now turn each of those names into an EntityType, no
        // member-relationships yet
        let mut entity_types: Vec<(Id, cedar_policy_validator::EntityType)> = entity_type_ids
            .iter()
            .filter(|id| settings.enable_action_groups_and_attrs || id.to_string() != "Action")
            .map(|id| {
                Ok((
                    id.clone(),
                    cedar_policy_validator::EntityType {
                        member_of_types: vec![],
                        shape: arbitrary_attrspec(&settings, &entity_type_names, u)?,
                    },
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        // fill in member-relationships. WLOG we only make edges from entities
        // earlier in the entity_types list to entities later in the list; this
        // ensures we get a DAG
        for i in 0..entity_types.len() {
            for name in &entity_type_ids[(i + 1)..] {
                if u.ratio::<u8>(1, 2)? {
                    entity_types[i].1.member_of_types.push(name.clone().into());
                }
            }
        }

        // same for actions
        let action_names: HashSet<String> = u
            .arbitrary()
            .map_err(|e| while_doing("generating action names".into(), e))?;
        let action_names: HashSet<SmolStr> = action_names.into_iter().map(SmolStr::from).collect();
        let action_names: Vec<SmolStr> = action_names
            .into_iter()
            .filter(|n| {
                !n.contains('\"')
                    && !n.contains('\\')
                    && !n.contains('\0')
                    && !n.contains('\r')
                    && !n.contains('\n')
            })
            .collect();
        // we want there to be at least one valid Action
        let action_names = if action_names.is_empty() {
            vec!["action".into()]
        } else {
            action_names
        };
        let mut principal_types: HashSet<Name> = HashSet::new();
        let mut resource_types = HashSet::new();
        // optionally return a list of entity types and add them to `tys` at the same time
        let pick_entity_types = |tys: &mut HashSet<Name>, u: &mut Unstructured<'_>| {
            Result::Ok(if u.ratio::<u8>(1, 4)? {
                // The action applies to an unspecified
                // resource and no other entity types.
                None
            } else {
                // for each entity type, flip a coin to see
                // whether to include it as a possible
                // principal type for this action
                Some(
                    entity_types
                        .iter()
                        .filter_map(|(name, _)| match u.ratio::<u8>(1, 2) {
                            Ok(true) => {
                                tys.insert(build_qualified_entity_type_name(
                                    namespace.clone(),
                                    name.clone().into(),
                                ));
                                Some(name.clone().into())
                            }
                            Ok(false) => None,
                            Err(_) => None,
                        })
                        .collect::<Vec<Name>>(),
                )
            })
        };
        let mut actions: Vec<(SmolStr, ActionType)> = action_names
            .iter()
            .map(|name| {
                Ok((
                    name.clone(),
                    ActionType {
                        applies_to: {
                            let apply_spec = if u.ratio::<u8>(1, 8)? {
                                // The action applies to an unspecified principal
                                // and resource, and no other entity types.
                                None
                            } else {
                                Some(ApplySpec {
                                    resource_types: pick_entity_types(&mut resource_types, u)?,
                                    principal_types: pick_entity_types(&mut principal_types, u)?,
                                    context: arbitrary_attrspec(&settings, &entity_type_names, u)?,
                                })
                            };
                            if settings.enable_unspecified_apply_spec {
                                apply_spec
                            } else {
                                match apply_spec {
                                    Some(ApplySpec {
                                        resource_types,
                                        principal_types,
                                        context,
                                    }) if resource_types.is_some() || principal_types.is_some() => {
                                        Some(ApplySpec {
                                            resource_types: if resource_types.is_none() {
                                                Some(vec![])
                                            } else {
                                                resource_types
                                            },
                                            principal_types: if principal_types.is_none() {
                                                Some(vec![])
                                            } else {
                                                principal_types
                                            },
                                            context,
                                        })
                                    }
                                    // `apply_spec` either is None or has both resource and principal types to be None
                                    //  we fail early for these cases
                                    _ => {
                                        return Err(Error::NoValidPrincipalOrResourceTypes);
                                    }
                                }
                            }
                        },
                        member_of: if settings.enable_action_groups_and_attrs {
                            Some(vec![])
                        } else {
                            None
                        },
                        //TODO: Fuzz arbitrary attribute names and values.
                        attributes: None,
                    },
                ))
            })
            .collect::<Result<Vec<_>>>()?;
        if principal_types.is_empty() || resource_types.is_empty() {
            // rather than try to remediate this situation, we just fail-fast
            // and start over
            return Err(Error::NoValidPrincipalOrResourceTypes);
        }
        // fill in member-relationships for actions; see notes for entity types
        if settings.enable_action_groups_and_attrs {
            for i in 0..actions.len() {
                for name in action_names[(i + 1)..].iter() {
                    if u.ratio::<u8>(1, 2)? {
                        actions[i]
                            .1
                            .member_of
                            .as_mut()
                            .expect(
                                "`member_of` is always `Some` when action groups are permitted.",
                            )
                            .push(cedar_policy_validator::ActionEntityUID::default_type(
                                name.clone(),
                            ));
                    }
                }
            }
        }

        let nsdef = cedar_policy_validator::NamespaceDefinition {
            common_types: HashMap::new().into(),
            entity_types: entity_types.into_iter().collect(),
            actions: actions.into_iter().collect(),
        };
        let attrsorcontexts /* : impl Iterator<Item = &AttributesOrContext> */ = nsdef.entity_types.values().map(|et| attrs_from_attrs_or_context(&nsdef, &et.shape))
            .chain(nsdef.actions.iter().filter_map(|(_, action)| action.applies_to.as_ref()).map(|a| attrs_from_attrs_or_context(&nsdef, &a.context)));
        let attributes: Vec<(SmolStr, cedar_policy_validator::SchemaType)> = attrsorcontexts
            .flat_map(|attributes| {
                attributes.attrs.iter().map(|(s, ty)| {
                    (
                        s.parse().expect("attribute names should be valid Ids"),
                        ty.ty.clone(),
                    )
                })
            })
            .collect();
        let attributes_by_type =
            build_attributes_by_type(&nsdef, nsdef.entity_types.iter(), namespace.as_ref());
        let actions_eids = nsdef
            .actions
            .keys()
            .map(|name| ast::Eid::new(name.clone()))
            .collect();
        Ok(Schema {
            schema: nsdef,
            namespace,
            constant_pool: u
                .arbitrary()
                .map_err(|e| while_doing("generating constant pool".into(), e))?,
            unknown_pool: UnknownPool::default(),
            ext_funcs: AvailableExtensionFunctions::create(&settings),
            settings,
            entity_types: entity_type_names,
            principal_types: principal_types.into_iter().collect(),
            actions_eids,
            resource_types: resource_types.into_iter().collect(),
            attributes,
            attributes_by_type,
        })
    }
    /// size hint for arbitrary()
    pub fn arbitrary_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <HashSet<ast::Name> as Arbitrary>::size_hint(depth),
            arbitrary_attrspec_size_hint(depth), // actually we do one of these per Name that was generated
            size_hint_for_ratio(1, 2),           // actually many of these calls
            <HashSet<String> as Arbitrary>::size_hint(depth),
            size_hint_for_ratio(1, 8), // actually many of these calls
            size_hint_for_ratio(1, 4), // zero to many of these calls
            size_hint_for_ratio(1, 2), // zero to many of these calls
            arbitrary_attrspec_size_hint(depth),
            size_hint_for_ratio(1, 2), // actually many of these calls
            <ConstantPool as Arbitrary>::size_hint(depth),
        ])
    }

    /// Get an arbitrary Hierarchy conforming to the schema.
    pub fn arbitrary_hierarchy(&self, u: &mut Unstructured<'_>) -> Result<Hierarchy> {
        HierarchyGenerator {
            mode: HierarchyGeneratorMode::SchemaBased { schema: self },
            uid_gen_mode: EntityUIDGenMode::default(),
            num_entities: NumEntities::RangePerEntityType(1..=self.settings.max_width),
            u,
            extensions: Extensions::all_available(),
        }
        .generate()
    }

    /// Get an arbitrary Hierarchy conforming to the schema but with nanoid uids.
    pub fn arbitrary_hierarchy_with_nanoid_uids(
        &self,
        nanoid_len: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<Hierarchy> {
        HierarchyGenerator {
            mode: HierarchyGeneratorMode::SchemaBased { schema: self },
            uid_gen_mode: EntityUIDGenMode::Nanoid(nanoid_len),
            num_entities: NumEntities::RangePerEntityType(1..=self.settings.max_width),
            u,
            extensions: Extensions::all_available(),
        }
        .generate()
    }

    fn arbitrary_uid_with_optional_type(
        &self,
        ty_name: Option<ast::Name>,
        hierarchy: Option<&Hierarchy>,
        request_field: ast::Var,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        let ty = build_qualified_entity_type(self.namespace().cloned(), ty_name);
        match ty {
            ast::EntityType::Specified(ty) => self
                .exprgenerator(hierarchy)
                .arbitrary_uid_with_type(&ty, u),
            ast::EntityType::Unspecified => Ok(ast::EntityUID::unspecified_from_eid(
                ast::Eid::new(request_field.to_string()),
            )),
        }
    }

    /// internal helper function, try to convert `Type` into `SchemaType`
    pub fn try_into_schematype(
        &self,
        ty: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<Option<cedar_policy_validator::SchemaType>> {
        Ok(match ty {
            Type::Bool => Some(SchemaTypeVariant::Boolean),
            Type::Long => Some(SchemaTypeVariant::Long),
            Type::String => Some(SchemaTypeVariant::String),
            Type::Set(None) => None, // SchemaType doesn't support any-set
            Type::Set(Some(el_ty)) => {
                self.try_into_schematype(el_ty, u)?
                    .map(|schematy| SchemaTypeVariant::Set {
                        element: Box::new(schematy),
                    })
            }
            Type::Record => Some(SchemaTypeVariant::Record {
                attributes: BTreeMap::new(),
                additional_attributes: true,
            }),
            Type::Entity => {
                let entity_type = self.exprgenerator(None).generate_uid(u)?.components().0;
                // not possible for Schema::arbitrary_uid to generate an unspecified entity
                match entity_type {
                    ast::EntityType::Unspecified => {
                        panic!("should not be possible to generate an unspecified entity")
                    }
                    ast::EntityType::Specified(name) => {
                        Some(entity_type_name_to_schema_type_variant(&name))
                    }
                }
            }
            Type::IPAddr => Some(SchemaTypeVariant::Extension {
                name: "ipaddr".parse().unwrap(),
            }),
            Type::Decimal => Some(SchemaTypeVariant::Extension {
                name: "decimal".parse().unwrap(),
            }),
        }
        .map(SchemaType::Type))
    }

    /// get an attribute name and its `SchemaType`, from the schema
    pub fn arbitrary_attr(
        &self,
        u: &mut Unstructured<'_>,
    ) -> Result<&(SmolStr, cedar_policy_validator::SchemaType)> {
        u.choose(&self.attributes)
            .map_err(|e| while_doing("getting arbitrary attr from schema".into(), e))
    }

    /// Given a type, get an entity type name and attribute name, such that
    /// entities with that typename have a (possibly optional) attribute with
    /// the given type
    pub fn arbitrary_attr_for_type(
        &self,
        target_type: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<&(ast::Name, SmolStr)> {
        match self.attributes_by_type.get(target_type) {
            Some(vec) => u.choose(vec).map_err(|e| {
                while_doing(
                    format!("getting arbitrary attr for type {target_type:?}"),
                    e,
                )
            }),
            None => Err(Error::EmptyChoose {
                doing_what: format!("getting arbitrary attr for type {target_type:?}"),
            }),
        }
    }

    /// Given a schematype, get an entity type name and attribute name, such
    /// that entities with that typename have a (possibly optional) attribute
    /// with the given schematype
    pub fn arbitrary_attr_for_schematype(
        &self,
        target_type: impl Into<cedar_policy_validator::SchemaType>,
        u: &mut Unstructured<'_>,
    ) -> Result<(ast::Name, SmolStr)> {
        let target_type: cedar_policy_validator::SchemaType = target_type.into();
        let pairs: Vec<(ast::Name, SmolStr)> = self
            .schema
            .entity_types
            .iter()
            .map(|(name, et)| {
                (
                    build_qualified_entity_type_name(
                        self.namespace().cloned(),
                        name.clone().into(),
                    ),
                    attrs_from_attrs_or_context(&self.schema, &et.shape),
                )
            })
            .flat_map(|(tyname, attributes)| {
                attributes
                    .attrs
                    .iter()
                    .filter(|(_, ty)| ty.ty == target_type)
                    .map(move |(attr_name, _)| (tyname.clone(), attr_name.clone()))
            })
            .collect();
        u.choose(&pairs).cloned().map_err(|e| {
            while_doing(
                format!("getting arbitrary attr for schematype {target_type:?}"),
                e,
            )
        })
    }

    /// get an arbitrary policy conforming to this schema
    pub fn arbitrary_policy(
        &self,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<ABACPolicy> {
        let id = u.arbitrary()?;
        let annotations: HashMap<ast::AnyId, SmolStr> = u.arbitrary()?;
        let effect = u.arbitrary()?;
        let principal_constraint = self.arbitrary_principal_constraint(hierarchy, u)?;
        let action_constraint = self.arbitrary_action_constraint(u, Some(3))?;
        let resource_constraint = self.arbitrary_resource_constraint(hierarchy, u)?;
        let mut abac_constraints = Vec::new();
        let mut exprgenerator = self.exprgenerator(Some(hierarchy));
        u.arbitrary_loop(Some(0), Some(self.settings.max_depth as u32), |u| {
            if self.settings.match_types {
                abac_constraints.push(exprgenerator.generate_expr_for_type(
                    &Type::bool(),
                    self.settings.max_depth,
                    u,
                )?);
            } else {
                abac_constraints.push(exprgenerator.generate_expr(self.settings.max_depth, u)?);
            }
            Ok(std::ops::ControlFlow::Continue(()))
        })?;
        let mut conjunction = ast::Expr::val(true);
        for constraint in abac_constraints {
            conjunction = ast::Expr::and(conjunction, constraint);
        }
        Ok(ABACPolicy(GeneratedPolicy::new(
            id,
            annotations,
            effect,
            principal_constraint,
            action_constraint,
            resource_constraint,
            conjunction,
        )))
    }

    /// size hint for arbitrary_policy()
    pub fn arbitrary_policy_size_hint(
        _settings: &ABACSettings,
        depth: usize,
    ) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <PolicyID as Arbitrary>::size_hint(depth),
            <Effect as Arbitrary>::size_hint(depth),
            Self::arbitrary_principal_constraint_size_hint(depth),
            Self::arbitrary_action_constraint_size_hint(depth),
            Self::arbitrary_resource_constraint_size_hint(depth),
            (1, None), // not sure how to count the arbitrary_loop() call
        ])
    }

    fn arbitrary_principal_constraint(
        &self,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<PrincipalOrResourceConstraint> {
        // 20% of the time, NoConstraint
        if u.ratio(1, 5)? {
            Ok(PrincipalOrResourceConstraint::NoConstraint)
        } else {
            // 32% Eq, 16% In, 16% Is, 16% IsIn
            let uid = self
                .exprgenerator(Some(hierarchy))
                .arbitrary_principal_uid(u)?;
            let ety = u.choose(self.entity_types())?.clone();
            gen!(u,
                2 => Ok(PrincipalOrResourceConstraint::Eq(uid)),
                1 => Ok(PrincipalOrResourceConstraint::In(uid)),
                1 => Ok(PrincipalOrResourceConstraint::IsType(ety)),
                1 => Ok(PrincipalOrResourceConstraint::IsTypeIn(ety, uid))
            )
        }
    }
    fn arbitrary_principal_constraint_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_range(1, 10),
            arbitrary::size_hint::or_all(&[
                (0, Some(0)),
                ExprGenerator::arbitrary_principal_uid_size_hint(depth),
                ExprGenerator::arbitrary_principal_uid_size_hint(depth),
            ]),
        )
    }

    fn arbitrary_resource_constraint(
        &self,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<PrincipalOrResourceConstraint> {
        // 20% of the time, NoConstraint
        if u.ratio(1, 5)? {
            Ok(PrincipalOrResourceConstraint::NoConstraint)
        } else {
            // 32% Eq, 16% In, 16% Is, 16% IsIn
            let uid = self
                .exprgenerator(Some(hierarchy))
                .arbitrary_resource_uid(u)?;
            let ety = u.choose(self.entity_types())?.clone();
            gen!(u,
                2 => Ok(PrincipalOrResourceConstraint::Eq(uid)),
                1 => Ok(PrincipalOrResourceConstraint::In(uid)),
                1 => Ok(PrincipalOrResourceConstraint::IsType(ety)),
                1 => Ok(PrincipalOrResourceConstraint::IsTypeIn(ety, uid))
            )
        }
    }
    fn arbitrary_resource_constraint_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_range(1, 10),
            arbitrary::size_hint::or_all(&[
                (0, Some(0)),
                ExprGenerator::arbitrary_resource_uid_size_hint(depth),
                ExprGenerator::arbitrary_resource_uid_size_hint(depth),
            ]),
        )
    }

    fn arbitrary_action_constraint(
        &self,
        u: &mut Unstructured<'_>,
        max_list_length: Option<u32>,
    ) -> Result<ActionConstraint> {
        if !self.settings.enable_action_in_constraints {
            // 25% of the time, NoConstraint; 75%, Eq
            gen!(u,
        1 => Ok(ActionConstraint::NoConstraint),
        3 => Ok(ActionConstraint::Eq(self.exprgenerator(None).arbitrary_action_uid(u)?)))
        } else {
            // 10% of the time, NoConstraint; 30%, Eq; 30%, In; 30%, InList
            gen!(u,
            1 => Ok(ActionConstraint::NoConstraint),
            3 => Ok(ActionConstraint::Eq(self.exprgenerator(None).arbitrary_action_uid(u)?)),
            3 => Ok(ActionConstraint::In(self.exprgenerator(None).arbitrary_action_uid(u)?)),
            3 => {
                let mut uids = vec![];
                let exprgenerator = self.exprgenerator(None);
                u.arbitrary_loop(Some(0), max_list_length, |u| {
                    uids.push(exprgenerator.arbitrary_action_uid(u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ActionConstraint::InList(uids))
            })
        }
    }
    fn arbitrary_action_constraint_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            size_hint_for_range(1, 10),
            arbitrary::size_hint::or_all(&[
                (0, Some(0)),
                ExprGenerator::arbitrary_action_uid_size_hint(depth),
                ExprGenerator::arbitrary_action_uid_size_hint(depth),
                (1, None), // not sure how to hint for arbitrary_loop()
            ]),
        )
    }

    /// generate an arbitrary `ABACRequest` conforming to the schema
    pub fn arbitrary_request(
        &self,
        hierarchy: &Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<ABACRequest> {
        // first pick one of the valid Actions
        let (action_name, action) = self
            .schema
            .actions
            .iter()
            .nth(
                u.choose_index(self.schema.actions.len())
                    .expect("Failed to select action index."),
            )
            .expect("Failed to select action from map.");
        // now generate a valid request for that Action
        Ok(ABACRequest(Request {
            principal: match action
                .applies_to
                .as_ref()
                .and_then(|at| at.principal_types.as_ref())
            {
                None => self.arbitrary_uid_with_optional_type(
                    None,
                    Some(hierarchy),
                    ast::Var::Principal,
                    u,
                )?, // unspecified principal
                Some(types) => {
                    // Assert that these are vec, so it's safe to draw from directly
                    let types: &Vec<_> = types;
                    let ty = u.choose(types).map_err(|e| {
                        while_doing("choosing one of the action principal types".into(), e)
                    })?;
                    self.arbitrary_uid_with_optional_type(
                        Some(ty.clone()),
                        Some(hierarchy),
                        ast::Var::Principal,
                        u,
                    )?
                }
            },
            action: uid_for_action_name(self.namespace.clone(), ast::Eid::new(action_name.clone())),
            resource: match action
                .applies_to
                .as_ref()
                .and_then(|at| at.resource_types.as_ref())
            {
                None => self.arbitrary_uid_with_optional_type(
                    None,
                    Some(hierarchy),
                    ast::Var::Resource,
                    u,
                )?, // unspecified resource
                Some(types) => {
                    // Assert that these are vec, so it's safe to draw from directly
                    let types: &Vec<_> = types;
                    let ty = u.choose(types).map_err(|e| {
                        while_doing("choosing one of the action resource types".into(), e)
                    })?;
                    self.arbitrary_uid_with_optional_type(
                        Some(ty.clone()),
                        Some(hierarchy),
                        ast::Var::Resource,
                        u,
                    )?
                }
            },
            context: {
                let mut attributes: Vec<_> = action
                    .applies_to
                    .as_ref()
                    .map(|a| attrs_from_attrs_or_context(&self.schema, &a.context))
                    .iter()
                    .flat_map(|attributes| attributes.attrs.iter())
                    .collect();
                attributes.sort();
                let exprgenerator = self.exprgenerator(Some(hierarchy));
                let attrs = attributes
                    .iter()
                    .map(|(attr_name, attr_type)| {
                        Ok((
                            attr_name.parse().expect("failed to parse attribute name"),
                            exprgenerator
                                .generate_attr_value_for_schematype(
                                    &attr_type.ty,
                                    self.settings.max_depth,
                                    u,
                                )?
                                .into(),
                        ))
                    })
                    .collect::<Result<HashMap<_, _>>>()?;
                ast::Context::from_pairs(attrs, Extensions::all_available())
                    .map_err(Error::ContextError)?
            },
        }))
    }
    /// size hint for arbitrary_request()
    pub fn arbitrary_request_size_hint(_depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(size_hint_for_choose(None), (1, None))
    }

    /// Get the namespace of this `Schema`, if any
    pub fn namespace(&self) -> Option<&ast::Name> {
        self.namespace.as_ref()
    }

    /// Get the underlying schema file, as a `NamespaceDefinition`
    pub fn schemafile(&self) -> &cedar_policy_validator::NamespaceDefinition {
        &self.schema
    }

    /// Get the underlying schema file, as a String containing JSON
    pub fn schemafile_string(&self) -> String {
        serde_json::to_string_pretty(&self.schema)
            .expect("failed to serialize schema NamespaceDefinition")
    }
}

impl From<Schema> for SchemaFragment {
    fn from(schema: Schema) -> SchemaFragment {
        SchemaFragment(HashMap::from_iter([(schema.namespace, schema.schema)]).into())
    }
}

impl TryFrom<Schema> for ValidatorSchema {
    type Error = SchemaError;
    fn try_from(schema: Schema) -> std::result::Result<ValidatorSchema, Self::Error> {
        ValidatorSchema::try_from(SchemaFragment::from(schema))
    }
}

#[cfg(test)]
mod tests {
    use super::Schema;
    use crate::{hierarchy::EntityUIDGenMode, settings::ABACSettings};
    use arbitrary::Unstructured;
    use cedar_policy_core::entities::Entities;
    use cedar_policy_core::extensions::Extensions;
    use cedar_policy_validator::{CoreSchema, SchemaFragment, ValidatorSchema};
    use rand::{rngs::ThreadRng, thread_rng, RngCore};

    const RANDOM_BYTE_SIZE: u16 = 1024;
    const ITERATION: u8 = 100;

    const TEST_SETTINGS: ABACSettings = ABACSettings {
        match_types: false,
        enable_extensions: false,
        max_depth: 4,
        max_width: 4,
        enable_additional_attributes: false,
        enable_like: false,
        enable_action_groups_and_attrs: true,
        enable_arbitrary_func_call: false,
        enable_unknowns: false,
        enable_unspecified_apply_spec: true,
        enable_action_in_constraints: true,
    };

    const GITHUB_SCHEMA_STR: &str = r#"
    {
        "": {
            "entityTypes": {
                "User": {
                    "memberOfTypes": [
                        "UserGroup",
                        "Team"
                    ]
                },
                "UserGroup": {
                    "memberOfTypes": [
                        "UserGroup"
                    ]
                },
                "Repository": {
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "readers": {
                                "type": "Entity",
                                "name": "UserGroup"
                            },
                            "traigers": {
                                "type": "Entity",
                                "name": "UserGroup"
                            },
                            "writers": {
                                "type": "Entity",
                                "name": "UserGroup"
                            },
                            "maintainers": {
                                "type": "Entity",
                                "name": "UserGroup"
                            },
                            "admins": {
                                "type": "Entity",
                                "name": "UserGroup"
                            }
                        }
                    }
                },
                "Issue": {
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "repo": {
                                "type": "Entity",
                                "name": "Repository"
                            },
                            "reporter": {
                                "type": "Entity",
                                "name": "User"
                            }
                        }
                    }
                },
                "Org": {
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "members": {
                                "type": "Entity",
                                "name": "UserGroup"
                            },
                            "owners": {
                                "type": "Entity",
                                "name": "UserGroup"
                            }
                        }
                    }
                },
                "Team": {
                    "memberOfTypes": [
                        "UserGroup"
                    ]
                }
            },
            "actions": {
                "pull": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                },
                "fork": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                },
                "delete_issue": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Issue"
                        ]
                    }
                },
                "edit_issue": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Issue"
                        ]
                    }
                },
                "assign_issue": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Issue"
                        ]
                    }
                },
                "push": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                },
                "add_reader": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                },
                "add_triager": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                },
                "add_writer": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                },
                "add_maintainer": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                },
                "add_admin": {
                    "appliesTo": {
                        "principalTypes": [
                            "User"
                        ],
                        "resourceTypes": [
                            "Repository"
                        ]
                    }
                }
            }
        }
    }
    "#;

    const DOCUMENT_CLOUD_SCHEMA_STR: &str = r#"
    {
        "": {
            "entityTypes": {
                "User": {
                    "memberOfTypes": [
                        "Group"
                    ],
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "personalGroup": {
                                "type": "Entity",
                                "name": "Group"
                            },
                            "blocked": {
                                "type": "Set",
                                "element": {
                                    "type": "Entity",
                                    "name": "User"
                                }
                            }
                        }
                    }
                },
                "Group": {
                    "memberOfTypes": [
                        "DocumentShare"
                    ],
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "owner": {
                                "type": "Entity",
                                "name": "User"
                            }
                        }
                    }
                },
                "Document": {
                    "memberOfTypes": [],
                    "shape": {
                        "type": "Record",
                        "attributes": {
                            "owner": {
                                "type": "Entity",
                                "name": "User"
                            },
                            "isPrivate": {
                                "type": "Boolean"
                            },
                            "publicAccess": {
                                "type": "String"
                            },
                            "viewACL": {
                                "type": "Entity",
                                "name": "DocumentShare"
                            },
                            "modifyACL": {
                                "type": "Entity",
                                "name": "DocumentShare"
                            },
                            "manageACL": {
                                "type": "Entity",
                                "name": "DocumentShare"
                            }
                        }
                    }
                },
                "DocumentShare": {},
                "Public": {
                    "memberOfTypes": [
                        "DocumentShare"
                    ]
                },
                "Drive": {}
            },
            "actions": {
                "CreateDocument": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Drive"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "ViewDocument": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Document"
                        ],
                        "principalTypes": [
                            "User",
                            "Public"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "DeleteDocument": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Document"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "ModifyDocument": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Document"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "EditIsPrivate": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Document"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "AddToShareACL": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Document"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "EditPublicAccess": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Document"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "CreateGroup": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Drive"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "ModifyGroup": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Group"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                },
                "DeleteGroup": {
                    "appliesTo": {
                        "resourceTypes": [
                            "Group"
                        ],
                        "principalTypes": [
                            "User"
                        ],
                        "context": {
                            "type": "ReusedContext"
                        }
                    }
                }
            },
            "commonTypes": {
                "ReusedContext": {
                    "type": "Record",
                    "attributes": {
                        "is_authenticated": {
                            "type": "Boolean",
                            "required": true
                        }
                    }
                }
            }
        }
    }"#;

    #[test]
    fn entities_generation_github() {
        let fragment = SchemaFragment::from_file(GITHUB_SCHEMA_STR.as_bytes())
            .expect("schema str should be valid!");
        let mut rng = thread_rng();
        for _ in 0..ITERATION {
            assert!(generate_hierarchy_from_schema(&mut rng, &fragment).is_ok());
        }
    }

    #[test]
    fn entities_generation_document_cloud() {
        let fragment = SchemaFragment::from_file(DOCUMENT_CLOUD_SCHEMA_STR.as_bytes())
            .expect("schema str should be valid!");
        let mut rng = thread_rng();
        for _ in 0..ITERATION {
            assert!(generate_hierarchy_from_schema(&mut rng, &fragment).is_ok());
        }
    }

    fn generate_hierarchy_from_schema(
        rng: &mut ThreadRng,
        fragment: &SchemaFragment,
    ) -> cedar_policy_core::entities::Result<Entities> {
        let mut bytes = [0; RANDOM_BYTE_SIZE as usize];
        rng.fill_bytes(&mut bytes);
        let mut u = Unstructured::new(&bytes);
        let schema = Schema::from_schemafrag(fragment.clone(), TEST_SETTINGS, &mut u)
            .expect("failed to generate schema!");
        let h = schema
            .arbitrary_hierarchy_with_nanoid_uids(EntityUIDGenMode::default_nanoid_len(), &mut u)
            .expect("failed to generate hierarchy!");
        let vschema =
            ValidatorSchema::try_from(schema).expect("failed to convert to ValidatorSchema");
        let coreschema = CoreSchema::new(&vschema);
        Entities::from_entities(
            h.entities().cloned(),
            Some(&coreschema),
            cedar_policy_core::entities::TCComputation::ComputeNow,
            Extensions::all_available(),
        )
    }
}
