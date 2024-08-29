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
use cedar_policy_core::ast::{self, Effect, PolicyID, UnreservedId};
use cedar_policy_core::extensions::Extensions;
use cedar_policy_validator::json_schema::CommonTypeId;
use cedar_policy_validator::{
    json_schema, ActionBehavior, AllDefs, RawName, SchemaError, ValidatorNamespaceDef,
    ValidatorSchema, ValidatorSchemaFragment,
};
use smol_str::{SmolStr, ToSmolStr};
use std::collections::BTreeMap;

/// Contains the schema, but also pools of constants etc
#[derive(Debug, Clone)]
pub struct Schema {
    /// actual underlying schema
    pub schema: json_schema::NamespaceDefinition<ast::InternalName>,
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
    pub entity_types: Vec<ast::EntityType>,
    /// list of entity types that occur as a valid principal for at least one
    /// action in the `schema`
    pub principal_types: Vec<ast::EntityType>,
    /// list of Eids that exist as a non-`None` actions name for an action in
    /// the schema.
    pub actions_eids: Vec<ast::Eid>,
    /// list of entity types that occur as a valid resource for at least one
    /// action in the `schema`
    pub resource_types: Vec<ast::EntityType>,
    /// list of (attribute, attribute type) pairs that occur in the `schema`
    attributes: Vec<(
        SmolStr,
        json_schema::EntityAttributeTypeInternal<ast::InternalName>,
    )>,
    /// map from type to (entity type, attribute name) pairs indicating
    /// attributes in the `schema` that have that type
    attributes_by_type: HashMap<Type, Vec<(ast::EntityType, SmolStr)>>,
}

/// internal helper function, basically `impl Arbitrary for RecordOrContextAttributes`
fn arbitrary_rca<N: From<ast::Name>>(
    settings: &ABACSettings,
    entity_types: &[ast::EntityType],
    u: &mut Unstructured<'_>,
) -> Result<json_schema::RecordOrContextAttributes<N>> {
    let attr_names: Vec<ast::Id> = u
        .arbitrary()
        .map_err(|e| while_doing("generating attribute names for an attrspec".into(), e))?;
    Ok(json_schema::RecordOrContextAttributes(json_schema::Type::Type(
        json_schema::TypeVariant::Record(json_schema::RecordType {
            attributes: attr_names
                .into_iter()
                .map(|attr| {
                    let mut ty = arbitrary_recordattributetype_with_bounded_depth::<N>(
                        settings,
                        entity_types,
                        settings.max_depth,
                        u,
                    )?;
                    if !settings.enable_extensions {
                        // can't have extension types. regenerate until morale improves
                        while ty.ty.is_extension().expect("DRT does not generate schema type using type defs, so `is_extension` should be `Some`") {
                            ty = arbitrary_recordattributetype_with_bounded_depth::<N>(
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
        }),
    )))
}
/// size hint for [`arbitrary_rca()`]
fn arbitrary_rca_size_hint(depth: usize) -> (usize, Option<usize>) {
    arbitrary::size_hint::recursion_guard(depth, |depth| {
        arbitrary::size_hint::and_all(&[
            <Vec<ast::Id> as Arbitrary>::size_hint(depth),
            arbitrary_recordattributetype_size_hint(depth),
            <bool as Arbitrary>::size_hint(depth),
        ])
    })
}

/// internal helper function, basically `impl Arbitrary for EntityAttributes`
fn arbitrary_entityattributes<N: From<ast::Name>>(
    settings: &ABACSettings,
    entity_types: &[ast::EntityType],
    u: &mut Unstructured<'_>,
) -> Result<json_schema::EntityAttributes<N>> {
    // RFC 68 is not yet fully supported.
    // Currently, we never generate `EAMap`s in this function.
    Ok(json_schema::EntityAttributes::RecordAttributes(
        arbitrary_rca(settings, entity_types, u)?,
    ))
}

/// internal helper function, an alternative to the `Arbitrary` impl for
/// [`json_schema::RecordAttributeType`] that implements a bounded maximum depth.
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
fn arbitrary_recordattributetype_with_bounded_depth<N: From<ast::Name>>(
    settings: &ABACSettings,
    entity_types: &[ast::EntityType],
    max_depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<json_schema::RecordAttributeType<N>> {
    Ok(json_schema::RecordAttributeType {
        ty: arbitrary_schematype_with_bounded_depth::<N>(settings, entity_types, max_depth, u)?,
        required: u.arbitrary()?,
    })
}
/// size hint for [`arbitrary_recordattributetype_with_bounded_depth()`]
fn arbitrary_recordattributetype_size_hint(depth: usize) -> (usize, Option<usize>) {
    arbitrary::size_hint::and(
        arbitrary_schematype_size_hint(depth),
        <bool as Arbitrary>::size_hint(depth),
    )
}

/// internal helper function, an alternative to the `Arbitrary` impl for
/// [`json_schema::Type`] that implements a bounded maximum depth.
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
pub fn arbitrary_schematype_with_bounded_depth<N: From<ast::Name>>(
    settings: &ABACSettings,
    entity_types: &[ast::EntityType],
    max_depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<json_schema::Type<N>> {
    Ok(json_schema::Type::Type(uniform!(
        u,
        json_schema::TypeVariant::String,
        json_schema::TypeVariant::Long,
        json_schema::TypeVariant::Boolean,
        {
            if max_depth == 0 {
                // can't recurse; we arbitrarily choose Set<Long> in this case
                json_schema::TypeVariant::Set {
                    element: Box::new(json_schema::Type::Type(json_schema::TypeVariant::Long)),
                }
            } else {
                json_schema::TypeVariant::Set {
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
                json_schema::TypeVariant::Record(json_schema::RecordType {
                    attributes: BTreeMap::new(),
                    additional_attributes: if settings.enable_additional_attributes {
                        u.arbitrary()?
                    } else {
                        false
                    },
                })
            } else {
                json_schema::TypeVariant::Record(json_schema::RecordType {
                    attributes: {
                        let attr_names: HashSet<String> = u
                            .arbitrary()
                            .map_err(|e| while_doing("generating attribute names".into(), e))?;
                        attr_names
                            .into_iter()
                            .map(|attr_name| {
                                Ok((
                                    attr_name.into(),
                                    arbitrary_recordattributetype_with_bounded_depth(
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
                })
            }
        },
        entity_type_name_to_schema_type_variant::<N>(u.choose(entity_types)?),
        json_schema::TypeVariant::Extension {
            name: "ipaddr".parse().unwrap(),
        },
        json_schema::TypeVariant::Extension {
            name: "decimal".parse().unwrap(),
        }
    )))
}

/// Convert an [`ast::EntityType`] into the corresponding
/// [`json_schema::TypeVariant`] for an entity reference with that entity type.
pub fn entity_type_name_to_schema_type_variant<N: From<ast::Name>>(
    name: &ast::EntityType,
) -> json_schema::TypeVariant<N> {
    json_schema::TypeVariant::Entity {
        name: N::from(name.as_ref().clone()),
    }
}

/// Convert an [`ast::EntityType`] into the corresponding [`json_schema::Type`]
/// for an entity reference with that entity type.
pub fn entity_type_name_to_schema_type<N: From<ast::Name>>(
    name: &ast::EntityType,
) -> json_schema::Type<N> {
    json_schema::Type::Type(entity_type_name_to_schema_type_variant(name))
}

/// size hint for arbitrary_schematype_with_bounded_depth
fn arbitrary_schematype_size_hint(depth: usize) -> (usize, Option<usize>) {
    // assume it's similar to the unbounded-depth version
    <json_schema::Type<RawName> as Arbitrary>::size_hint(depth)
}

/// internal helper function, get the [`ast::EntityUID`] corresponding to the given action
pub fn uid_for_action_name(namespace: Option<&ast::Name>, action_name: ast::Eid) -> ast::EntityUID {
    let entity_type = ast::EntityType::from_normalized_str("Action")
        .expect("valid id")
        .qualify_with(namespace);
    ast::EntityUID::from_components(entity_type, action_name, None)
}

/// Lookup the given `common_type_name` in the `schema`, and if it's defined,
/// return its definition
pub fn lookup_common_type<'a>(
    schema: &'a json_schema::NamespaceDefinition<ast::InternalName>,
    common_type_name: &ast::InternalName,
) -> Option<&'a json_schema::Type<ast::InternalName>> {
    // uh-oh: the common `type_name` could refer to a common type defined in
    // another namespace, but our `schema` is only a `NamespaceDefinition`,
    // which only contains items in a single namespace.
    // For now, we assume that in DRT, both definitions and references are
    // always all in the same single namespace, so it's safe to strip the
    // namespace and look it up in the current namespace's `common_types`
    let base_type_name =
        CommonTypeId::unchecked(common_type_name.basename().clone().try_into().unwrap());
    schema.common_types.get(&base_type_name)
}

/// internal helper function, convert a [`json_schema::Type`] to a [`Type`]
/// (loses some information)
fn schematype_to_type(
    schema: &json_schema::NamespaceDefinition<ast::InternalName>,
    schematy: &json_schema::Type<ast::InternalName>,
) -> Type {
    match schematy {
        json_schema::Type::CommonTypeRef { type_name } => schematype_to_type(
            schema,
            lookup_common_type(schema, type_name)
                .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
        ),
        json_schema::Type::Type(ty) => match ty {
            json_schema::TypeVariant::Boolean => Type::bool(),
            json_schema::TypeVariant::Long => Type::long(),
            json_schema::TypeVariant::String => Type::string(),
            json_schema::TypeVariant::Set { element } => {
                Type::set_of(schematype_to_type(schema, element))
            }
            json_schema::TypeVariant::Record { .. } => Type::record(),
            json_schema::TypeVariant::Entity { .. } => Type::entity(),
            json_schema::TypeVariant::EntityOrCommon { type_name } => {
                match lookup_common_type(schema, type_name) {
                    Some(ty) => schematype_to_type(schema, ty),
                    None => Type::entity(),
                }
            }
            json_schema::TypeVariant::Extension { name } => match name.as_ref() {
                "ipaddr" => Type::ipaddr(),
                "decimal" => Type::decimal(),
                _ => panic!("unrecognized extension type: {name:?}"),
            },
        },
    }
}

/// internal helper function, convert a
/// [`json_schema::EntityAttributeTypeInternal`] to a [`Type`] (loses some
/// information)
fn eatypeinternal_to_type(
    schema: &json_schema::NamespaceDefinition<ast::InternalName>,
    eatypeinternal: &json_schema::EntityAttributeTypeInternal<ast::InternalName>,
) -> Type {
    match eatypeinternal {
        json_schema::EntityAttributeTypeInternal::Type(ty) => schematype_to_type(schema, ty),
        json_schema::EntityAttributeTypeInternal::EAMap { .. } => Type::record(), // For these purposes, EAMaps are just records, as runtime values of type EAMap are valid runtime values of type Record
    }
}

/// Get an arbitrary namespace for a schema. The namespace may be absent.
fn arbitrary_namespace(u: &mut Unstructured<'_>) -> Result<Option<ast::Name>> {
    u.arbitrary()
        .map_err(|e| while_doing("generating namespace".into(), e))
}

/// Information about record or context attributes
pub(crate) struct RecordOrContextAttributes<'a> {
    /// the actual attributes
    pub attrs: &'a BTreeMap<SmolStr, json_schema::RecordAttributeType<ast::InternalName>>,
    /// whether `additional_attributes` is set
    pub additional_attrs: bool,
}

/// Information about entity attributes
pub(crate) struct EntityAttributes {
    /// the actual attributes
    pub attrs: BTreeMap<SmolStr, json_schema::EntityAttributeType<ast::InternalName>>,
    /// whether `additional_attributes` is set
    pub additional_attrs: bool,
}

/// Given a [`json_schema::RecordOrContextAttributes`], get the
/// [`RecordOrContextAttributes`] describing it
pub(crate) fn attrs_from_rca<'a>(
    schema: &'a json_schema::NamespaceDefinition<ast::InternalName>,
    rca: &'a json_schema::RecordOrContextAttributes<ast::InternalName>,
) -> RecordOrContextAttributes<'a> {
    match &rca.0 {
        json_schema::Type::CommonTypeRef { type_name } => match lookup_common_type(schema, type_name).unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")) {
            json_schema::Type::CommonTypeRef { .. } => panic!("common type `{type_name}` refers to another common type, which is not allowed as of this writing?"),
            json_schema::Type::Type(json_schema::TypeVariant::Record(json_schema::RecordType { attributes, additional_attributes })) => RecordOrContextAttributes { attrs: attributes, additional_attrs: *additional_attributes },
        json_schema::Type::Type(ty) => panic!("expected attributes or context to be a record, got {ty:?}"),
        }
        json_schema::Type::Type(json_schema::TypeVariant::Record(json_schema::RecordType { attributes, additional_attributes })) => RecordOrContextAttributes { attrs: attributes, additional_attrs: *additional_attributes },
        json_schema::Type::Type(ty) => panic!("expected attributes or context to be a record, got {ty:?}"),
    }
}

/// Given a [`json_schema::EntityAttributes`], get the [`EntityAttributes`]
/// describing it
pub(crate) fn attrs_from_ea(
    schema: &json_schema::NamespaceDefinition<ast::InternalName>,
    ea: &json_schema::EntityAttributes<ast::InternalName>,
) -> EntityAttributes {
    match ea {
        json_schema::EntityAttributes::RecordAttributes(rca) => {
            let RecordOrContextAttributes {
                attrs,
                additional_attrs,
            } = attrs_from_rca(schema, rca);
            EntityAttributes {
                attrs: attrs
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            json_schema::EntityAttributeType {
                                ty: json_schema::EntityAttributeTypeInternal::Type(v.ty.clone()),
                                required: v.required,
                            },
                        )
                    })
                    .collect(),
                additional_attrs,
            }
        }
        json_schema::EntityAttributes::EntityAttributes(
            json_schema::EntityAttributesInternal {
                attrs:
                    json_schema::RecordType {
                        attributes,
                        additional_attributes,
                    },
                ..
            },
        ) => EntityAttributes {
            attrs: attributes
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
                .collect(),
            additional_attrs: *additional_attributes,
        },
    }
}

/// Given a [`json_schema::EntityAttributes`], get just the attribute names in it
pub(crate) fn attr_names_from_ea<'a>(
    schema: &'a json_schema::NamespaceDefinition<ast::InternalName>,
    ea: &'a json_schema::EntityAttributes<ast::InternalName>,
) -> Box<dyn Iterator<Item = SmolStr> + 'a> {
    match ea {
        json_schema::EntityAttributes::RecordAttributes(rca) => {
            let attrs = attrs_from_rca(schema, rca);
            Box::new(attrs.attrs.keys().cloned())
        }
        json_schema::EntityAttributes::EntityAttributes(rty) => {
            Box::new(rty.attrs.attributes.keys().cloned())
        }
    }
}

/// Given a [`json_schema::Type`], return all (attribute, type) pairs that occur
/// inside it
fn attrs_in_schematype(
    schema: &json_schema::NamespaceDefinition<ast::InternalName>,
    schematype: &json_schema::Type<ast::InternalName>,
) -> Box<
    dyn Iterator<
        Item = (
            SmolStr,
            json_schema::EntityAttributeTypeInternal<ast::InternalName>,
        ),
    >,
> {
    match schematype {
        json_schema::Type::Type(variant) => match variant {
            json_schema::TypeVariant::Boolean => Box::new(std::iter::empty()),
            json_schema::TypeVariant::Long => Box::new(std::iter::empty()),
            json_schema::TypeVariant::String => Box::new(std::iter::empty()),
            json_schema::TypeVariant::Entity { .. } => Box::new(std::iter::empty()),
            json_schema::TypeVariant::EntityOrCommon { type_name } => {
                match lookup_common_type(schema, type_name) {
                    Some(ty) => attrs_in_schematype(schema, ty),
                    None => {
                        // it's an entity type, so treat it like we treat entity types
                        attrs_in_schematype(
                            schema,
                            &json_schema::Type::Type(json_schema::TypeVariant::Entity {
                                name: type_name.clone(),
                            }),
                        )
                    }
                }
            }
            json_schema::TypeVariant::Extension { .. } => Box::new(std::iter::empty()),
            json_schema::TypeVariant::Set { element } => attrs_in_schematype(schema, element),
            json_schema::TypeVariant::Record(json_schema::RecordType { attributes, .. }) => {
                let toplevel = attributes
                    .iter()
                    .map(|(k, v)| {
                        (
                            k.clone(),
                            json_schema::EntityAttributeTypeInternal::Type(v.ty.clone()),
                        )
                    })
                    .collect::<Vec<_>>();
                let recursed = toplevel
                    .iter()
                    .flat_map(|(_, v)| attrs_in_eatypeinternal(schema, v))
                    .collect::<Vec<_>>();
                Box::new(toplevel.into_iter().chain(recursed))
            }
        },
        json_schema::Type::CommonTypeRef { type_name } => attrs_in_schematype(
            schema,
            lookup_common_type(schema, type_name)
                .unwrap_or_else(|| panic!("reference to undefined common type: {type_name}")),
        ),
    }
}

/// Given a [`json_schema::EntityType`], return all (attribute,
/// type) pairs that occur inside it
fn attrs_in_etype(
    schema: &json_schema::NamespaceDefinition<ast::InternalName>,
    etype: &json_schema::EntityType<ast::InternalName>,
) -> Box<
    dyn Iterator<
        Item = (
            SmolStr,
            json_schema::EntityAttributeTypeInternal<ast::InternalName>,
        ),
    >,
> {
    match &etype.shape {
        json_schema::EntityAttributes::RecordAttributes(
            json_schema::RecordOrContextAttributes(ty),
        ) => attrs_in_schematype(schema, ty),
        json_schema::EntityAttributes::EntityAttributes(
            json_schema::EntityAttributesInternal {
                attrs: json_schema::RecordType { attributes, .. },
                ..
            },
        ) => {
            let toplevel = attributes
                .iter()
                .map(|(k, v)| (k.clone(), v.ty.clone()))
                .collect::<Vec<_>>();
            let recursed = toplevel
                .iter()
                .flat_map(|(_, v)| attrs_in_eatypeinternal(schema, v))
                .collect::<Vec<_>>();
            Box::new(toplevel.into_iter().chain(recursed))
        }
    }
}

/// Given a [`json_schema::EntityAttributeTypeInternal`], return all
/// (attribute, type) pairs that occur inside it
fn attrs_in_eatypeinternal(
    schema: &json_schema::NamespaceDefinition<ast::InternalName>,
    eatypeinternal: &json_schema::EntityAttributeTypeInternal<ast::InternalName>,
) -> Box<
    dyn Iterator<
        Item = (
            SmolStr,
            json_schema::EntityAttributeTypeInternal<ast::InternalName>,
        ),
    >,
> {
    match eatypeinternal {
        json_schema::EntityAttributeTypeInternal::Type(ty) => attrs_in_schematype(schema, ty),
        json_schema::EntityAttributeTypeInternal::EAMap { value_type } => {
            // we can't return any attributes from the EAMap itself because we
            // are not guaranteed that any particular attribute names exist
            attrs_in_schematype(schema, value_type)
        }
    }
}

/// Build `attributes_by_type` from other components of `Schema`
fn build_attributes_by_type<'a>(
    schema: &json_schema::NamespaceDefinition<ast::InternalName>,
    entity_types: impl IntoIterator<
        Item = (
            &'a UnreservedId,
            &'a json_schema::EntityType<ast::InternalName>,
        ),
    >,
    namespace: Option<&ast::Name>,
) -> HashMap<Type, Vec<(ast::EntityType, SmolStr)>> {
    let triples = entity_types
        .into_iter()
        .map(|(name, et)| {
            (
                ast::EntityType::from(ast::Name::from(name.clone())).qualify_with(namespace),
                attrs_from_ea(schema, &et.shape),
            )
        })
        .flat_map(|(tyname, attributes)| {
            attributes
                .attrs
                .iter()
                .map(move |(attr_name, ty)| {
                    (
                        eatypeinternal_to_type(schema, &ty.ty),
                        (tyname.clone(), attr_name.clone()),
                    )
                })
                .collect::<Vec<_>>()
        });
    let mut hm: HashMap<Type, Vec<(ast::EntityType, SmolStr)>> = HashMap::new();
    for (ty, pair) in triples {
        hm.entry(ty).or_default().push(pair);
    }
    hm
}

// Common type bindings
#[derive(Debug)]
struct Bindings {
    // Bindings from `json_schema::Type` to a list of `UnreservedId`.
    // The `ids` field ensures that `UnreservedId`s are unique.
    // Note that the `json_schema::Type`s in the `bindings` map should not
    // contain any common type references.
    bindings: BTreeMap<json_schema::Type<ast::InternalName>, Vec<CommonTypeId>>,
    // The set of `UnreservedId`s used in the bindings
    ids: HashSet<SmolStr>,
}
impl Bindings {
    fn new() -> Self {
        Self {
            bindings: BTreeMap::new(),
            ids: HashSet::new(),
        }
    }

    // Add a `json_schema::Type` and `UnreservedId` binding.
    // Note that this function always succeeds even if the `UnreservedId` already exists.
    // Under that situation, we create a new `UnreservedId` based on the existing `UnreservedId`.
    fn add_binding(&mut self, binding: (json_schema::Type<ast::InternalName>, CommonTypeId)) {
        let (ty, id) = binding;
        let id: UnreservedId = id.into();
        // create a new id when the provided id has been used
        let id_smolstr: &str = id.as_ref();
        let new_id = if self.ids.contains(id_smolstr) {
            let mut new_id = id.to_string();
            while self.ids.contains(new_id.as_str()) {
                new_id.push('_');
                new_id.push('_');
                new_id.push('_');
            }
            new_id.parse().unwrap()
        } else {
            id
        };
        // `new_id` must be a valid `CommonTypeId`
        let new_id = CommonTypeId::unchecked(new_id);

        self.ids.insert(new_id.clone().to_smolstr());
        if let Some(binding_for_ty) = self.bindings.get_mut(&ty) {
            binding_for_ty.push(new_id);
        } else {
            self.bindings.insert(ty, vec![new_id]);
        }
    }

    // Replace types with common type references.
    // We only replace smaller types in composite types like sets and records
    // to avoid circularity.
    // This function is a no-op for other types.
    fn rewrite_type(
        &self,
        u: &mut Unstructured<'_>,
        ty: &json_schema::Type<ast::InternalName>,
    ) -> Result<json_schema::Type<ast::InternalName>> {
        match ty {
            json_schema::Type::CommonTypeRef { .. } => {
                unreachable!("common type references shouldn't be here")
            }
            json_schema::Type::Type(json_schema::TypeVariant::Set { element }) => {
                Ok(json_schema::Type::Type(json_schema::TypeVariant::Set {
                    element: Box::new(if let Some(ids) = self.bindings.get(element) {
                        json_schema::Type::CommonTypeRef {
                            type_name: ast::Name::unqualified_name(u.choose(ids)?.clone().into())
                                .into(),
                        }
                    } else {
                        self.rewrite_type(u, element)?
                    }),
                }))
            }
            json_schema::Type::Type(json_schema::TypeVariant::Record(
                json_schema::RecordType {
                    attributes,
                    additional_attributes,
                },
            )) => Ok(json_schema::Type::Type(json_schema::TypeVariant::Record(
                json_schema::RecordType {
                    attributes: BTreeMap::from_iter(
                        attributes
                            .iter()
                            .map(|(attr, attr_ty)| {
                                Ok((
                                    attr.to_owned(),
                                    json_schema::RecordAttributeType {
                                        ty: self.rewrite_type(u, &attr_ty.ty)?,
                                        required: attr_ty.required.to_owned(),
                                    },
                                ))
                            })
                            .collect::<Result<Vec<_>>>()?,
                    ),
                    additional_attributes: additional_attributes.to_owned(),
                },
            ))),
            _ => Ok(ty.clone()),
        }
    }

    /// Replace attribute types in an entity type with common types
    fn rewrite_entity_type(
        &self,
        u: &mut Unstructured<'_>,
        et: &json_schema::EntityType<ast::InternalName>,
    ) -> Result<json_schema::EntityType<ast::InternalName>> {
        Ok(json_schema::EntityType {
            member_of_types: et.member_of_types.clone(),
            shape: self.rewrite_entity_attributes(u, &et.shape)?,
        })
    }

    /// Replace attribute types in a [`json_schema::EntityAttributes`] with common types
    fn rewrite_entity_attributes(
        &self,
        u: &mut Unstructured<'_>,
        ea: &json_schema::EntityAttributes<ast::InternalName>,
    ) -> Result<json_schema::EntityAttributes<ast::InternalName>> {
        match ea {
            json_schema::EntityAttributes::RecordAttributes(attrs) => Ok(
                json_schema::EntityAttributes::RecordAttributes(self.rewrite_rca(u, attrs)?),
            ),
            json_schema::EntityAttributes::EntityAttributes(attrs) => Ok(
                json_schema::EntityAttributes::from(self.rewrite_record_type(u, &attrs.attrs)?),
            ),
        }
    }

    /// Replace attribute types in a [`json_schema::RecordOrContextAttributes`] with common types
    fn rewrite_rca(
        &self,
        u: &mut Unstructured<'_>,
        rca: &json_schema::RecordOrContextAttributes<ast::InternalName>,
    ) -> Result<json_schema::RecordOrContextAttributes<ast::InternalName>> {
        Ok(json_schema::RecordOrContextAttributes(
            self.rewrite_or_replace_type(u, &rca.0)?,
        ))
    }

    fn rewrite_record_type(
        &self,
        u: &mut Unstructured<'_>,
        rty: &json_schema::RecordType<json_schema::EntityAttributeType<ast::InternalName>>,
    ) -> Result<json_schema::RecordType<json_schema::EntityAttributeType<ast::InternalName>>> {
        Ok(json_schema::RecordType {
            attributes: rty
                .attributes
                .iter()
                .map(|(k, v)| Ok((k.clone(), self.rewrite_eatype(u, v)?)))
                .collect::<Result<_>>()?,
            additional_attributes: rty.additional_attributes,
        })
    }

    fn rewrite_eatype(
        &self,
        u: &mut Unstructured<'_>,
        eatype: &json_schema::EntityAttributeType<ast::InternalName>,
    ) -> Result<json_schema::EntityAttributeType<ast::InternalName>> {
        Ok(json_schema::EntityAttributeType {
            ty: self.rewrite_eatypeinternal(u, &eatype.ty)?,
            required: eatype.required,
        })
    }

    fn rewrite_eatypeinternal(
        &self,
        u: &mut Unstructured<'_>,
        eatypeinternal: &json_schema::EntityAttributeTypeInternal<ast::InternalName>,
    ) -> Result<json_schema::EntityAttributeTypeInternal<ast::InternalName>> {
        match eatypeinternal {
            json_schema::EntityAttributeTypeInternal::Type(ty) => {
                Ok(json_schema::EntityAttributeTypeInternal::Type(
                    self.rewrite_or_replace_type(u, ty)?,
                ))
            }
            json_schema::EntityAttributeTypeInternal::EAMap { value_type } => {
                Ok(json_schema::EntityAttributeTypeInternal::EAMap {
                    value_type: self.rewrite_or_replace_type(u, value_type)?,
                })
            }
        }
    }

    /// Replace the type with a common-type reference, or rewrite the type to
    /// possibly replace subcomponents of the type with common-type references
    fn rewrite_or_replace_type(
        &self,
        u: &mut Unstructured<'_>,
        ty: &json_schema::Type<ast::InternalName>,
    ) -> Result<json_schema::Type<ast::InternalName>> {
        if let Some(ids) = self.bindings.get(ty) {
            Ok(json_schema::Type::CommonTypeRef {
                type_name: ast::Name::unqualified_name(u.choose(ids)?.clone().into()).into(),
            })
        } else {
            self.rewrite_type(u, ty)
        }
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
    fn to_common_types(
        &self,
        u: &mut Unstructured<'_>,
    ) -> Result<HashMap<CommonTypeId, json_schema::Type<ast::InternalName>>> {
        let mut common_types = HashMap::new();
        for (ty, ids) in &self.bindings {
            if ids.len() == 1 {
                common_types.insert(ids.first().unwrap().clone(), self.rewrite_type(u, ty)?);
            } else if ids.len() > 1 {
                // ids[0] -> ids[1] -> ... -> ids[n]
                for i in 0..(ids.len() - 1) {
                    common_types.insert(
                        ids[i].clone(),
                        json_schema::Type::CommonTypeRef {
                            type_name: ast::Name::unqualified_name(ids[i + 1].clone().into())
                                .into(),
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
fn bind_type(
    ty: &json_schema::Type<ast::InternalName>,
    u: &mut Unstructured<'_>,
    bindings: &mut Bindings,
) -> Result<()> {
    // flip a coin to decide if we should create a binding for the top-level type
    if u.ratio(1, 2)? {
        bindings.add_binding((ty.clone(), u.arbitrary()?));
    }
    match ty {
        json_schema::Type::Type(json_schema::TypeVariant::Set { element }) => {
            bind_type(element, u, bindings)?;
        }
        json_schema::Type::Type(json_schema::TypeVariant::Record(json_schema::RecordType {
            attributes,
            additional_attributes: _,
        })) => {
            attributes
                .iter()
                .map(|(_, attr_ty)| bind_type(&attr_ty.ty, u, bindings))
                .collect::<Result<Vec<()>>>()?;
        }
        json_schema::Type::CommonTypeRef { .. } => {
            unreachable!("common type references shouldn't exist here")
        }
        _ => {}
    };
    Ok(())
}

impl Schema {
    /// Add common types to the existing schema and return a new schema
    pub fn add_common_types(
        &self,
        u: &mut Unstructured<'_>,
    ) -> Result<json_schema::NamespaceDefinition<ast::InternalName>> {
        let mut bindings = Bindings::new();
        for (_, ty) in &self.attributes {
            if let json_schema::EntityAttributeTypeInternal::Type(ty) = ty {
                bind_type(ty, u, &mut bindings)?;
            }
        }

        let common_types = bindings.to_common_types(u)?;
        let entity_types: HashMap<UnreservedId, json_schema::EntityType<ast::InternalName>> =
            HashMap::from_iter(
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
                        json_schema::ActionType {
                            attributes: ty.attributes.to_owned(),
                            member_of: ty.member_of.clone(),
                            applies_to: match &ty.applies_to {
                                Some(applies) => Some(json_schema::ApplySpec {
                                    resource_types: applies.resource_types.clone(),
                                    principal_types: applies.principal_types.clone(),
                                    context: json_schema::RecordOrContextAttributes(
                                        bindings.rewrite_or_replace_type(u, &applies.context.0)?,
                                    ),
                                }),
                                None => None,
                            },
                        },
                    ))
                })
                .collect::<Result<Vec<_>>>()?,
        );
        Ok(json_schema::NamespaceDefinition {
            common_types: common_types.into(),
            entity_types: entity_types.into(),
            actions: actions.into(),
        })
    }
    /// Get a slice of all of the entity types in this schema
    pub fn entity_types(&self) -> &[ast::EntityType] {
        &self.entity_types
    }

    /// Create an arbitrary `Schema` based on (compatible with) the given
    /// Validator `NamespaceDefinition`.
    ///
    /// The input is `NamespaceDefinition<RawName>`, meaning that entity and
    /// common type names may not yet be fully qualified.
    pub fn from_raw_nsdef(
        nsdef: json_schema::NamespaceDefinition<RawName>,
        namespace: Option<ast::Name>,
        settings: ABACSettings,
        u: &mut Unstructured<'_>,
    ) -> Result<Schema> {
        let namespace_internal: Option<&ast::InternalName> = namespace.as_ref().map(AsRef::as_ref);
        let all_defs = AllDefs::single_fragment(&ValidatorSchemaFragment::from_namespaces([
            ValidatorNamespaceDef::from_namespace_definition(
                namespace.clone().map(Into::into),
                nsdef.clone(),
                ActionBehavior::PermitAttributes,
                Extensions::all_available(),
            )?,
        ]));
        Self::from_nsdef(
            nsdef
                .conditionally_qualify_type_references(namespace_internal)
                .fully_qualify_type_references(&all_defs)
                .unwrap(),
            namespace,
            settings,
            u,
        )
    }

    /// Create an arbitrary [`Schema`] based on (compatible with) the given
    /// [`json_schema::NamespaceDefinition`].
    ///
    /// The input is [`json_schema::NamespaceDefinition<ast::InternalName>`], meaning that all
    /// entity and common type names are expected to already be fully qualified.
    pub fn from_nsdef(
        nsdef: json_schema::NamespaceDefinition<ast::InternalName>,
        namespace: Option<ast::Name>,
        settings: ABACSettings,
        u: &mut Unstructured<'_>,
    ) -> Result<Schema> {
        let mut principal_types = HashSet::new();
        let mut resource_types = HashSet::new();
        for atype in nsdef.actions.values() {
            if let Some(applyspec) = atype.applies_to.as_ref() {
                principal_types.extend(applyspec.principal_types.iter());
                resource_types.extend(applyspec.resource_types.iter());
            }
        }
        let mut attributes = Vec::new();
        for schematype in nsdef.common_types.values() {
            attributes.extend(attrs_in_schematype(&nsdef, schematype));
        }
        for etype in nsdef.entity_types.values() {
            attributes.extend(attrs_in_etype(&nsdef, etype));
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
                .cloned()
                .map(|k| ast::EntityType::from(ast::Name::from(k)))
                .collect(),
            principal_types: principal_types
                .into_iter()
                .cloned()
                .map(|iname| ast::Name::try_from(iname).unwrap().into())
                .collect(),
            actions_eids: nsdef.actions.keys().cloned().map(ast::Eid::new).collect(),
            resource_types: resource_types
                .into_iter()
                .cloned()
                .map(|iname| ast::Name::try_from(iname).unwrap().into())
                .collect(),
            attributes,
            attributes_by_type,
            schema: nsdef,
        })
    }

    /// Create an arbitrary `Schema` based on (compatible with) the given [`json_schema::Fragment`].
    ///
    /// The input is [`json_schema::Fragment<RawName>`], meaning that entity and common
    /// type names may not yet be fully qualified.
    pub fn from_raw_schemafrag(
        schemafrag: json_schema::Fragment<RawName>,
        settings: ABACSettings,
        u: &mut Unstructured<'_>,
    ) -> Result<Schema> {
        let mut nsdefs = schemafrag.0.into_iter();
        match nsdefs.next() {
            None => panic!("Empty json_schema::Fragment not supported in this method"),
            Some((ns, nsdef)) => match nsdefs.next() {
                Some(_) => unimplemented!(
                    "json_schema::Fragment with multiple namespaces not yet supported in this method"
                ),
                None => Self::from_raw_nsdef(nsdef, ns, settings, u),
            },
        }
    }

    /// Create an arbitrary `Schema` based on (compatible with) the given
    /// [`json_schema::Fragment`].
    ///
    /// The input is [`json_schema::Fragment<ast::InternalName>`], meaning that all
    /// entity and common type names are expected to already be fully-qualified.
    pub fn from_schemafrag(
        schemafrag: json_schema::Fragment<ast::InternalName>,
        settings: ABACSettings,
        u: &mut Unstructured<'_>,
    ) -> Result<Schema> {
        let mut nsdefs = schemafrag.0.into_iter();
        match nsdefs.next() {
            None => panic!("Empty json_schema::Fragment not supported in this method"),
            Some((ns, nsdef)) => match nsdefs.next() {
                Some(_) => unimplemented!(
                    "json_schema::Fragment with multiple namespaces not yet supported in this method"
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
        let entity_type_ids: HashSet<ast::UnreservedId> = u
            .arbitrary()
            .map_err(|e| while_doing("generating entity type ids".into(), e))?;
        let entity_type_ids: Vec<ast::UnreservedId> = if entity_type_ids.is_empty() {
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
        let entity_type_names: Vec<ast::EntityType> = entity_type_ids
            .iter()
            .map(|id| {
                ast::EntityType::from(ast::Name::from(id.clone())).qualify_with(namespace.as_ref())
            })
            .collect();

        // now turn each of those names into an EntityType, no
        // member-relationships yet
        let mut entity_types: Vec<(UnreservedId, json_schema::EntityType<ast::InternalName>)> =
            entity_type_ids
                .iter()
                .filter(|id| settings.enable_action_groups_and_attrs || id.to_string() != "Action")
                .map(|id| {
                    Ok((
                        id.clone(),
                        json_schema::EntityType {
                            member_of_types: vec![],
                            shape: arbitrary_entityattributes(&settings, &entity_type_names, u)?,
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
                    let etype = ast::InternalName::from(ast::Name::from(name.clone()));
                    entity_types[i].1.member_of_types.push(etype);
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
        let mut principal_types: HashSet<ast::InternalName> = HashSet::new();
        let mut resource_types: HashSet<ast::InternalName> = HashSet::new();
        // optionally return a list of entity types and add them to `tys` at the same time
        let pick_entity_types = |tys: &mut HashSet<ast::InternalName>,
                                 u: &mut Unstructured<'_>|
         -> Result<Vec<ast::InternalName>> {
            // Pre-select the number of entity types (minimum 1), then randomly select that many indices
            let num = u.int_in_range(1..=entity_types.len()).unwrap();
            let mut indices: Vec<usize> = (0..entity_types.len()).collect();
            let mut selected_indices = Vec::with_capacity(num);

            while selected_indices.len() < num {
                let index = u.choose_index(indices.len()).unwrap();
                selected_indices.push(indices.swap_remove(index));
            }

            Result::Ok(
                selected_indices
                    .iter()
                    .map(|&i| {
                        let (name, _) = &entity_types[i];
                        let etyp = ast::InternalName::from(ast::Name::from(name.clone()));
                        tys.insert(etyp.qualify_with_name(namespace.as_ref()));
                        etyp
                    })
                    .collect::<Vec<ast::InternalName>>(),
            )
        };
        let mut principal_and_resource_types_exist = false;
        // Ensure on the first pass we always generate a principal/resource
        // After that, flip a coin to optional delete the principal/resource type lists
        let mut actions: Vec<(SmolStr, json_schema::ActionType<ast::InternalName>)> = action_names
            .iter()
            .map(|name| {
                Ok((
                    name.clone(),
                    json_schema::ActionType {
                        applies_to: {
                            let mut picked_resource_types =
                                pick_entity_types(&mut resource_types, u)?;
                            let mut picked_principal_types =
                                pick_entity_types(&mut principal_types, u)?;
                            if principal_and_resource_types_exist {
                                if u.ratio(1, 8)? {
                                    picked_principal_types.clear();
                                }
                                if u.ratio(1, 8)? {
                                    picked_resource_types.clear();
                                }
                            } else {
                                principal_and_resource_types_exist = true;
                            }
                            Some(json_schema::ApplySpec {
                                resource_types: picked_resource_types,
                                principal_types: picked_principal_types,
                                context: arbitrary_rca(&settings, &entity_type_names, u)?,
                            })
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
                            .push(
                                json_schema::ActionEntityUID::default_type(name.clone())
                                    .qualify_with(namespace.as_ref().map(AsRef::as_ref)),
                            );
                    }
                }
            }
        }

        let nsdef = json_schema::NamespaceDefinition {
            common_types: HashMap::new().into(),
            entity_types: entity_types.into_iter().collect(),
            actions: actions.into_iter().collect(),
        };
        let entity_attributes = nsdef
            .entity_types
            .values()
            .map(|et| attrs_from_ea(&nsdef, &et.shape))
            .flat_map(|attrs| {
                attrs.attrs.into_iter().map(|(s, ty)| {
                    (
                        s.parse().expect("attribute names should be valid Ids"),
                        ty.ty,
                    )
                })
            });
        let context_attributes = nsdef
            .actions
            .iter()
            .filter_map(|(_, action)| action.applies_to.as_ref())
            .map(|a| attrs_from_rca(&nsdef, &a.context))
            .flat_map(|attrs| {
                attrs.attrs.into_iter().map(|(s, ty)| {
                    (
                        s.parse().expect("attribute names should be valid Ids"),
                        json_schema::EntityAttributeTypeInternal::Type(ty.ty.clone()),
                    )
                })
            });
        let attributes: Vec<(SmolStr, json_schema::EntityAttributeTypeInternal<_>)> =
            entity_attributes.chain(context_attributes).collect();
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
            principal_types: principal_types
                .into_iter()
                .map(|ptype| ast::Name::try_from(ptype).unwrap().into())
                .collect(),
            actions_eids,
            resource_types: resource_types
                .into_iter()
                .map(|rtype| ast::Name::try_from(rtype).unwrap().into())
                .collect(),
            attributes,
            attributes_by_type,
        })
    }
    /// size hint for arbitrary()
    pub fn arbitrary_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <HashSet<ast::Name> as Arbitrary>::size_hint(depth),
            arbitrary_rca_size_hint(depth), // actually we do one of these per Name that was generated
            size_hint_for_ratio(1, 2),      // actually many of these calls
            <HashSet<String> as Arbitrary>::size_hint(depth),
            size_hint_for_ratio(1, 8), // actually many of these calls
            size_hint_for_ratio(1, 4), // zero to many of these calls
            size_hint_for_ratio(1, 2), // zero to many of these calls
            arbitrary_rca_size_hint(depth),
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

    #[allow(dead_code)]
    fn arbitrary_uid_with_etype(
        &self,
        ty_name: &ast::EntityType,
        hierarchy: Option<&Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        let ty = ty_name.qualify_with(self.namespace());
        self.exprgenerator(hierarchy)
            .arbitrary_uid_with_type(&ty, u)
    }

    /// Like `arbitrary_uid_with_etype`, but takes the entity type as `ast::Name`
    fn arbitrary_uid_with_etype_as_name(
        &self,
        ty_name: &ast::Name,
        hierarchy: Option<&Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        let ty = ty_name.qualify_with_name(self.namespace()).into();
        self.exprgenerator(hierarchy)
            .arbitrary_uid_with_type(&ty, u)
    }

    /// internal helper function, try to convert [`Type`] into [`json_schema::Type`]
    pub fn try_into_schematype<N: From<ast::Name>>(
        &self,
        ty: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<Option<json_schema::Type<N>>> {
        Ok(match ty {
            Type::Bool => Some(json_schema::TypeVariant::Boolean),
            Type::Long => Some(json_schema::TypeVariant::Long),
            Type::String => Some(json_schema::TypeVariant::String),
            Type::Set(None) => None, // json_schema::Type doesn't support any-set
            Type::Set(Some(el_ty)) => {
                self.try_into_schematype(el_ty, u)?
                    .map(|schematy| json_schema::TypeVariant::Set {
                        element: Box::new(schematy),
                    })
            }
            Type::Record => Some(json_schema::TypeVariant::Record(json_schema::RecordType {
                attributes: BTreeMap::new(),
                additional_attributes: true,
            })),
            Type::Entity => {
                let entity_type = self.exprgenerator(None).generate_uid(u)?.components().0;
                Some(entity_type_name_to_schema_type_variant(&entity_type))
            }
            Type::IPAddr => Some(json_schema::TypeVariant::Extension {
                name: "ipaddr".parse().unwrap(),
            }),
            Type::Decimal => Some(json_schema::TypeVariant::Extension {
                name: "decimal".parse().unwrap(),
            }),
        }
        .map(json_schema::Type::Type))
    }

    /// get an attribute name and its attribute type, from the schema
    pub fn arbitrary_attr(
        &self,
        u: &mut Unstructured<'_>,
    ) -> Result<&(
        SmolStr,
        json_schema::EntityAttributeTypeInternal<ast::InternalName>,
    )> {
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
    ) -> Result<&(ast::EntityType, SmolStr)> {
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

    /// Given a [`json_schema::Type`], get an entity type name and attribute
    /// name, such that entities with that typename have a (possibly optional)
    /// attribute with the given [`json_schema::Type`]
    pub fn arbitrary_attr_for_schematype(
        &self,
        target_type: impl Into<json_schema::Type<ast::InternalName>>,
        u: &mut Unstructured<'_>,
    ) -> Result<(ast::EntityType, SmolStr)> {
        let target_type: json_schema::Type<ast::InternalName> = target_type.into();
        let pairs: Vec<(ast::EntityType, SmolStr)> = self
            .schema
            .entity_types
            .iter()
            .map(|(name, et)| {
                (
                    ast::EntityType::from(ast::Name::from(name.clone()))
                        .qualify_with(self.namespace()),
                    attrs_from_ea(&self.schema, &et.shape),
                )
            })
            .flat_map(|(tyname, attributes)| {
                attributes
                    .attrs
                    .into_iter()
                    .filter(|(_, ty)| matches!(&ty.ty, json_schema::EntityAttributeTypeInternal::Type(t) if t == &target_type))
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
        let applicable_actions: Vec<_> = self
            .schema
            .actions
            .iter()
            .filter(|(_, action)| action.applies_to.is_some())
            .collect();
        let (action_name, action) = applicable_actions[u.choose_index(applicable_actions.len())?];
        // This is safe as we checked above
        let applies_to: &json_schema::ApplySpec<ast::InternalName> =
            action.applies_to.as_ref().unwrap();
        // now generate a valid request for that Action
        Ok(ABACRequest(Request {
            principal: {
                let types = &applies_to.principal_types;
                let ty = u.choose(types).map_err(|e| {
                    while_doing("choosing one of the action principal types".into(), e)
                })?;
                self.arbitrary_uid_with_etype_as_name(ty.try_into().unwrap(), Some(hierarchy), u)?
            },
            action: uid_for_action_name(
                self.namespace.as_ref(),
                ast::Eid::new(action_name.clone()),
            ),
            resource: {
                // Assert that these are vec, so it's safe to draw from directly
                let types = &applies_to.resource_types;
                let ty = u.choose(types).map_err(|e| {
                    while_doing("choosing one of the action resource types".into(), e)
                })?;
                self.arbitrary_uid_with_etype_as_name(ty.try_into().unwrap(), Some(hierarchy), u)?
            },
            context: {
                let mut attributes: Vec<_> = action
                    .applies_to
                    .as_ref()
                    .map(|a| attrs_from_rca(&self.schema, &a.context))
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
    pub fn schemafile(&self) -> &json_schema::NamespaceDefinition<ast::InternalName> {
        &self.schema
    }

    /// Get the underlying schema file, as a String containing JSON
    pub fn schemafile_string(&self) -> String {
        serde_json::to_string_pretty(&self.schema)
            .expect("failed to serialize schema NamespaceDefinition")
    }
}

impl From<Schema> for json_schema::Fragment<ast::InternalName> {
    fn from(schema: Schema) -> json_schema::Fragment<ast::InternalName> {
        json_schema::Fragment(HashMap::from_iter([(schema.namespace, schema.schema)]).into())
    }
}

impl From<Schema> for json_schema::Fragment<RawName> {
    fn from(schema: Schema) -> json_schema::Fragment<RawName> {
        downgrade_frag_to_raw(json_schema::Fragment::<ast::InternalName>::from(schema))
    }
}

/// Utility function to "downgrade" a [`json_schema::Fragment`] with fully-qualified
/// names into one with [`RawName`]s.
/// When this results in `RawName`s like `A::B`, this is unambiguous, because
/// the `RawName` `A::B` is always translated back into the fully-qualified
/// `A::B`.
/// When this results in `RawName`s like `A` (because the fully-qualified name
/// was in the empty namespace), this is potentially ambiguous, because this
/// could be turned back into a fully-qualified `Name` like `C::A`, if the
/// reference is part of `namespace C` and `C::A` exists (and once cedar#579 is
/// fixed). However, we can't do any better, because there is currently no way
/// for a `RawName` to unambiguously refer to a name in the empty namespace;
/// solutions are discussed in RFC 64 (which is `pending` as of this writing).
pub fn downgrade_frag_to_raw(
    frag: json_schema::Fragment<ast::InternalName>,
) -> json_schema::Fragment<RawName> {
    json_schema::Fragment(
        frag.0
            .into_iter()
            .map(|(k, nsdef)| (k, downgrade_nsdef_to_raw(nsdef)))
            .collect(),
    )
}

/// Utility function to "downgrade" a [`NamespaceDefinition`] with fully-qualified
/// names into one with [`RawName`]s. See notes on [`downgrade_frag_to_raw()`].
fn downgrade_nsdef_to_raw(
    nsdef: json_schema::NamespaceDefinition<ast::InternalName>,
) -> json_schema::NamespaceDefinition<RawName> {
    json_schema::NamespaceDefinition {
        common_types: nsdef
            .common_types
            .into_iter()
            .map(|(k, v)| (k, downgrade_schematype_to_raw(v)))
            .collect(),
        entity_types: nsdef
            .entity_types
            .into_iter()
            .map(|(k, v)| (k, downgrade_entitytype_to_raw(v)))
            .collect(),
        actions: nsdef
            .actions
            .into_iter()
            .map(|(k, v)| (k, downgrade_action_to_raw(v)))
            .collect(),
    }
}

/// Utility function to "downgrade" a [`json_schema::Type`] with fully-qualified names
/// into one with [`RawName`]s. See notes on [`downgrade_frag_to_raw()`].
fn downgrade_schematype_to_raw(
    schematype: json_schema::Type<ast::InternalName>,
) -> json_schema::Type<RawName> {
    match schematype {
        json_schema::Type::CommonTypeRef { type_name } => json_schema::Type::CommonTypeRef {
            type_name: RawName::from_name(type_name),
        },
        json_schema::Type::Type(stv) => {
            json_schema::Type::Type(downgrade_schematypevariant_to_raw(stv))
        }
    }
}

/// Utility function to "downgrade" a [`json_schema::TypeVariant`] with fully-qualified
/// names into one with [`RawName`]s. See notes on [`downgrade_frag_to_raw()`].
fn downgrade_schematypevariant_to_raw(
    stv: json_schema::TypeVariant<ast::InternalName>,
) -> json_schema::TypeVariant<RawName> {
    match stv {
        json_schema::TypeVariant::Boolean => json_schema::TypeVariant::Boolean,
        json_schema::TypeVariant::Long => json_schema::TypeVariant::Long,
        json_schema::TypeVariant::String => json_schema::TypeVariant::String,
        json_schema::TypeVariant::Extension { name } => {
            json_schema::TypeVariant::Extension { name }
        }
        json_schema::TypeVariant::Set { element } => json_schema::TypeVariant::Set {
            element: Box::new(downgrade_schematype_to_raw(*element)),
        },
        json_schema::TypeVariant::Entity { name } => json_schema::TypeVariant::Entity {
            name: RawName::from_name(name),
        },
        json_schema::TypeVariant::EntityOrCommon { type_name } => {
            json_schema::TypeVariant::EntityOrCommon {
                type_name: RawName::from_name(type_name),
            }
        }
        json_schema::TypeVariant::Record(json_schema::RecordType {
            attributes,
            additional_attributes,
        }) => json_schema::TypeVariant::Record(json_schema::RecordType {
            attributes: attributes
                .into_iter()
                .map(|(k, v)| (k, downgrade_rat_to_raw(v)))
                .collect(),
            additional_attributes,
        }),
    }
}

/// Utility function to "downgrade" a [`json_schema::RecordAttributeType`] with fully-qualified
/// names into one with [`RawName`]s. See notes on [`downgrade_frag_to_raw()`].
fn downgrade_rat_to_raw(
    rat: json_schema::RecordAttributeType<ast::InternalName>,
) -> json_schema::RecordAttributeType<RawName> {
    json_schema::RecordAttributeType {
        ty: downgrade_schematype_to_raw(rat.ty),
        required: rat.required,
    }
}

/// Utility function to "downgrade" a [`json_schema::EntityType`] with
/// fully-qualified names into one with [`RawName`]s. See notes on
/// [`downgrade_frag_to_raw()`].
fn downgrade_entitytype_to_raw(
    entitytype: json_schema::EntityType<ast::InternalName>,
) -> json_schema::EntityType<RawName> {
    json_schema::EntityType {
        member_of_types: entitytype
            .member_of_types
            .into_iter()
            .map(RawName::from_name)
            .collect(),
        shape: downgrade_ea_to_raw(entitytype.shape),
    }
}

/// Utility function to "downgrade" a [`json_schema::RecordOrContextAttributes`]
/// with fully-qualified names into one with [`RawName`]s. See notes on
/// [`downgrade_frag_to_raw()`].
fn downgrade_rca_to_raw(
    rca: json_schema::RecordOrContextAttributes<ast::InternalName>,
) -> json_schema::RecordOrContextAttributes<RawName> {
    json_schema::RecordOrContextAttributes(downgrade_schematype_to_raw(rca.0))
}

/// Utility function to "downgrade" a [`json_schema::EntityAttributes`]
/// with fully-qualified names into one with [`RawName`]s. See notes on
/// [`downgrade_frag_to_raw()`].
fn downgrade_ea_to_raw(
    ea: json_schema::EntityAttributes<ast::InternalName>,
) -> json_schema::EntityAttributes<RawName> {
    match ea {
        json_schema::EntityAttributes::RecordAttributes(rca) => {
            json_schema::EntityAttributes::RecordAttributes(downgrade_rca_to_raw(rca))
        }
        json_schema::EntityAttributes::EntityAttributes(
            json_schema::EntityAttributesInternal { attrs, .. },
        ) => downgrade_rty_to_raw(attrs).into(),
    }
}

/// Utility function to "downgrade" a [`json_schema::RecordType`]
/// with fully-qualified names into one with [`RawName`]s.
/// See notes on [`downgrade_frag_to_raw()`].
fn downgrade_rty_to_raw(
    rty: json_schema::RecordType<json_schema::EntityAttributeType<ast::InternalName>>,
) -> json_schema::RecordType<json_schema::EntityAttributeType<RawName>> {
    json_schema::RecordType {
        attributes: rty
            .attributes
            .into_iter()
            .map(|(k, v)| (k, downgrade_eatype_to_raw(v)))
            .collect(),
        additional_attributes: rty.additional_attributes,
    }
}

/// Utility function to "downgrade" a [`json_schema::EntityAttributeType`]
/// with fully-qualified names into one with [`RawName`]s.
/// See notes on [`downgrade_frag_to_raw()`].
fn downgrade_eatype_to_raw(
    eatype: json_schema::EntityAttributeType<ast::InternalName>,
) -> json_schema::EntityAttributeType<RawName> {
    json_schema::EntityAttributeType {
        ty: downgrade_eatypeinternal_to_raw(eatype.ty),
        required: eatype.required,
    }
}

/// Utility function to "downgrade" a [`json_schema::EntityAttributeTypeInternal`]
/// with fully-qualified names into one with [`RawName`]s.
/// See notes on [`downgrade_frag_to_raw()`].
fn downgrade_eatypeinternal_to_raw(
    eatypeinternal: json_schema::EntityAttributeTypeInternal<ast::InternalName>,
) -> json_schema::EntityAttributeTypeInternal<RawName> {
    match eatypeinternal {
        json_schema::EntityAttributeTypeInternal::Type(ty) => {
            json_schema::EntityAttributeTypeInternal::Type(downgrade_schematype_to_raw(ty))
        }
        json_schema::EntityAttributeTypeInternal::EAMap { value_type } => {
            json_schema::EntityAttributeTypeInternal::EAMap {
                value_type: downgrade_schematype_to_raw(value_type),
            }
        }
    }
}

/// Utility function to "downgrade" an [`ActionType`] with fully-qualified names
/// into one with [`RawName`]s. See notes on [`downgrade_frag_to_raw()`].
fn downgrade_action_to_raw(
    action: json_schema::ActionType<ast::InternalName>,
) -> json_schema::ActionType<RawName> {
    json_schema::ActionType {
        attributes: action.attributes,
        applies_to: action.applies_to.map(downgrade_applyspec_to_raw),
        member_of: action
            .member_of
            .map(|v| v.into_iter().map(downgrade_aeuid_to_raw).collect()),
    }
}

/// Utility function to "downgrade" an [`ApplySpec`] with fully-qualified names
/// into one with [`RawName`]s. See notes on [`downgrade_frag_to_raw()`].
fn downgrade_applyspec_to_raw(
    applyspec: json_schema::ApplySpec<ast::InternalName>,
) -> json_schema::ApplySpec<RawName> {
    json_schema::ApplySpec {
        principal_types: applyspec
            .principal_types
            .into_iter()
            .map(RawName::from_name)
            .collect(),
        resource_types: applyspec
            .resource_types
            .into_iter()
            .map(RawName::from_name)
            .collect(),
        context: downgrade_rca_to_raw(applyspec.context),
    }
}

/// Utility function to "downgrade" an [`ActionEntityUID`] with fully-qualified
/// names into one with [`RawName`]s. See notes on [`downgrade_frag_to_raw()`].
fn downgrade_aeuid_to_raw(
    aeuid: json_schema::ActionEntityUID<ast::InternalName>,
) -> json_schema::ActionEntityUID<RawName> {
    json_schema::ActionEntityUID::new(
        Some(RawName::from_name(aeuid.ty().clone().into())),
        aeuid.id,
    )
}

impl TryFrom<Schema> for ValidatorSchema {
    type Error = SchemaError;
    fn try_from(schema: Schema) -> std::result::Result<ValidatorSchema, Self::Error> {
        ValidatorSchema::try_from(json_schema::Fragment::<RawName>::from(schema))
    }
}

#[cfg(test)]
mod tests {
    use super::Schema;
    use crate::{hierarchy::EntityUIDGenMode, settings::ABACSettings};
    use arbitrary::Unstructured;
    use cedar_policy_core::entities::Entities;
    use cedar_policy_core::extensions::Extensions;
    use cedar_policy_validator::{json_schema, CoreSchema, RawName, ValidatorSchema};
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
        let fragment = json_schema::Fragment::from_json_file(GITHUB_SCHEMA_STR.as_bytes())
            .expect("schema str should be valid!");
        let mut rng = thread_rng();
        for _ in 0..ITERATION {
            assert!(generate_hierarchy_from_schema(&mut rng, fragment.clone()).is_ok());
        }
    }

    #[test]
    fn entities_generation_document_cloud() {
        let fragment = json_schema::Fragment::from_json_file(DOCUMENT_CLOUD_SCHEMA_STR.as_bytes())
            .expect("schema str should be valid!");
        let mut rng = thread_rng();
        for _ in 0..ITERATION {
            assert!(generate_hierarchy_from_schema(&mut rng, fragment.clone()).is_ok());
        }
    }

    fn generate_hierarchy_from_schema(
        rng: &mut ThreadRng,
        fragment: json_schema::Fragment<RawName>,
    ) -> cedar_policy_core::entities::err::Result<Entities> {
        let mut bytes = [0; RANDOM_BYTE_SIZE as usize];
        rng.fill_bytes(&mut bytes);
        let mut u = Unstructured::new(&bytes);
        let schema = Schema::from_raw_schemafrag(fragment.clone(), TEST_SETTINGS, &mut u)
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
