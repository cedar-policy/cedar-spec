use super::abac::{
    ABACPolicy, ABACRequest, ABACSettings, AttrValue, AvailableExtensionFunctions, ConstantPool,
    Type, UnknownPool,
};
use super::{while_doing, ActionConstraint, Error, PrincipalOrResourceConstraint, Result};
use crate::collections::{HashMap, HashSet};
use amzn_cedar_core::ast::Value;
use amzn_cedar_core::parser::parse_name;
use amzn_cedar_core::{ast, parser};
use amzn_cedar_validator::{
    ActionType, ApplySpec, AttributesOrContext, EntityType, NamespaceDefinition, SchemaFragment,
    TypeOfAttribute,
};
use ast::{Effect, PolicyID};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use smol_str::SmolStr;
use std::collections::BTreeMap;
use std::sync::Arc;

/// Contains the schema, but also pools of constants etc
#[derive(Debug, Clone)]
pub struct Schema {
    /// actual underlying schema
    schema: amzn_cedar_validator::NamespaceDefinition,
    /// Namespace for the schema
    namespace: Option<SmolStr>,
    /// settings
    pub settings: ABACSettings,
    /// constant pool
    constant_pool: ConstantPool,
    /// unknown pool
    pub unknown_pool: UnknownPool,
    /// data on available extension functions
    ext_funcs: AvailableExtensionFunctions,
    /// list of all entity types that are declared in the schema. Note that this
    /// may contain an entity type that is not in `principal_types` or
    /// `resource_types`.
    entity_types: Vec<ast::Name>,
    /// list of entity types that occur as a valid principal for at least one
    /// action in the `schema`
    principal_types: Vec<ast::Name>,
    /// list of Eids that exist as a non-`None` actions name for an action in
    /// the schema.
    actions_eids: Vec<SmolStr>,
    /// list of entity types that occur as a valid resource for at least one
    /// action in the `schema`
    resource_types: Vec<ast::Name>,
    /// list of (attribute, type) pairs that occur in the `schema`
    attributes: Vec<(SmolStr, amzn_cedar_validator::SchemaType)>,
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
        .map_err(|e| while_doing("generating attribute names for an attrspec", e))?;
    Ok(AttributesOrContext(amzn_cedar_validator::SchemaType::Type(
        amzn_cedar_validator::SchemaTypeVariant::Record {
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
                    Ok((attr.into(), ty))
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
fn arbitrary_schematype_with_bounded_depth(
    settings: &ABACSettings,
    entity_types: &[ast::Name],
    max_depth: usize,
    u: &mut Unstructured<'_>,
) -> Result<amzn_cedar_validator::SchemaType> {
    use amzn_cedar_validator::SchemaType;
    use amzn_cedar_validator::SchemaTypeVariant;
    Ok(SchemaType::Type(match u.int_in_range::<u8>(1..=8)? {
        1 => SchemaTypeVariant::String,
        2 => SchemaTypeVariant::Long,
        3 => SchemaTypeVariant::Boolean,
        4 => {
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
        }
        5 => {
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
                            .map_err(|e| while_doing("generating attribute names", e))?;
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
        }
        6 => entity_type_name_to_schema_type(u.choose(entity_types)?),
        7 => SchemaTypeVariant::Extension {
            name: "ipaddr".into(),
        },
        8 => SchemaTypeVariant::Extension {
            name: "decimal".into(),
        },
        n => panic!("bad index: {n}"),
    }))
}

/// Convert a `Name` representing an entity type into the corresponding
/// SchemaType for an entity reference with that entity type.
fn entity_type_name_to_schema_type(name: &ast::Name) -> amzn_cedar_validator::SchemaTypeVariant {
    amzn_cedar_validator::SchemaTypeVariant::Entity {
        name: name.to_string().into(),
    }
}

/// size hint for arbitrary_schematype_with_bounded_depth
fn arbitrary_schematype_size_hint(depth: usize) -> (usize, Option<usize>) {
    // assume it's similar to the unbounded-depth version
    <amzn_cedar_validator::SchemaType as Arbitrary>::size_hint(depth)
}

/// internal helper function, get the EntityUID corresponding to the given ActionType
fn uid_for_action_name(namespace: Option<SmolStr>, action_name: &SmolStr) -> ast::EntityUID {
    let namespace_prefix = namespace.map(|ns| format!("{ns}::")).unwrap_or_default();
    format!("{}Action::\"{}\"", namespace_prefix, action_name)
                .parse()
                .unwrap_or_else(|e| panic!("schema actions should all be valid EntityUIDs in this context, but {:?} led to an invalid one: {}", action_name, amzn_cedar_core::parser::err::ParseErrors(e)))
}

/// internal helper function, convert a SchemaType to a Type (loses some
/// information)
fn schematype_to_type(schematy: &amzn_cedar_validator::SchemaType) -> Type {
    use amzn_cedar_validator::SchemaTypeVariant;
    let schematy = unwrap_schema_type(schematy);
    match schematy {
        SchemaTypeVariant::Boolean => Type::bool(),
        SchemaTypeVariant::Long => Type::long(),
        SchemaTypeVariant::String => Type::string(),
        SchemaTypeVariant::Set { element } => Type::set_of(schematype_to_type(element)),
        SchemaTypeVariant::Record { .. } => Type::record(),
        SchemaTypeVariant::Entity { .. } => Type::entity(),
        SchemaTypeVariant::Extension { name } => match name.as_str() {
            "ipaddr" => Type::ipaddr(),
            "decimal" => Type::decimal(),
            _ => panic!("unrecognized extension type: {name:?}"),
        },
    }
}

/// internal helper function, get a SchemaType representing a Record with (at
/// least) one attribute of the specified name and SchemaType.
fn record_schematype_with_attr(
    attr_name: SmolStr,
    attr_type: impl Into<amzn_cedar_validator::SchemaType>,
) -> amzn_cedar_validator::SchemaTypeVariant {
    amzn_cedar_validator::SchemaTypeVariant::Record {
        attributes: [(
            attr_name,
            TypeOfAttribute {
                ty: attr_type.into(),
                required: true,
            },
        )]
        .into_iter()
        .collect(),
        additional_attributes: true,
    }
}

/// Get an arbitrary namespaces for a schema. The namespace may be absent or it
/// may be a string generated from a `Name`.
fn arbitrary_namespace(u: &mut Unstructured<'_>) -> Result<Option<SmolStr>> {
    let namespace: Option<ast::Name> = u
        .arbitrary()
        .map_err(|e| while_doing("generating namespace", e))?;
    Ok(namespace.map(|ns| ns.to_string().into()))
}

// Parse `name` into a `Name`. The result may have a namespace. If it does, keep
// it as is. Otherwise, qualify it with the default namespace if one is provided.
fn parse_name_with_default_namespace(namespace: &Option<SmolStr>, name: &SmolStr) -> ast::Name {
    let schema_entity_type_name = parse_name(name).expect("Valid Name required for entity type.");
    if schema_entity_type_name
        .namespace_components()
        .next()
        .is_none()
        && namespace.is_some()
    {
        build_qualified_entity_type_name(
            namespace.clone(),
            schema_entity_type_name.basename().as_ref(),
        )
    } else {
        schema_entity_type_name
    }
}

/// Given a namespace string and a type base name string, build a fully
/// qualified `Name` parsing `namespace` as a namespace and `name` as an Id and
/// passing these to the `Name` constructor.
fn build_qualified_entity_type_name(namespace: Option<SmolStr>, name: &str) -> ast::Name {
    match build_qualified_entity_type(namespace, Some(name)) {
        ast::EntityType::Concrete(type_name) => type_name,
        ast::EntityType::Unspecified => {
            panic!("Should not have built an unspecified type from `Some(name)`.")
        }
    }
}

/// Given a `SchemaType` unwrap it to retrieve the inner `SchemaTypeVariant`.
/// This is not possible if the `SchemaType` is `TypeDef` instead of `Type`, but
/// we do not yet generate this sort of type.
fn unwrap_schema_type(
    ty: &amzn_cedar_validator::SchemaType,
) -> &amzn_cedar_validator::SchemaTypeVariant {
    if let amzn_cedar_validator::SchemaType::Type(ty) = ty {
        ty
    } else {
        panic!("DRT does not currently generate schema type using type defs, so `unwrap_schema_type` should not fail.")
    }
}

fn unwrap_attrs_or_context(
    attrs: &AttributesOrContext,
) -> (&BTreeMap<SmolStr, TypeOfAttribute>, bool) {
    if let amzn_cedar_validator::SchemaTypeVariant::Record {
        attributes,
        additional_attributes,
    } = unwrap_schema_type(&attrs.0)
    {
        (attributes, *additional_attributes)
    } else {
        panic!("DRT does not currently generate schema entity type attributes or action contexts that are not record types, so `unwrap_attrs_or_context` should not fail.")
    }
}

/// Given a namespace string and a type base name string, build a fully
/// qualified `EntityType` parsing `namespace` as a namespace and `name` as an
/// `Id`. If `name` is `None`, then this builds an unspecified entity type. Use
/// `build_qualified_entity_type_name` if `name` is not `None`.
fn build_qualified_entity_type(namespace: Option<SmolStr>, name: Option<&str>) -> ast::EntityType {
    match name {
        Some(name) => {
            let type_id: ast::Id = name.parse().unwrap_or_else(|_| {
                panic!("Valid name required to build entity type. Got {}", name)
            });
            let type_namespace: Vec<ast::Id> = namespace
                .map(|ns| {
                    parser::parse_namespace(&ns).unwrap_or_else(|_| {
                        panic!("Valid namespace required to build entity type. Got {}", ns)
                    })
                })
                .unwrap_or_default();
            ast::EntityType::Concrete(ast::Name::new(type_id, type_namespace))
        }
        None => ast::EntityType::Unspecified,
    }
}

impl Schema {
    /// Get an arbitrary Schema.
    pub fn arbitrary(settings: ABACSettings, u: &mut Unstructured<'_>) -> Result<Schema> {
        let namespace = arbitrary_namespace(u)?;

        // first generate the pool of names. we generate a set (so there are no
        // duplicates), but then convert it to a Vec (because we want them
        // ordered, even though we want the order to be arbitrary)
        let entity_type_ids: HashSet<ast::Id> = u
            .arbitrary()
            .map_err(|e| while_doing("generating entity type ids", e))?;
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
            .map(|id| build_qualified_entity_type_name(namespace.clone(), id.as_ref()))
            .collect();

        // now turn each of those names into an EntityType, no
        // member-relationships yet
        let mut entity_types: Vec<(SmolStr, EntityType)> = entity_type_ids
            .iter()
            .filter(|id| settings.enable_action_groups_and_attrs || id.to_string() != "Action")
            .map(|id| {
                Ok((
                    id.into(),
                    EntityType {
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
                    entity_types[i].1.member_of_types.push(name.into());
                }
            }
        }

        // same for actions
        let action_names: HashSet<String> = u
            .arbitrary()
            .map_err(|e| while_doing("generating action names", e))?;
        let action_names: HashSet<SmolStr> = action_names.into_iter().map(SmolStr::from).collect();
        let action_names: Vec<SmolStr> = action_names
            .into_iter()
            // TODO: we just don't want to deal with escaping right now
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
        let mut principal_types = HashSet::new();
        let mut resource_types = HashSet::new();
        let mut actions: Vec<(SmolStr, ActionType)> = action_names
            .iter()
            .map(|name| {
                Ok((
                    name.clone(),
                    ActionType {
                        applies_to: if u.ratio::<u8>(1, 8)? {
                            // The action applies to an unspecified principal
                            // and resource, and no other entity types.
                            None
                        } else {
                            Some(ApplySpec {
                                resource_types: if u.ratio::<u8>(1, 4)? {
                                    // The action applies to an unspecified
                                    // principal an no other entity types.
                                    None
                                } else {
                                    // for each entity type, flip a coin to see
                                    // whether to include it as a possible
                                    // resource type for this action
                                    Some(
                                        entity_types
                                            .iter()
                                            .filter_map(|(name, _)| match u.ratio::<u8>(1, 2) {
                                                Ok(true) => {
                                                    resource_types.insert(
                                                        build_qualified_entity_type_name(
                                                            namespace.clone(),
                                                            name,
                                                        ),
                                                    );
                                                    Some(name.clone())
                                                }
                                                Ok(false) => None,
                                                Err(_) => None,
                                            })
                                            .collect(),
                                    )
                                },
                                principal_types: if u.ratio::<u8>(1, 4)? {
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
                                                    principal_types.insert(
                                                        build_qualified_entity_type_name(
                                                            namespace.clone(),
                                                            name,
                                                        ),
                                                    );
                                                    Some(name.clone())
                                                }
                                                Ok(false) => None,
                                                Err(_) => None,
                                            })
                                            .collect(),
                                    )
                                },
                                context: arbitrary_attrspec(&settings, &entity_type_names, u)?,
                            })
                        },
                        member_of: if settings.enable_action_groups_and_attrs {
                            Some(vec![])
                        } else {
                            None
                        },
                        // Attributes are currently ignored by the validator, so I
                        // haven't bothered filling this in. They'll definitely be
                        // used soon-ish. TODO: Arbitrary attribute names and
                        // values.
                        attributes: HashMap::new().into(),
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
                            .push(amzn_cedar_validator::ActionEntityUID::default_type(
                                name.clone(),
                            ));
                    }
                }
            }
        }

        let attrsorcontexts /* : impl Iterator<Item = &AttributesOrContext> */ = entity_types
            .iter()
            .map(|(_, et)| unwrap_attrs_or_context(&et.shape))
            .chain(actions.iter().filter_map(|(_, action)| action.applies_to.as_ref()).map(|a| unwrap_attrs_or_context(&a.context)));
        let attributes: Vec<(SmolStr, amzn_cedar_validator::SchemaType)> = attrsorcontexts
            .flat_map(|(attributes, _)| {
                attributes.iter().map(|(s, ty)| {
                    (
                        s.parse().expect("attribute names should be valid Ids"),
                        ty.ty.clone(),
                    )
                })
            })
            .collect();
        let attributes_by_type = {
            let triples = entity_types
                .iter()
                .map(|(name, et)| {
                    (
                        build_qualified_entity_type_name(namespace.clone(), name),
                        unwrap_attrs_or_context(&et.shape).0,
                    )
                })
                .flat_map(|(tyname, attrs)| {
                    attrs.iter().map(move |(attr_name, ty)| {
                        (
                            schematype_to_type(&ty.ty),
                            (tyname.clone(), attr_name.clone()),
                        )
                    })
                });
            let mut hm: HashMap<Type, Vec<(ast::Name, SmolStr)>> = HashMap::new();
            for (ty, pair) in triples {
                hm.entry(ty).or_default().push(pair);
            }
            hm
        };

        let actions_eids = actions.iter().map(|(name, _)| name.clone()).collect();
        Ok(Schema {
            schema: amzn_cedar_validator::NamespaceDefinition {
                common_types: HashMap::new().into(),
                entity_types: entity_types.into_iter().collect(),
                actions: actions.into_iter().collect(),
            },
            namespace,
            constant_pool: u
                .arbitrary()
                .map_err(|e| while_doing("generating constant pool", e))?,
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
    pub fn arbitrary_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            <HashSet<ast::Name> as Arbitrary>::size_hint(depth),
            arbitrary_attrspec_size_hint(depth), // actually we do one of these per Name that was generated
            super::size_hint_for_ratio(1, 2),    // actually many of these calls
            <HashSet<String> as Arbitrary>::size_hint(depth),
            super::size_hint_for_ratio(1, 8), // actually many of these calls
            super::size_hint_for_ratio(1, 4), // zero to many of these calls
            super::size_hint_for_ratio(1, 2), // zero to many of these calls
            arbitrary_attrspec_size_hint(depth),
            super::size_hint_for_ratio(1, 2), // actually many of these calls
            <ConstantPool as Arbitrary>::size_hint(depth),
        ])
    }

    /// Get an arbitrary Hierarchy conforming to the schema.
    pub fn arbitrary_hierarchy(&self, u: &mut Unstructured<'_>) -> Result<super::Hierarchy> {
        // For each entity type in the schema, generate one or more entities of that type
        let uids_by_type = self
            .schema
            .entity_types
            .keys()
            .map(|name| {
                let name = build_qualified_entity_type_name(self.namespace.clone(), name);
                let mut uids = vec![Self::arbitrary_uid_with_type(&name, None, u)?];
                u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                    uids.push(Self::arbitrary_uid_with_type(&name, None, u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok((name, uids))
            })
            .collect::<Result<HashMap<ast::Name, Vec<ast::EntityUID>>>>()?;
        let entities = uids_by_type
            .iter()
            .flat_map(|(_, uids)| {
                uids.iter()
                    .map(|uid| (uid.clone(), ast::Entity::with_uid(uid.clone())))
            })
            .collect::<HashMap<ast::EntityUID, ast::Entity>>();
        let uids = entities.iter().map(|(uid, _)| uid.clone()).collect();
        let mut hierarchy = super::Hierarchy {
            entities,
            uids,
            uids_by_type,
        };
        let entitytypes_by_type: HashMap<ast::Name, &EntityType> = self
            .schema
            .entity_types
            .iter()
            .map(|(name, et)| {
                (
                    build_qualified_entity_type_name(self.namespace.clone(), name),
                    et,
                )
            })
            .collect();
        // for each entity, optionally add hierarchy-membership edges to every
        // entity that's eligible to be a parent of that type
        for (uid, entity) in &mut hierarchy.entities {
            match uid.entity_type() {
                // entity data is generated with `arbitrary_uid_with_type`, which can never
                // produce an unspecified entity
                ast::EntityType::Unspecified => {
                    panic!("should not be possible to generate an unspecified entity")
                }
                ast::EntityType::Concrete(name) => {
                    for allowed_parent_typename in &entitytypes_by_type
                        .get(name)
                        .expect("typename should have an EntityType")
                        .member_of_types
                    {
                        let allowed_parent_typename = build_qualified_entity_type_name(
                            self.namespace.clone(),
                            allowed_parent_typename,
                        );
                        for possible_parent_uid in hierarchy
                            .uids_by_type
                            .get(&allowed_parent_typename)
                            .expect("all typenames should be in the map")
                        {
                            if u.ratio::<u8>(1, 2)? {
                                entity.add_ancestor(possible_parent_uid.clone());
                            }
                        }
                    }
                }
            }
        }
        // for each entity, add appropriate attributes
        let hierarchy_no_attrs = hierarchy.clone(); // TODO: that's a hack to get around borrow checker
        for (uid, entity) in &mut hierarchy.entities {
            match uid.entity_type() {
                // entity data is generated with `arbitrary_uid_with_type`, which can never
                // produce an unspecified entity
                ast::EntityType::Unspecified => {
                    panic!("should not be possible to generate an unspecified entity")
                }
                ast::EntityType::Concrete(name) => {
                    let attr_or_context = unwrap_attrs_or_context(
                        &entitytypes_by_type
                            .get(name)
                            .expect("typename should have an EntityType")
                            .shape,
                    );
                    if attr_or_context.1 {
                        // maybe add some additional attributes with arbitrary types
                        u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                            let attr_type = if self.settings.enable_extensions {
                                u.arbitrary()?
                            } else {
                                Type::arbitrary_nonextension(u)?
                            };
                            let attr_name: String = u.arbitrary()?;
                            entity.set_attr(
                                attr_name.into(),
                                self.arbitrary_attr_value_for_type(
                                    &attr_type,
                                    Some(&hierarchy_no_attrs),
                                    self.settings.max_depth,
                                    u,
                                )?
                                .into(),
                            );
                            Ok(std::ops::ControlFlow::Continue(()))
                        })?;
                    }
                    for (attr, ty) in attr_or_context.0 {
                        // now add the actual optional and required attributes, with the
                        // correct types.
                        // Doing this second ensures that we overwrite any "additional"
                        // attributes so that they definitely have the required type, in
                        // case we got a name collision between an explicitly specified
                        // attribute and one of the "additional" ones we added.
                        if ty.required || u.ratio::<u8>(1, 2)? {
                            let attr_val = self.arbitrary_attr_value_for_schematype(
                                &ty.ty,
                                Some(&hierarchy_no_attrs),
                                self.settings.max_depth,
                                u,
                            )?;
                            entity.set_attr(
                                attr.parse().expect(
                                    "all attribute names in the schema should be valid identifiers",
                                ),
                                attr_val.into(),
                            );
                        }
                    }
                }
            }
        }

        Ok(hierarchy)
    }
    pub fn arbitrary_hierarchy_size_hint(_depth: usize) -> (usize, Option<usize>) {
        (0, None) // TODO: more precise
    }

    /// Get an arbitrary UID from the schema, that could be used as a `principal`.
    ///
    /// If `hierarchy` is present, (usually) choose a UID that exists in the hierarchy.
    pub fn arbitrary_principal_uid(
        &self,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        Self::arbitrary_uid_with_type(
            u.choose(&self.principal_types)
                .map_err(|e| while_doing("choosing a principal type", e))?,
            hierarchy,
            u,
        )
    }
    pub fn arbitrary_principal_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            super::size_hint_for_choose(None),
            Self::arbitrary_uid_with_type_size_hint(depth),
        )
    }
    /// Get an arbitrary UID from the schema, that could be used as an `action`.
    ///
    /// This doesn't take the `Hierarchy` as an input, because we assume that
    /// all actions are defined in the schema, and we just give you one of the
    /// actions from the schema.
    pub fn arbitrary_action_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        let action = &u
            .choose(&self.actions_eids)
            .map_err(|e| while_doing("choosing an action", e))?;
        Ok(uid_for_action_name(self.namespace.clone(), action))
    }
    pub fn arbitrary_action_uid_size_hint(_depth: usize) -> (usize, Option<usize>) {
        super::size_hint_for_choose(None)
    }
    /// Get an arbitrary UID from the schema, that could be used as a `resource`.
    ///
    /// If `hierarchy` is present, (usually) choose a UID that exists in the hierarchy.
    pub fn arbitrary_resource_uid(
        &self,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        Self::arbitrary_uid_with_type(
            u.choose(&self.resource_types)
                .map_err(|e| while_doing("choosing a resource type", e))?,
            hierarchy,
            u,
        )
    }
    pub fn arbitrary_resource_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            super::size_hint_for_choose(None),
            Self::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    fn arbitrary_uid_with_optional_type(
        &self,
        ty_name: Option<&SmolStr>,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        let ty = build_qualified_entity_type(
            self.namespace.clone(),
            ty_name.as_ref().map(|x| x.as_str()),
        );
        match ty {
            ast::EntityType::Concrete(ty) => Self::arbitrary_uid_with_type(&ty, hierarchy, u),
            ast::EntityType::Unspecified => Ok(ast::EntityUID::unspecified_from_eid(
                ast::Eid::new("Unspecified"),
            )),
        }
    }

    /// Get an arbitrary UID with the given typename.
    ///
    /// If `hierarchy` is present, (usually) choose a UID that exists in the hierarchy.
    fn arbitrary_uid_with_type(
        ty: &ast::Name,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        match hierarchy {
            None => Ok(ast::EntityUID::from_components(ty.clone(), u.arbitrary()?)),
            Some(hierarchy) => hierarchy.arbitrary_uid_with_type(ty, u),
        }
    }
    fn arbitrary_uid_with_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::or(
            <ast::Eid as Arbitrary>::size_hint(depth),
            super::Hierarchy::arbitrary_uid_with_type_size_hint(depth),
        )
    }

    /// get an arbitrary UID from the schema -- may be a principal, action, or resource UID.
    ///
    /// If `hierarchy` is present, (usually) choose a UID that exists in the hierarchy.
    fn arbitrary_uid(
        &self,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityUID> {
        match u.int_in_range::<u8>(0..=2)? {
            0 => self.arbitrary_principal_uid(hierarchy, u),
            1 => self.arbitrary_action_uid(u),
            2 => self.arbitrary_resource_uid(hierarchy, u),
            n => panic!("bad index: {n}"),
        }
    }

    fn arbitrary_specified_uid_without_schema(u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        Ok(ast::EntityUID::from_components(
            u.arbitrary::<ast::Name>()?,
            u.arbitrary::<ast::Eid>()?,
        ))
    }

    #[allow(dead_code)]
    fn arbitrary_uid_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            crate::size_hint_for_range(0, 2),
            arbitrary::size_hint::or_all(&[
                Self::arbitrary_principal_uid_size_hint(depth),
                Self::arbitrary_action_uid_size_hint(depth),
                Self::arbitrary_resource_uid_size_hint(depth),
            ]),
        )
    }

    /// internal helper function, try to convert `Type` into `SchemaType`
    fn try_into_schematype(
        &self,
        ty: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<Option<amzn_cedar_validator::SchemaType>> {
        use amzn_cedar_validator::SchemaType;
        use amzn_cedar_validator::SchemaTypeVariant;
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
                let entity_type = self.arbitrary_uid(None, u)?.components().0;
                // not possible for Schema::arbitrary_uid to generate an unspecified entity
                match entity_type {
                    ast::EntityType::Unspecified => {
                        panic!("should not be possible to generate an unspecified entity")
                    }
                    ast::EntityType::Concrete(name) => Some(entity_type_name_to_schema_type(&name)),
                }
            }
            Type::IPAddr => Some(SchemaTypeVariant::Extension {
                name: "ipaddr".into(),
            }),
            Type::Decimal => Some(SchemaTypeVariant::Extension {
                name: "decimal".into(),
            }),
        }
        .map(SchemaType::Type))
    }

    /// get an attribute name and its `SchemaType`, from the schema
    fn arbitrary_attr(
        &self,
        u: &mut Unstructured<'_>,
    ) -> Result<&(SmolStr, amzn_cedar_validator::SchemaType)> {
        u.choose(&self.attributes)
            .map_err(|e| while_doing("getting arbitrary attr from schema", e))
    }

    /// Given a type, get an entity type name and attribute name, such that
    /// entities with that typename have a (possibly optional) attribute with
    /// the given type
    fn arbitrary_attr_for_type(
        &self,
        target_type: &Type,
        u: &mut Unstructured<'_>,
    ) -> Result<&(ast::Name, SmolStr)> {
        match self.attributes_by_type.get(target_type) {
            Some(vec) => u
                .choose(vec)
                .map_err(|e| while_doing("getting arbitrary attr for type", e)),
            None => Err(Error::EmptyChoose {
                doing_what: "getting arbitrary attr for type",
            }),
        }
    }

    /// Given a schematype, get an entity type name and attribute name, such
    /// that entities with that typename have a (possibly optional) attribute
    /// with the given schematype
    fn arbitrary_attr_for_schematype(
        &self,
        target_type: impl Into<amzn_cedar_validator::SchemaType>,
        u: &mut Unstructured<'_>,
    ) -> Result<(ast::Name, SmolStr)> {
        let target_type: amzn_cedar_validator::SchemaType = target_type.into();
        let pairs: Vec<(ast::Name, SmolStr)> = self
            .schema
            .entity_types
            .iter()
            .map(|(name, et)| {
                (
                    build_qualified_entity_type_name(self.namespace.clone(), name),
                    unwrap_attrs_or_context(&et.shape).0,
                )
            })
            .flat_map(|(tyname, attrs)| {
                attrs
                    .iter()
                    .filter(|(_, ty)| ty.ty == target_type)
                    .map(move |(attr_name, _)| (tyname.clone(), attr_name.clone()))
            })
            .collect();
        u.choose(&pairs)
            .cloned()
            .map_err(|e| while_doing("getting arbitrary attr for schematype", e))
    }

    /// get a literal value of an arbitrary type.
    /// This function is guaranteed to not recurse, directly or indirectly.
    fn arbitrary_literal(
        &self,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        match u.int_in_range::<u8>(0..=54)? {
            0..=10 => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
            11..=20 => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_int_constant(u)?,
            )),
            21..=30 => Ok(ast::Expr::val(
                self.constant_pool.arbitrary_string_constant(u)?,
            )),
            31..=50 => Ok(ast::Expr::val(self.arbitrary_uid(hierarchy, u)?)),
            51..=54 => Ok(ast::Expr::val(
                Self::arbitrary_specified_uid_without_schema(u)?,
            )),
            n => panic!("bad index: {n}"),
        }
    }

    /// get a literal value or variable of an arbitrary type.
    /// This function is guaranteed to not recurse, directly or indirectly.
    fn arbitrary_literal_or_var(
        &self,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        if u.ratio(1, 4)? {
            Ok(ast::Expr::var(u.arbitrary()?))
        } else {
            self.arbitrary_literal(hierarchy, u)
        }
    }

    pub fn arbitrary_value_for_type(
        &self,
        target_type: &Type,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<Value> {
        match target_type {
            Type::Bool => {
                // the only valid bool-typed attribute value is a bool literal
                let b: bool = u.arbitrary()?;
                Ok(Value::Lit(b.into()))
            }
            Type::Long => {
                // the only valid long-typed attribute value is an int literal
                Ok(Value::Lit(
                    self.constant_pool.arbitrary_int_constant(u)?.into(),
                ))
            }
            Type::String => {
                // the only valid string-typed attribute value is a string literal
                Ok(Value::Lit(
                    self.constant_pool.arbitrary_string_constant(u)?.into(),
                ))
            }
            Type::Entity => {
                // the only valid entity-typed attribute value is a UID literal
                Ok(Value::Lit(self.arbitrary_uid(hierarchy, u)?.into()))
            }
            Type::Set(target_element_ty) => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(Value::empty_set())
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
                        l.push(self.arbitrary_value_for_type(
                            &target_element_ty,
                            hierarchy,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(Value::set(l))
                }
            }
            Type::Record => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty record
                    Ok(Value::empty_record())
                } else {
                    let mut r = HashMap::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        let (attr_name, attr_ty) = self.arbitrary_attr(u)?.clone();
                        let attr_val = self.arbitrary_value_for_schematype(
                            &attr_ty,
                            hierarchy,
                            max_depth - 1,
                            u,
                        )?;
                        r.insert(attr_name, attr_val);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    let map: BTreeMap<_, _> = r.into_iter().collect();
                    Ok(Value::Record(Arc::new(map)))
                }
            }
            _ => Err(Error::ExtensionsDisabled),
        }
    }

    fn arbitrary_value_for_schematype(
        &self,
        target_type: &amzn_cedar_validator::SchemaType,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<Value> {
        use amzn_cedar_validator::SchemaTypeVariant;
        let target_type = unwrap_schema_type(target_type);
        match target_type {
            SchemaTypeVariant::Boolean => {
                self.arbitrary_value_for_type(&Type::bool(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Long => {
                self.arbitrary_value_for_type(&Type::long(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::String => {
                self.arbitrary_value_for_type(&Type::string(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Set {
                element: element_ty,
            } => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(Value::empty_set())
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.arbitrary_value_for_schematype(
                            element_ty,
                            hierarchy,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(Value::set(l))
                }
            }
            SchemaTypeVariant::Record {
                attributes,
                additional_attributes,
            } => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: quit here
                    Err(Error::TooDeep)
                } else {
                    let mut r = HashMap::new();
                    if *additional_attributes {
                        // maybe add some "additional" attributes not mentioned in schema
                        u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                            let (attr_name, attr_ty) = self.arbitrary_attr(u)?.clone();
                            let attr_val = self.arbitrary_value_for_schematype(
                                &attr_ty,
                                hierarchy,
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
                            let attr_val = self.arbitrary_value_for_schematype(
                                &attr_ty.ty,
                                hierarchy,
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
                    let m: BTreeMap<_, _> = r.into_iter().collect();
                    Ok(Value::Record(Arc::new(m)))
                }
            }
            SchemaTypeVariant::Entity { name } => {
                // the only valid entity-typed attribute value is a UID literal

                // The namespace for the entity type is the namespace of the
                // SchemaType if one is present. Otherwise, it is the schema
                // namespace if that is present. The type is unqualified if
                // neither is present.
                let entity_type_name = parse_name_with_default_namespace(&self.namespace, name);
                let euid = Self::arbitrary_uid_with_type(&entity_type_name, hierarchy, u)?;
                Ok(Value::Lit(euid.into()))
            }
            _ => Err(Error::ExtensionsDisabled),
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
    fn arbitrary_attr_value_for_type(
        &self,
        target_type: &Type,
        hierarchy: Option<&super::Hierarchy>,
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
                Ok(AttrValue::UIDLit(self.arbitrary_uid(hierarchy, u)?))
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
                        l.push(self.arbitrary_attr_value_for_type(
                            &target_element_ty,
                            hierarchy,
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
                        let (attr_name, attr_ty) = self.arbitrary_attr(u)?.clone();
                        let attr_val = self.arbitrary_attr_value_for_schematype(
                            &attr_ty,
                            hierarchy,
                            max_depth - 1,
                            u,
                        )?;
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
    fn arbitrary_attr_value_for_type_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::recursion_guard(depth, |depth| {
            arbitrary::size_hint::and(
                super::size_hint_for_range(0, 7),
                arbitrary::size_hint::or_all(&[
                    <bool as Arbitrary>::size_hint(depth),
                    ConstantPool::arbitrary_int_constant_size_hint(depth),
                    ConstantPool::arbitrary_string_constant_size_hint(depth),
                    Schema::arbitrary_uid_size_hint(depth),
                    arbitrary::size_hint::and_all(&[
                        AvailableExtensionFunctions::arbitrary_constructor_for_type_size_hint(
                            depth,
                        ),
                        super::size_hint_for_ratio(9, 10),
                        super::size_hint_for_range(0, 4),
                        Schema::arbitrary_attr_value_for_type_size_hint(depth),
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
    /// If `hierarchy` is present, any literal UIDs included in the AttrValue
    /// will (usually) exist in the hierarchy.
    ///
    /// `max_depth`: maximum depth of the attribute value expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    fn arbitrary_attr_value_for_schematype(
        &self,
        target_type: &amzn_cedar_validator::SchemaType,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<AttrValue> {
        use amzn_cedar_validator::SchemaTypeVariant;
        let target_type = unwrap_schema_type(target_type);
        match target_type {
            SchemaTypeVariant::Boolean => {
                self.arbitrary_attr_value_for_type(&Type::bool(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Long => {
                self.arbitrary_attr_value_for_type(&Type::long(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::String => {
                self.arbitrary_attr_value_for_type(&Type::string(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Set {
                element: element_ty,
            } => {
                // the only valid Set-typed attribute value is a set literal
                if max_depth == 0 {
                    // no recursion allowed: just do the empty set
                    Ok(AttrValue::Set(vec![]))
                } else {
                    let mut l = Vec::new();
                    u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                        l.push(self.arbitrary_attr_value_for_schematype(
                            element_ty,
                            hierarchy,
                            max_depth - 1,
                            u,
                        )?);
                        Ok(std::ops::ControlFlow::Continue(()))
                    })?;
                    Ok(AttrValue::Set(l))
                }
            }
            SchemaTypeVariant::Record {
                attributes,
                additional_attributes,
            } => {
                // the only valid Record-typed attribute value is a record literal
                if max_depth == 0 {
                    // no recursion allowed: quit here
                    Err(Error::TooDeep)
                } else {
                    let mut r = HashMap::new();
                    if *additional_attributes {
                        // maybe add some "additional" attributes not mentioned in schema
                        u.arbitrary_loop(None, Some(self.settings.max_width as u32), |u| {
                            let (attr_name, attr_ty) = self.arbitrary_attr(u)?.clone();
                            let attr_val = self.arbitrary_attr_value_for_schematype(
                                &attr_ty,
                                hierarchy,
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
                            let attr_val = self.arbitrary_attr_value_for_schematype(
                                &attr_ty.ty,
                                hierarchy,
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
            SchemaTypeVariant::Entity { name } => {
                // the only valid entity-typed attribute value is a UID literal

                let entity_type_name = parse_name_with_default_namespace(&self.namespace, name);
                Ok(AttrValue::UIDLit(Self::arbitrary_uid_with_type(
                    &entity_type_name,
                    hierarchy,
                    u,
                )?))
            }
            SchemaTypeVariant::Extension { .. } if !self.settings.enable_extensions => {
                panic!("shouldn't have SchemaTypeVariant::Extension with extensions disabled")
            }
            SchemaTypeVariant::Extension { name } => match name.as_str() {
                "ipaddr" => {
                    self.arbitrary_attr_value_for_type(&Type::ipaddr(), hierarchy, max_depth, u)
                }
                "decimal" => {
                    self.arbitrary_attr_value_for_type(&Type::decimal(), hierarchy, max_depth, u)
                }
                _ => unimplemented!("extension type {name:?}"),
            },
        }
    }

    /// size hint for arbitrary_attr_value_for_schematype()
    #[allow(dead_code)]
    fn arbitrary_attr_value_for_schematype_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::recursion_guard(depth, |depth| {
            arbitrary::size_hint::or_all(&[
                Self::arbitrary_attr_value_for_type_size_hint(depth),
                (1, None), // not sure how to hint for arbitrary_loop()
                Self::arbitrary_uid_with_type_size_hint(depth),
                Self::arbitrary_attr_value_for_type_size_hint(depth),
            ])
        })
    }

    /// get a (fully general) arbitrary expression conforming to the schema, but
    /// no attempt to match types. (TODO: better specification for what
    /// "conforming to the schema but not matching types" means.)
    ///
    /// If `hierarchy` is present, any literal UIDs included in the Expr will
    /// (usually) exist in the hierarchy.
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    pub fn arbitrary_expr(
        &self,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        if max_depth == 0 {
            // no recursion allowed: just generate a literal
            self.arbitrary_literal_or_var(hierarchy, u)
        } else {
            match u.int_in_range::<u8>(0..=4)? {
                0 | 1 => {
                    // a literal or variable
                    self.arbitrary_literal_or_var(hierarchy, u)
                }
                2 => {
                    // == expression
                    Ok(ast::Expr::is_eq(
                        self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                    ))
                }
                3 => {
                    // not expression
                    Ok(ast::Expr::not(self.arbitrary_expr(
                        hierarchy,
                        max_depth - 1,
                        u,
                    )?))
                }
                4 => {
                    // any other expression
                    match u.int_in_range::<u8>(0..=38)? {
                        0 | 1 => Ok(ast::Expr::ite(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        2 | 3 => Ok(ast::Expr::and(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        4 | 5 => Ok(ast::Expr::or(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        6 => Ok(ast::Expr::less(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        7 => Ok(ast::Expr::lesseq(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        8 => Ok(ast::Expr::greater(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        9 => Ok(ast::Expr::greatereq(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        10 => Ok(ast::Expr::add(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        11 => Ok(ast::Expr::sub(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        12 => {
                            // arbitrary expression, which may be a constant
                            let expr = self.arbitrary_expr(hierarchy, max_depth - 1, u)?;
                            // arbitrary constant integer
                            let c = self.constant_pool.arbitrary_int_constant(u)?;
                            Ok(ast::Expr::mul(expr, c))
                        }
                        13 => {
                            // negation expression
                            Ok(ast::Expr::neg(self.arbitrary_expr(
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?))
                        }
                        14..=19 => Ok(ast::Expr::is_in(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        20 => Ok(ast::Expr::contains(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        21 => Ok(ast::Expr::contains_all(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        22 => Ok(ast::Expr::contains_any(
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                            self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                        )),
                        23 | 24 => {
                            if self.settings.enable_like {
                                Ok(ast::Expr::like(
                                    self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                                    self.constant_pool.arbitrary_pattern_literal(u)?,
                                ))
                            } else {
                                Err(Error::LikeDisabled)
                            }
                        }
                        25 => {
                            let mut l = Vec::new();
                            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                                l.push(self.arbitrary_expr(hierarchy, max_depth - 1, u)?);
                                Ok(std::ops::ControlFlow::Continue(()))
                            })?;
                            Ok(ast::Expr::set(l))
                        }
                        26 => {
                            let mut r = Vec::new();
                            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                                let (attr_name, _) = self.arbitrary_attr(u)?;
                                r.push((
                                    attr_name.clone(),
                                    self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                                ));
                                Ok(std::ops::ControlFlow::Continue(()))
                            })?;
                            Ok(ast::Expr::record(r))
                        }
                        27 => {
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
                                    .map(|_| self.arbitrary_expr(hierarchy, max_depth - 1, u))
                                    .collect::<Result<_>>()?,
                            ))
                        }
                        v @ 28..=34 => {
                            let attr_name = match v {
                                28 => {
                                    let s: String = u.arbitrary()?;
                                    SmolStr::from(s)
                                }
                                _ => self.arbitrary_attr(u)?.0.clone(),
                            };
                            let e = self.arbitrary_expr(hierarchy, max_depth - 1, u)?;
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
                        }
                        v @ 35..=38 => {
                            let attr_name = match v {
                                35 | 36 => self.arbitrary_attr(u)?.0.clone(),
                                _ => {
                                    let s: String = u.arbitrary()?;
                                    SmolStr::from(s)
                                }
                            };
                            Ok(ast::Expr::has_attr(
                                self.arbitrary_expr(hierarchy, max_depth - 1, u)?,
                                attr_name,
                            ))
                        }
                        n => panic!("bad index: {n}"),
                    }
                }
                n => panic!("bad index: {n}"),
            }
        }
    }
    /// get a (fully general) arbitrary constant, as an expression.
    ///
    /// If `hierarchy` is present, any literal UIDs included in the Expr will
    /// (usually) exist in the hierarchy.
    #[allow(dead_code)]
    fn arbitrary_const_expr(
        &self,
        hierarchy: Option<&super::Hierarchy>,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        match u.int_in_range::<u8>(0..=5)? {
            0..=3 => self.arbitrary_literal(hierarchy, u),
            4 => {
                let mut l = Vec::new();
                u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                    l.push(self.arbitrary_const_expr(hierarchy, u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::set(l))
            }
            5 => {
                let mut r = Vec::new();
                u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                    let (attr_name, _) = self.arbitrary_attr(u)?;
                    r.push((attr_name.clone(), self.arbitrary_const_expr(hierarchy, u)?));
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::record(r))
            }
            n => panic!("bad index: {n}"),
        }
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

    /// get an arbitrary expression of a given type conforming to the schema
    ///
    /// If `hierarchy` is present, any literal UIDs included in the Expr will
    /// (usually) exist in the hierarchy.
    ///
    /// `max_depth`: maximum size (i.e., depth) of the expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    fn arbitrary_expr_for_type(
        &self,
        target_type: &Type,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        if self.should_generate_unknown(max_depth, u)? {
            let name = self
                .unknown_pool
                .alloc(target_type.clone(), self, hierarchy, u)?;
            Ok(ast::Expr::unknown(name))
        } else {
            match target_type {
                Type::Bool => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do a literal
                        Ok(ast::Expr::val(u.arbitrary::<bool>()?))
                    } else {
                        match u.int_in_range::<u8>(0..=60)? {
                            // bool literal
                            0 | 1 => Ok(ast::Expr::val(u.arbitrary::<bool>()?)),
                            // == expression, where types on both sides match
                            2..=6 => {
                                let ty: Type = u.arbitrary()?;
                                Ok(ast::Expr::is_eq(
                                    self.arbitrary_expr_for_type(&ty, hierarchy, max_depth - 1, u)?,
                                    self.arbitrary_expr_for_type(&ty, hierarchy, max_depth - 1, u)?,
                                ))
                            }
                            // == expression, where types do not match
                            7 | 8 => {
                                let ty1: Type = u.arbitrary()?;
                                let ty2: Type = u.arbitrary()?;
                                Ok(ast::Expr::is_eq(
                                    self.arbitrary_expr_for_type(
                                        &ty1,
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    self.arbitrary_expr_for_type(
                                        &ty2,
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                ))
                            }
                            // not expression
                            9..=13 => Ok(ast::Expr::not(self.arbitrary_expr_for_type(
                                &Type::bool(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?)),
                            // if-then-else expression, where both arms are bools
                            14..=18 => Ok(ast::Expr::ite(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // && expression
                            19..=23 => Ok(ast::Expr::and(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // || expression
                            24..=28 => Ok(ast::Expr::or(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // < expression
                            29 => Ok(ast::Expr::less(
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // <= expression
                            30 => Ok(ast::Expr::lesseq(
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // > expression
                            31 => Ok(ast::Expr::greater(
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // >= expression
                            32 => Ok(ast::Expr::greatereq(
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // in expression, non-set form
                            33..=43 => Ok(ast::Expr::is_in(
                                self.arbitrary_expr_for_type(
                                    &Type::entity(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::entity(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // in expression, set form
                            44 | 45 => Ok(ast::Expr::is_in(
                                self.arbitrary_expr_for_type(
                                    &Type::entity(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::set_of(Type::entity()),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // contains() on a set
                            46 | 47 => {
                                let element_ty = u.arbitrary()?;
                                let element = self.arbitrary_expr_for_type(
                                    &element_ty,
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?;
                                let set = self.arbitrary_expr_for_type(
                                    &Type::set_of(element_ty),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?;
                                Ok(ast::Expr::contains(set, element))
                            }
                            // containsAll()
                            48 => Ok(ast::Expr::contains_all(
                                // doesn't require the input sets to have the same element type
                                self.arbitrary_expr_for_type(
                                    &Type::set_of(u.arbitrary()?),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::set_of(u.arbitrary()?),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // containsAny()
                            49 => Ok(ast::Expr::contains_any(
                                // doesn't require the input sets to have the same element type
                                self.arbitrary_expr_for_type(
                                    &Type::set_of(u.arbitrary()?),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::set_of(u.arbitrary()?),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // like
                            50 | 51 => {
                                if self.settings.enable_like {
                                    Ok(ast::Expr::like(
                                        self.arbitrary_expr_for_type(
                                            &Type::string(),
                                            hierarchy,
                                            max_depth - 1,
                                            u,
                                        )?,
                                        self.constant_pool.arbitrary_pattern_literal(u)?,
                                    ))
                                } else {
                                    Err(Error::LikeDisabled)
                                }
                            }
                            // extension function that returns bool
                            52 | 53 => self.arbitrary_ext_func_call_for_type(
                                &Type::bool(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            ),
                            // getting an attr (on an entity) with type bool
                            54 => {
                                let (entity_type, attr_name) = self.arbitrary_attr_for_schematype(
                                    amzn_cedar_validator::SchemaTypeVariant::Boolean,
                                    u,
                                )?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &entity_type_name_to_schema_type(&entity_type),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // getting an attr (on a record) with type bool
                            55 => {
                                let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &record_schematype_with_attr(
                                            attr_name.clone(),
                                            amzn_cedar_validator::SchemaTypeVariant::Boolean,
                                        ),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // has expression on an entity, for a (possibly optional) attribute the entity does have in the schema
                            56 | 57 => {
                                let (entity_name, entity_type) = self
                                    .schema
                                    .entity_types
                                    .iter()
                                    .nth(
                                        u.choose_index(self.schema.entity_types.len())
                                            .expect("Failed to select entity index."),
                                    )
                                    .expect("Failed to select entity from map.");
                                let attr_names: Vec<&SmolStr> =
                                    unwrap_attrs_or_context(&entity_type.shape)
                                        .0
                                        .keys()
                                        .collect::<Vec<_>>();
                                let attr_name = SmolStr::clone(u.choose(&attr_names)?);
                                Ok(ast::Expr::has_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &amzn_cedar_validator::SchemaTypeVariant::Entity {
                                            // This does not use an explicit namespace because entity types
                                            // implicitly use the schema namespace if an explicit one is not
                                            // provided.
                                            name: entity_name.clone(),
                                        },
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // has expression on an entity, for an arbitrary attribute name
                            58 => Ok(ast::Expr::has_attr(
                                self.arbitrary_expr_for_type(
                                    &Type::entity(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.constant_pool.arbitrary_string_constant(u)?,
                            )),
                            // has expression on a record
                            59 | 60 => Ok(ast::Expr::has_attr(
                                self.arbitrary_expr_for_type(
                                    &Type::record(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.constant_pool.arbitrary_string_constant(u)?,
                            )),
                            n => panic!("bad index: {n}"),
                        }
                    }
                }
                Type::Long => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do a literal
                        Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_int_constant(u)?,
                        ))
                    } else {
                        match u.int_in_range::<u8>(0..=33)? {
                            // int literal. weighted highly because all the other choices
                            // are recursive, and we don't want a scenario where we have,
                            // say, a 90% chance to recurse every time
                            0..=15 => Ok(ast::Expr::val(
                                self.constant_pool.arbitrary_int_constant(u)?,
                            )),
                            // if-then-else expression, where both arms are longs
                            16..=20 => Ok(ast::Expr::ite(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // + expression
                            21 => Ok(ast::Expr::add(
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // - expression
                            22 => Ok(ast::Expr::sub(
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // * expression
                            23 => {
                                // arbitrary expression, which may be a constant
                                let expr = self.arbitrary_expr_for_type(
                                    &Type::long(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?;
                                // arbitrary integer constant
                                let c = self.constant_pool.arbitrary_int_constant(u)?;
                                Ok(ast::Expr::mul(expr, c))
                            }
                            // negation expression
                            24 => Ok(ast::Expr::neg(self.arbitrary_expr_for_type(
                                &Type::long(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?)),
                            // extension function that returns a long
                            25 => self.arbitrary_ext_func_call_for_type(
                                &Type::long(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            ),
                            // getting an attr (on an entity) with type long
                            26..=29 => {
                                let (entity_type, attr_name) = self.arbitrary_attr_for_schematype(
                                    amzn_cedar_validator::SchemaTypeVariant::Long,
                                    u,
                                )?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &entity_type_name_to_schema_type(&entity_type),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // getting an attr (on a record) with type long
                            30..=33 => {
                                let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &record_schematype_with_attr(
                                            attr_name.clone(),
                                            amzn_cedar_validator::SchemaTypeVariant::Long,
                                        ),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            n => panic!("bad index: {n}"),
                        }
                    }
                }
                Type::String => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do a literal
                        Ok(ast::Expr::val(
                            self.constant_pool.arbitrary_string_constant(u)?,
                        ))
                    } else {
                        match u.int_in_range::<u8>(0..=29)? {
                            // string literal. weighted highly because all the other choices
                            // are recursive, and we don't want a scenario where we have, say,
                            // a 90% chance to recurse every time
                            0..=15 => Ok(ast::Expr::val(
                                self.constant_pool.arbitrary_string_constant(u)?,
                            )),
                            // if-then-else expression, where both arms are strings
                            16..=20 => Ok(ast::Expr::ite(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::string(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::string(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // extension function that returns a string
                            21 => self.arbitrary_ext_func_call_for_type(
                                &Type::string(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            ),
                            // getting an attr (on an entity) with type string
                            22..=25 => {
                                let (entity_type, attr_name) = self.arbitrary_attr_for_schematype(
                                    amzn_cedar_validator::SchemaTypeVariant::String,
                                    u,
                                )?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &entity_type_name_to_schema_type(&entity_type),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // getting an attr (on a record) with type string
                            26..=29 => {
                                let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &record_schematype_with_attr(
                                            attr_name.clone(),
                                            amzn_cedar_validator::SchemaTypeVariant::String,
                                        ),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            n => panic!("bad index: {n}"),
                        }
                    }
                }
                Type::Set(target_element_ty) => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed, so, just do empty-set
                        Ok(ast::Expr::set(vec![]))
                    } else {
                        match u.int_in_range::<u8>(0..=15)? {
                            // set literal
                            0..=5 => {
                                let mut l = Vec::new();
                                let target_element_ty = target_element_ty
                                    .as_ref()
                                    .map_or_else(|| u.arbitrary(), |ty| Ok((*ty).clone()))?;
                                u.arbitrary_loop(
                                    Some(0),
                                    Some(self.settings.max_width as u32),
                                    |u| {
                                        l.push(self.arbitrary_expr_for_type(
                                            &target_element_ty,
                                            hierarchy,
                                            max_depth - 1,
                                            u,
                                        )?);
                                        Ok(std::ops::ControlFlow::Continue(()))
                                    },
                                )?;
                                Ok(ast::Expr::set(l))
                            }
                            // if-then-else expression, where both arms are (appropriate) sets
                            6 | 7 => Ok(ast::Expr::ite(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    target_type,
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    target_type,
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // extension function that returns an (appropriate) set
                            8 => self.arbitrary_ext_func_call_for_type(
                                target_type,
                                hierarchy,
                                max_depth - 1,
                                u,
                            ),
                            // getting an attr (on an entity) with the appropriate set type
                            9..=12 => {
                                let (entity_type, attr_name) =
                                    self.arbitrary_attr_for_type(target_type, u)?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &entity_type_name_to_schema_type(entity_type),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name.clone(),
                                ))
                            }
                            // getting an attr (on a record) with the appropriate set type
                            13..=15 => {
                                let attr_name: SmolStr =
                                    self.constant_pool.arbitrary_string_constant(u)?;
                                let attr_ty: amzn_cedar_validator::SchemaType =
                                match self.try_into_schematype(target_type, u)? {
                                    Some(schematy) => schematy,
                                    None => return Err(Error::IncorrectFormat {
                                        doing_what: "this particular complicated type not supported in this position",
                                    })
                                };
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &record_schematype_with_attr(attr_name.clone(), attr_ty),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            n => panic!("bad index: {n}"),
                        }
                    }
                }
                Type::Record => {
                    if max_depth == 0 || u.len() < 10 {
                        // no recursion allowed
                        Err(Error::TooDeep)
                    } else {
                        match u.int_in_range::<u8>(0..=11)? {
                            // record literal
                            0 | 1 => {
                                let mut r = Vec::new();
                                u.arbitrary_loop(
                                    Some(0),
                                    Some(self.settings.max_width as u32),
                                    |u| {
                                        let attr_val = self.arbitrary_expr_for_type(
                                            &u.arbitrary()?,
                                            hierarchy,
                                            max_depth - 1,
                                            u,
                                        )?;
                                        r.push((
                                            self.constant_pool.arbitrary_string_constant(u)?,
                                            attr_val,
                                        ));
                                        Ok(std::ops::ControlFlow::Continue(()))
                                    },
                                )?;
                                Ok(ast::Expr::record(r))
                            }
                            // if-then-else expression, where both arms are records
                            2 | 3 => Ok(ast::Expr::ite(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::record(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::record(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // extension function that returns a record
                            4 => self.arbitrary_ext_func_call_for_type(
                                &Type::record(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            ),
                            // getting an attr (on an entity) with type record
                            5..=8 => {
                                let (entity_type, attr_name) = self.arbitrary_attr_for_schematype(
                                    amzn_cedar_validator::SchemaTypeVariant::Record {
                                        // TODO: can we do better here, put in some
                                        // other attributes that appear in schema?
                                        attributes: BTreeMap::new(),
                                        additional_attributes: true,
                                    },
                                    u,
                                )?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &entity_type_name_to_schema_type(&entity_type),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // getting an attr (on a record) with type record
                            9..=11 => {
                                let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &record_schematype_with_attr(
                                            attr_name.clone(),
                                            amzn_cedar_validator::SchemaTypeVariant::Record {
                                                attributes: BTreeMap::new(),
                                                additional_attributes: true,
                                            },
                                        ),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            n => panic!("bad index: {n}"),
                        }
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
                        match u.int_in_range::<u8>(0..=44)? {
                            // UID literal, that exists
                            0..=10 => Ok(ast::Expr::val(self.arbitrary_uid(hierarchy, u)?)),
                            // UID literal, that doesn't exist
                            11 | 12 => Ok(ast::Expr::val(
                                Self::arbitrary_specified_uid_without_schema(u)?,
                            )),
                            // `principal`
                            13..=18 => Ok(ast::Expr::var(ast::Var::Principal)),
                            // `action`
                            19..=24 => Ok(ast::Expr::var(ast::Var::Action)),
                            // `resource`
                            25..=30 => Ok(ast::Expr::var(ast::Var::Resource)),
                            // if-then-else expression, where both arms are entities
                            31 | 32 => Ok(ast::Expr::ite(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::entity(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    &Type::entity(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // extension function that returns an entity
                            33 => self.arbitrary_ext_func_call_for_type(
                                &Type::entity(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            ),
                            // getting an attr (on an entity) with type entity
                            34..=39 => {
                                let (entity_type, attr_name) = self.arbitrary_attr_for_schematype(
                                    entity_type_name_to_schema_type(u.choose(&self.entity_types)?),
                                    u,
                                )?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &entity_type_name_to_schema_type(&entity_type),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // getting an attr (on a record) with type entity
                            40..=44 => {
                                let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &record_schematype_with_attr(
                                            attr_name.clone(),
                                            entity_type_name_to_schema_type(
                                                u.choose(&self.entity_types)?,
                                            ),
                                        ),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            n => panic!("bad index: {n}"),
                        }
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
                        let type_name: SmolStr = match target_type {
                            Type::IPAddr => "ipaddr",
                            Type::Decimal => "decimal",
                            _ => unreachable!("target type is deemed to be an extension type!"),
                        }
                        .into();
                        match u.int_in_range::<u8>(0..=14)? {
                            // if-then-else expression, where both arms are extension types
                            0 | 1 => Ok(ast::Expr::ite(
                                self.arbitrary_expr_for_type(
                                    &Type::bool(),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    target_type,
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                self.arbitrary_expr_for_type(
                                    target_type,
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                            )),
                            // extension function that returns an extension type
                            2..=10 => self.arbitrary_ext_func_call_for_type(
                                target_type,
                                hierarchy,
                                max_depth - 1,
                                u,
                            ),
                            // getting an attr (on an entity) with extension type
                            11 | 12 => {
                                let (entity_type, attr_name) = self.arbitrary_attr_for_schematype(
                                    amzn_cedar_validator::SchemaTypeVariant::Extension {
                                        name: type_name,
                                    },
                                    u,
                                )?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &entity_type_name_to_schema_type(&entity_type),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            // getting an attr (on a record) with type extension type
                            13 | 14 => {
                                let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                                Ok(ast::Expr::get_attr(
                                    self.arbitrary_expr_for_schematype(
                                        &record_schematype_with_attr(
                                            attr_name.clone(),
                                            amzn_cedar_validator::SchemaTypeVariant::Extension {
                                                name: type_name,
                                            },
                                        ),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?,
                                    attr_name,
                                ))
                            }
                            n => panic!("bad index: {n}"),
                        }
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
    fn arbitrary_expr_for_schematype(
        &self,
        target_type: &amzn_cedar_validator::SchemaTypeVariant,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        use amzn_cedar_validator::SchemaTypeVariant;
        match target_type {
            SchemaTypeVariant::Boolean => {
                self.arbitrary_expr_for_type(&Type::bool(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Long => {
                self.arbitrary_expr_for_type(&Type::long(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::String => {
                self.arbitrary_expr_for_type(&Type::string(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Set {
                element: element_ty,
            } => {
                if max_depth == 0 || u.len() < 10 {
                    // no recursion allowed, so, just do empty-set
                    Ok(ast::Expr::set(vec![]))
                } else {
                    match u.int_in_range::<u8>(0..=15)? {
                        // set literal
                        0..=5 => {
                            let mut l = Vec::new();
                            u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                                l.push(self.arbitrary_expr_for_schematype(
                                    unwrap_schema_type(element_ty),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?);
                                Ok(std::ops::ControlFlow::Continue(()))
                            })?;
                            Ok(ast::Expr::set(l))
                        }
                        // if-then-else expression, where both arms are (appropriate) sets
                        6 | 7 => Ok(ast::Expr::ite(
                            self.arbitrary_expr_for_type(
                                &Type::bool(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                            self.arbitrary_expr_for_schematype(
                                unwrap_schema_type(element_ty),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                            self.arbitrary_expr_for_schematype(
                                unwrap_schema_type(element_ty),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns an (appropriate) set
                        8 => self.arbitrary_ext_func_call_for_schematype(
                            unwrap_schema_type(element_ty),
                            hierarchy,
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with the appropriate set type
                        9..=12 => {
                            let (entity_type, attr_name) =
                                self.arbitrary_attr_for_schematype(target_type.clone(), u)?;
                            Ok(ast::Expr::get_attr(
                                self.arbitrary_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        }
                        // getting an attr (on a record) with the appropriate set type
                        13..=15 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            let record_expr = self.arbitrary_expr_for_schematype(
                                &record_schematype_with_attr(
                                    attr_name.clone(),
                                    target_type.clone(),
                                ),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?;
                            Ok(ast::Expr::get_attr(record_expr, attr_name))
                        }
                        n => panic!("bad index: {n}"),
                    }
                }
            }
            SchemaTypeVariant::Record {
                attributes,
                additional_attributes,
            } => {
                if max_depth == 0 || u.len() < 10 {
                    // no recursion allowed
                    Err(Error::TooDeep)
                } else {
                    match u.int_in_range::<u8>(0..=25)? {
                        // record literal
                        0 | 1 => {
                            let mut r: Vec<(SmolStr, ast::Expr)> = Vec::new();
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
                                        r.push((
                                            {
                                                let s: String = u.arbitrary()?;
                                                SmolStr::from(s)
                                            },
                                            self.arbitrary_expr_for_type(
                                                &attr_type,
                                                hierarchy,
                                                max_depth - 1,
                                                u,
                                            )?,
                                        ));
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
                                    let attr_val = self.arbitrary_expr_for_schematype(
                                        unwrap_schema_type(&ty.ty),
                                        hierarchy,
                                        max_depth - 1,
                                        u,
                                    )?;
                                    r.push((attr.clone(), attr_val));
                                }
                            }
                            Ok(ast::Expr::record(r))
                        }
                        // `context`, if `context` is an appropriate record type
                        // TODO: Check if the `context` is the appropriate type, and
                        // return it if it is.
                        2..=15 => Err(Error::TooDeep),
                        // if-then-else expression, where both arms are (appropriate) records
                        16 | 17 => Ok(ast::Expr::ite(
                            self.arbitrary_expr_for_type(
                                &Type::bool(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                            self.arbitrary_expr_for_schematype(
                                target_type,
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                            self.arbitrary_expr_for_schematype(
                                target_type,
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns an appropriate record
                        18 => self.arbitrary_ext_func_call_for_schematype(
                            target_type,
                            hierarchy,
                            max_depth - 1,
                            u,
                        ),
                        // getting an attr (on an entity) with an appropriate record type
                        19..=22 => {
                            let (entity_type, attr_name) =
                                self.arbitrary_attr_for_schematype(target_type.clone(), u)?;
                            Ok(ast::Expr::get_attr(
                                self.arbitrary_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        }
                        // getting an attr (on a record) with an appropriate record type
                        23..=25 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.arbitrary_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        target_type.clone(),
                                    ),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        }
                        n => panic!("bad index: {n}"),
                    }
                }
            }
            SchemaTypeVariant::Entity { name } => {
                if max_depth == 0 || u.len() < 10 {
                    // no recursion allowed, so, just do `principal`, `action`, or `resource`
                    Ok(ast::Expr::var(*u.choose(&[
                        ast::Var::Principal,
                        ast::Var::Action,
                        ast::Var::Resource,
                    ])?))
                } else {
                    match u.int_in_range::<u8>(0..=44)? {
                        // UID literal
                        0..=12 => {
                            let entity_type_name =
                                parse_name_with_default_namespace(&self.namespace, name);
                            Ok(ast::Expr::val(Self::arbitrary_uid_with_type(
                                &entity_type_name,
                                hierarchy,
                                u,
                            )?))
                        }
                        // `principal`
                        13..=18 => Ok(ast::Expr::var(ast::Var::Principal)),
                        // `action`
                        19..=24 => Ok(ast::Expr::var(ast::Var::Action)),
                        // `resource`
                        25..=30 => Ok(ast::Expr::var(ast::Var::Resource)),
                        // if-then-else expression, where both arms are entities with the appropriate type
                        31 | 32 => Ok(ast::Expr::ite(
                            self.arbitrary_expr_for_type(
                                &Type::bool(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                            self.arbitrary_expr_for_schematype(
                                target_type,
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                            self.arbitrary_expr_for_schematype(
                                target_type,
                                hierarchy,
                                max_depth - 1,
                                u,
                            )?,
                        )),
                        // extension function that returns an entity
                        33 => {
                            // TODO: this doesn't guarantee it returns the _correct_ entity type
                            self.arbitrary_ext_func_call_for_type(
                                &Type::entity(),
                                hierarchy,
                                max_depth - 1,
                                u,
                            )
                        }
                        // getting an attr (on an entity) with the appropriate entity type
                        34..=39 => {
                            let (entity_type, attr_name) =
                                self.arbitrary_attr_for_schematype(target_type.clone(), u)?;
                            Ok(ast::Expr::get_attr(
                                self.arbitrary_expr_for_schematype(
                                    &entity_type_name_to_schema_type(&entity_type),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        }
                        // getting an attr (on a record) with the appropriate entity type
                        40..=44 => {
                            let attr_name = self.constant_pool.arbitrary_string_constant(u)?;
                            Ok(ast::Expr::get_attr(
                                self.arbitrary_expr_for_schematype(
                                    &record_schematype_with_attr(
                                        attr_name.clone(),
                                        target_type.clone(),
                                    ),
                                    hierarchy,
                                    max_depth - 1,
                                    u,
                                )?,
                                attr_name,
                            ))
                        }
                        n => panic!("bad index: {n}"),
                    }
                }
            }
            SchemaTypeVariant::Extension { name } => match name.as_str() {
                "ipaddr" => self.arbitrary_expr_for_type(&Type::ipaddr(), hierarchy, max_depth, u),
                "decimal" => {
                    self.arbitrary_expr_for_type(&Type::decimal(), hierarchy, max_depth, u)
                }
                _ => panic!("unrecognized extension type: {name:?}"),
            },
        }
    }

    /// get an arbitrary constant of a given type, as an expression.
    ///
    /// If `hierarchy` is present, any literal UIDs included in the Expr will
    /// (usually) exist in the hierarchy.
    #[allow(dead_code)]
    fn arbitrary_const_expr_for_type(
        &self,
        target_type: &Type,
        hierarchy: Option<&super::Hierarchy>,
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
                        None => self.arbitrary_const_expr(hierarchy, u)?,
                        Some(el_ty) => self.arbitrary_const_expr_for_type(el_ty, hierarchy, u)?,
                    };
                    l.push(el);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::set(l))
            }
            Type::Record => {
                let mut r = Vec::new();
                u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
                    let (attr_name, _) = self.arbitrary_attr(u)?;
                    r.push((attr_name.clone(), self.arbitrary_const_expr(hierarchy, u)?));
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ast::Expr::record(r))
            }
            Type::Entity => {
                match u.int_in_range(0..=3)? {
                    // UID literal, that exists
                    0..=2 => Ok(ast::Expr::val(self.arbitrary_uid(hierarchy, u)?)),
                    // UID literal, that doesn't exist
                    3 => Ok(ast::Expr::val(
                        Self::arbitrary_specified_uid_without_schema(u)?,
                    )),
                    n => panic!("bad index: {n}"),
                }
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
    fn arbitrary_ext_func_call_for_type(
        &self,
        target_type: &Type,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        let func = self.ext_funcs.arbitrary_for_type(target_type, u)?;
        assert_eq!(&func.return_ty, target_type);
        let args = func
            .parameter_types
            .iter()
            .map(|param_ty| self.arbitrary_expr_for_type(param_ty, hierarchy, max_depth, u))
            .collect::<Result<_>>()?;
        Ok(ast::Expr::call_extension_fn(func.name.clone(), args))
    }

    /// internal helper function: get an extension-function-call expression that
    /// returns the given schematype
    ///
    /// `max_depth`: maximum depth of each argument expression.
    /// For instance, maximum depth of nested sets. Not to be confused with the
    /// `depth` parameter to size_hint.
    fn arbitrary_ext_func_call_for_schematype(
        &self,
        target_type: &amzn_cedar_validator::SchemaTypeVariant,
        hierarchy: Option<&super::Hierarchy>,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::Expr> {
        use amzn_cedar_validator::SchemaTypeVariant;
        match target_type {
            SchemaTypeVariant::Boolean => {
                self.arbitrary_ext_func_call_for_type(&Type::bool(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Long => {
                self.arbitrary_ext_func_call_for_type(&Type::long(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::String => {
                self.arbitrary_ext_func_call_for_type(&Type::string(), hierarchy, max_depth, u)
            }
            SchemaTypeVariant::Extension { name } => match name.as_str() {
                "ipaddr" => {
                    self.arbitrary_ext_func_call_for_type(&Type::ipaddr(), hierarchy, max_depth, u)
                }
                "decimal" => {
                    self.arbitrary_ext_func_call_for_type(&Type::decimal(), hierarchy, max_depth, u)
                }
                _ => panic!("unrecognized extension type: {name:?}"),
            },
            // no existing extension functions return set type
            SchemaTypeVariant::Set { .. } => Err(Error::EmptyChoose {
                doing_what: "getting an extension function returning set type",
            }),
            // no existing extension functions return record type
            SchemaTypeVariant::Record { .. } => Err(Error::EmptyChoose {
                doing_what: "getting an extension function returning record type",
            }),
            // no existing extension functions return entity type
            SchemaTypeVariant::Entity { .. } => Err(Error::EmptyChoose {
                doing_what: "getting an extension function returning entity type",
            }),
        }
    }

    /// get an arbitrary policy conforming to this schema
    pub fn arbitrary_policy(
        &self,
        hierarchy: &super::Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<ABACPolicy> {
        let id = u.arbitrary()?;
        let annotations = u.arbitrary()?;
        let effect = u.arbitrary()?;
        let principal_constraint = self.arbitrary_principal_constraint(hierarchy, u)?;
        let action_constraint = self.arbitrary_action_constraint(u, Some(3))?;
        let resource_constraint = self.arbitrary_resource_constraint(hierarchy, u)?;
        let mut abac_constraints = Vec::new();
        u.arbitrary_loop(Some(0), Some(self.settings.max_depth as u32), |u| {
            if self.settings.match_types {
                abac_constraints.push(self.arbitrary_expr_for_type(
                    &Type::bool(),
                    Some(hierarchy),
                    self.settings.max_depth,
                    u,
                )?);
            } else {
                abac_constraints.push(self.arbitrary_expr(
                    Some(hierarchy),
                    self.settings.max_depth,
                    u,
                )?);
            }
            Ok(std::ops::ControlFlow::Continue(()))
        })?;
        let mut conjunction = ast::Expr::val(true);
        for constraint in abac_constraints {
            conjunction = ast::Expr::and(conjunction, constraint);
        }
        Ok(ABACPolicy(super::GeneratedPolicy {
            id,
            annotations,
            effect,
            principal_constraint,
            action_constraint,
            resource_constraint,
            abac_constraints: conjunction,
        }))
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
        hierarchy: &super::Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<PrincipalOrResourceConstraint> {
        // 20% of the time, NoConstraint; 40%, Eq; 40%, In
        match u.int_in_range::<u8>(1..=10)? {
            1..=2 => Ok(PrincipalOrResourceConstraint::NoConstraint),
            3..=6 => Ok(PrincipalOrResourceConstraint::Eq(
                self.arbitrary_principal_uid(Some(hierarchy), u)?,
            )),
            7..=10 => Ok(PrincipalOrResourceConstraint::In(
                self.arbitrary_principal_uid(Some(hierarchy), u)?,
            )),
            n => panic!("bad index: {n}"),
        }
    }
    fn arbitrary_principal_constraint_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            super::size_hint_for_range(1, 10),
            arbitrary::size_hint::or_all(&[
                (0, Some(0)),
                Self::arbitrary_principal_uid_size_hint(depth),
                Self::arbitrary_principal_uid_size_hint(depth),
            ]),
        )
    }

    fn arbitrary_resource_constraint(
        &self,
        hierarchy: &super::Hierarchy,
        u: &mut Unstructured<'_>,
    ) -> Result<PrincipalOrResourceConstraint> {
        // 20% of the time, NoConstraint; 40%, Eq; 40%, In
        match u.int_in_range::<u8>(1..=10)? {
            1..=2 => Ok(PrincipalOrResourceConstraint::NoConstraint),
            3..=6 => Ok(PrincipalOrResourceConstraint::Eq(
                self.arbitrary_resource_uid(Some(hierarchy), u)?,
            )),
            7..=10 => Ok(PrincipalOrResourceConstraint::In(
                self.arbitrary_resource_uid(Some(hierarchy), u)?,
            )),
            n => panic!("bad index: {n}"),
        }
    }
    fn arbitrary_resource_constraint_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            super::size_hint_for_range(1, 10),
            arbitrary::size_hint::or_all(&[
                (0, Some(0)),
                Self::arbitrary_resource_uid_size_hint(depth),
                Self::arbitrary_resource_uid_size_hint(depth),
            ]),
        )
    }

    fn arbitrary_action_constraint(
        &self,
        u: &mut Unstructured<'_>,
        max_list_length: Option<u32>,
    ) -> Result<ActionConstraint> {
        // 10% of the time, NoConstraint; 30%, Eq; 30%, In; 30%, InList
        match u.int_in_range::<u8>(1..=10)? {
            1 => Ok(ActionConstraint::NoConstraint),
            2..=4 => Ok(ActionConstraint::Eq(self.arbitrary_action_uid(u)?)),
            5..=7 => Ok(ActionConstraint::In(self.arbitrary_action_uid(u)?)),
            8..=10 => {
                let mut uids = vec![];
                u.arbitrary_loop(Some(0), max_list_length, |u| {
                    uids.push(self.arbitrary_action_uid(u)?);
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Ok(ActionConstraint::InList(uids))
            }
            n => panic!("bad index: {n}"),
        }
    }
    fn arbitrary_action_constraint_size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            super::size_hint_for_range(1, 10),
            arbitrary::size_hint::or_all(&[
                (0, Some(0)),
                Self::arbitrary_action_uid_size_hint(depth),
                Self::arbitrary_action_uid_size_hint(depth),
                (1, None), // not sure how to hint for arbitrary_loop()
            ]),
        )
    }

    pub fn arbitrary_request(
        &self,
        hierarchy: &super::Hierarchy,
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
        Ok(ABACRequest(super::Request {
            principal: match action
                .applies_to
                .as_ref()
                .and_then(|at| at.principal_types.as_ref())
            {
                None => self.arbitrary_uid_with_optional_type(None, Some(hierarchy), u)?, // unspecified principal
                Some(types) => {
                    // Assert that these are vec, so it's safe to draw from directly
                    let types: &Vec<_> = types;
                    let ty = u.choose(types).map_err(|e| {
                        while_doing("choosing one of the action principal types", e)
                    })?;
                    self.arbitrary_uid_with_optional_type(Some(ty), Some(hierarchy), u)?
                }
            },
            action: uid_for_action_name(self.namespace.clone(), action_name),
            resource: match action
                .applies_to
                .as_ref()
                .and_then(|at| at.resource_types.as_ref())
            {
                None => self.arbitrary_uid_with_optional_type(None, Some(hierarchy), u)?, // unspecified resource
                Some(types) => {
                    // Assert that these are vec, so it's safe to draw from directly
                    let types: &Vec<_> = types;
                    let ty = u
                        .choose(types)
                        .map_err(|e| while_doing("choosing one of the action resource types", e))?;
                    self.arbitrary_uid_with_optional_type(Some(ty), Some(hierarchy), u)?
                }
            },
            context: {
                let mut attributes: Vec<_> = action
                    .applies_to
                    .as_ref()
                    .map(|a| unwrap_attrs_or_context(&a.context).0)
                    .iter()
                    .flat_map(|a| a.iter())
                    .collect();
                attributes.sort();
                attributes
                    .iter()
                    .map(|(attr_name, attr_type)| {
                        Ok((
                            attr_name.parse().expect("failed to parse attribute name"),
                            self.arbitrary_attr_value_for_schematype(
                                &attr_type.ty,
                                Some(hierarchy),
                                self.settings.max_depth,
                                u,
                            )?
                            .into(),
                        ))
                    })
                    .collect::<Result<_>>()?
            },
        }))
    }
    pub fn arbitrary_request_size_hint(_depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and(
            super::size_hint_for_choose(None),
            (1, None), // TODO: more precise
        )
    }

    pub fn namespace(&self) -> &Option<SmolStr> {
        &self.namespace
    }

    /// Get the underlying schema file, as a NamespaceDefinition
    pub fn schemafile(&self) -> &NamespaceDefinition {
        &self.schema
    }

    /// Get the underlying schema file, as a String containing JSON
    pub fn schemafile_string(&self) -> String {
        self.schema.to_string()
    }
}

impl From<Schema> for SchemaFragment {
    fn from(schema: Schema) -> SchemaFragment {
        SchemaFragment(
            HashMap::from_iter([(schema.namespace.unwrap_or_default(), schema.schema)].into_iter())
                .into(),
        )
    }
}
