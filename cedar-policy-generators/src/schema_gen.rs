use std::collections::BTreeMap;

use crate::{
    abac::{self, AvailableExtensionFunctions, ConstantPool, QualifiedType, UnknownPool},
    collections::HashMap,
    err::{while_doing, Result},
    expr::ExprGenerator,
    hierarchy::Hierarchy,
    schema::Schema,
    settings::ABACSettings,
};
use arbitrary::Unstructured;
use cedar_policy_core::{
    ast::{self, EntityType},
    validator::{
        types::{self, OpenTag},
        ValidatorSchema as CoreSchema,
    },
};
use smol_str::SmolStr;

impl From<types::Type> for abac::Type {
    fn from(ty: types::Type) -> Self {
        match ty {
            types::Type::False
            | types::Type::True
            | types::Type::Primitive {
                primitive_type: types::Primitive::Bool,
            } => Self::Bool,
            types::Type::Primitive {
                primitive_type: types::Primitive::Long,
            } => Self::Long,
            types::Type::Primitive {
                primitive_type: types::Primitive::String,
            } => Self::String,
            types::Type::Never => {
                unreachable!("validated schema shouldn't contain such type variant")
            }
            types::Type::EntityOrRecord(types::EntityRecordKind::ActionEntity { name, .. }) => {
                Self::Entity(name)
            }
            types::Type::EntityOrRecord(types::EntityRecordKind::AnyEntity) => {
                unreachable!("validated schema shouldn't contain such type variant")
            }
            types::Type::EntityOrRecord(types::EntityRecordKind::Entity(lub)) => Self::Entity(
                lub.into_single_entity()
                    .expect("should contain just one element"),
            ),
            types::Type::EntityOrRecord(types::EntityRecordKind::Record { attrs, .. }) => {
                Self::record(attrs.into_iter().map(|(a, ty)| {
                    (
                        a,
                        QualifiedType {
                            ty: Box::new(ty.attr_type.into()),
                            required: ty.is_required,
                        },
                    )
                }))
            }
            types::Type::Set { element_type } => Self::Set(Box::new(
                (*element_type.expect("validated schema shouldn't contain such type")).into(),
            )),
            types::Type::ExtensionType { name } if name.to_string() == "datetime" => Self::DateTime,
            types::Type::ExtensionType { name } if name.to_string() == "duration" => Self::Duration,
            types::Type::ExtensionType { name } if name.to_string() == "ipaddr" => Self::IPAddr,
            types::Type::ExtensionType { name } if name.to_string() == "decimal" => Self::Decimal,
            types::Type::ExtensionType { .. } => unreachable!("invalid extension name"),
        }
    }
}

/// A trait that specifies what methods other generators expect from a schema
pub trait SchemaGen: std::fmt::Debug {
    /// Gen all entity types
    fn entity_types(&self) -> Box<dyn Iterator<Item = EntityType> + '_>;
    /// Get an arbitrary entity type
    fn arbitrary_entity_type(&self, u: &mut Unstructured<'_>) -> Result<EntityType>;
    /// Get an arbitrary attribute
    fn arbitrary_attr(&self, u: &mut Unstructured<'_>) -> Result<SmolStr>;
    /// Get an arbitrary attribute of type `target_type`
    fn arbitrary_attr_for_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<&(ast::EntityType, SmolStr)>;
    /// Get an arbitrary entity type that has tag type `target_type`
    fn arbitrary_entity_type_with_tag_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityType>;
    /// Get an arbitrary attribute of an entity type
    fn arbitrary_attr_of_entity_type(
        &self,
        entity_type: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<SmolStr>;
    /// Get uid choices of an entity type
    fn get_uid_enum_choices(&self, ty: &ast::EntityType) -> Vec<SmolStr>;
    /// Get an arbitrary principal type
    fn arbitrary_principal_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType>;
    /// Get an arbitrary resource type
    fn arbitrary_resource_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType>;
    /// Get an arbitrary action
    fn arbitrary_action_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID>;
    /// Get allowed parent type names
    fn allowed_parent_typenames(
        &self,
        ety: &EntityType,
    ) -> Option<Box<dyn Iterator<Item = EntityType> + '_>>;
    /// Get attribute types and whether there are additional attributes
    fn attribute_by_entity_type(
        &self,
        ety: &EntityType,
    ) -> Option<(BTreeMap<SmolStr, QualifiedType>, bool)>;
    /// Get tag type of an entity type
    fn tag_type_by_entity_type(&self, ety: &EntityType) -> Option<Option<abac::Type>>;
    /// Get settings
    fn get_abac_settings(&self) -> &ABACSettings;
    /// Get an expression generator
    fn exprgenerator<'s>(&'s self, hierarchy: Option<&'s Hierarchy>) -> ExprGenerator<'s>;
}

/// A wrapper around the validator schema of core
#[derive(Debug)]
pub struct ValidatorSchema<'a> {
    core_schema: &'a CoreSchema,
    entity_types: Vec<EntityType>,
    attributes: Vec<(SmolStr, abac::Type)>,
    attributes_by_type: HashMap<abac::Type, Vec<(ast::EntityType, SmolStr)>>,
    settings: &'a ABACSettings,
    constant_pool: ConstantPool,
    unknown_pool: UnknownPool,
    ext_funcs: AvailableExtensionFunctions,
}

impl<'a> ValidatorSchema<'a> {
    /// Create such wrapper
    pub fn new(
        core_schema: &'a CoreSchema,
        settings: &'a ABACSettings,
        u: &mut Unstructured<'_>,
    ) -> Result<Self> {
        let entity_types = core_schema.entity_type_names().cloned().collect();
        let attributes_by_type = Self::build_attributes(core_schema);
        let attributes = attributes_by_type
            .iter()
            .flat_map(|(ty, pairs)| {
                pairs
                    .iter()
                    .map(move |(_, attr)| (attr.clone(), ty.clone()))
            })
            .collect();
        Ok(Self {
            core_schema,
            entity_types,
            attributes,
            attributes_by_type,
            settings,
            constant_pool: u.arbitrary()?,
            unknown_pool: UnknownPool::default(),
            ext_funcs: AvailableExtensionFunctions::create(&settings),
        })
    }
    fn build_attributes(
        core_schema: &'a CoreSchema,
    ) -> HashMap<abac::Type, Vec<(ast::EntityType, SmolStr)>> {
        let mut attributes = HashMap::new();
        for et in core_schema.entity_types() {
            for (attr, ty) in et.attributes().iter() {
                let attr_type = abac::Type::from(ty.attr_type.clone());
                attributes
                    .entry(attr_type)
                    .or_insert_with(Vec::new)
                    .push((et.name().clone(), attr.clone()));
            }
        }
        attributes
    }
}

impl SchemaGen for ValidatorSchema<'_> {
    fn arbitrary_entity_type(&self, u: &mut Unstructured<'_>) -> Result<EntityType> {
        Ok(u.choose(&self.entity_types)?.clone())
    }
    fn arbitrary_attr(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        Ok(u.choose(&self.attributes).map(|(a, _)| a.clone())?)
    }
    fn arbitrary_attr_for_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<&(ast::EntityType, SmolStr)> {
        match self.attributes_by_type.get(target_type) {
            Some(vec) => u.choose(vec).map_err(|e| {
                while_doing(
                    format!("getting arbitrary attr for type {target_type:?}"),
                    e,
                )
            }),
            None => Err(crate::err::Error::EmptyChoose {
                doing_what: format!("getting arbitrary attr for type {target_type:?}"),
            }),
        }
    }
    fn arbitrary_entity_type_with_tag_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityType> {
        let candidates: Vec<ast::EntityType> = self
            .core_schema
            .entity_types()
            .filter_map(|ty| match ty.tag_type() {
                Some(t) if &abac::Type::from(t.clone()) == target_type => Some(ty.name().clone()),
                _ => None,
            })
            .collect();
        u.choose(&candidates).cloned().map_err(|e| {
            while_doing(
                format!("getting entity type with tag schematype {target_type:?}"),
                e,
            )
        })
    }
    fn arbitrary_attr_of_entity_type(
        &self,
        entity_type: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<SmolStr> {
        Ok(u.choose(
            &self
                .core_schema
                .get_entity_type(entity_type)
                .expect("entity type should exist")
                .attributes()
                .iter()
                .map(|a| a.0.clone())
                .collect::<Vec<_>>(),
        )?
        .clone())
    }
    fn arbitrary_action_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        Ok(
            u.choose(&self.core_schema.action_ids().collect::<Vec<_>>())?
                .name()
                .clone(),
        )
    }
    fn arbitrary_principal_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        let principals: Vec<_> = self.core_schema.principals().cloned().collect();
        Ok(u.choose(&principals)?.clone())
    }
    fn arbitrary_resource_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        let resources: Vec<_> = self.core_schema.resources().cloned().collect();
        Ok(u.choose(&resources)?.clone())
    }
    fn get_uid_enum_choices(&self, ty: &ast::EntityType) -> Vec<SmolStr> {
        self.core_schema
            .get_entity_type(ty)
            .map_or(vec![], |ty| match &ty.kind {
                cedar_policy_core::validator::ValidatorEntityTypeKind::Enum(choices) => {
                    choices.into_iter().cloned().collect()
                }
                cedar_policy_core::validator::ValidatorEntityTypeKind::Standard(_) => vec![],
            })
    }
    fn entity_types(&self) -> Box<dyn Iterator<Item = EntityType> + '_> {
        Box::new(self.entity_types.clone().into_iter())
    }
    fn allowed_parent_typenames(
        &self,
        ety: &EntityType,
    ) -> Option<Box<dyn Iterator<Item = EntityType> + '_>> {
        self.core_schema.get_entity_type(ety).map(|_| {
            let parent_types: Vec<EntityType> = self
                .core_schema
                .entity_types()
                .filter(|t| t.has_descendant_entity_type(ety))
                .map(|t| t.name().clone())
                .collect();
            Box::new(parent_types.into_iter()) as Box<dyn Iterator<Item = EntityType> + '_>
        })
    }
    fn attribute_by_entity_type(
        &self,
        ety: &EntityType,
    ) -> Option<(BTreeMap<SmolStr, QualifiedType>, bool)> {
        self.core_schema.get_entity_type(ety).map(|ty| {
            (
                ty.attributes()
                    .iter()
                    .map(|(a, q)| {
                        (
                            a.clone(),
                            QualifiedType {
                                ty: Box::new(q.attr_type.clone().into()),
                                required: q.is_required,
                            },
                        )
                    })
                    .collect(),
                matches!(ty.open_attributes(), OpenTag::OpenAttributes),
            )
        })
    }
    fn tag_type_by_entity_type(&self, ety: &EntityType) -> Option<Option<abac::Type>> {
        self.core_schema
            .get_entity_type(ety)
            .map(|ty| ty.tag_type().map(|ty| abac::Type::from(ty.clone())))
    }
    fn get_abac_settings(&self) -> &ABACSettings {
        self.settings
    }
    fn exprgenerator<'s>(&'s self, hierarchy: Option<&'s Hierarchy>) -> ExprGenerator<'s> {
        ExprGenerator {
            schema: self,
            settings: self.settings,
            constant_pool: &self.constant_pool,
            unknown_pool: &self.unknown_pool,
            ext_funcs: &self.ext_funcs,
            hierarchy,
        }
    }
}

impl SchemaGen for Schema {
    fn arbitrary_entity_type(&self, u: &mut Unstructured<'_>) -> Result<EntityType> {
        Ok(u.choose(&self.entity_types)?.clone())
    }
    fn arbitrary_attr(&self, u: &mut Unstructured<'_>) -> Result<SmolStr> {
        self.arbitrary_attr(u)
    }
    fn arbitrary_attr_for_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<&(ast::EntityType, SmolStr)> {
        self.arbitrary_attr_for_type(target_type, u)
    }
    fn arbitrary_entity_type_with_tag_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityType> {
        self.arbitrary_entity_type_with_tag_type(target_type, u)
    }
    fn arbitrary_attr_of_entity_type(
        &self,
        entity_type: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<SmolStr> {
        self.arbitrary_attr_of_entity_type(entity_type, u)
    }
    fn arbitrary_action_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        self.arbitrary_action_uid(u)
    }
    fn arbitrary_principal_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        // TODO: figure out if we need to qualify them with ns
        Ok(u.choose(&self.principal_types).cloned()?)
    }
    fn arbitrary_resource_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        // TODO: figure out if we need to qualify them with ns
        Ok(u.choose(&self.resource_types).cloned()?)
    }
    fn get_uid_enum_choices(&self, ty: &ast::EntityType) -> Vec<SmolStr> {
        self.get_uid_enum_choices(ty)
    }
    fn entity_types(&self) -> Box<dyn Iterator<Item = EntityType> + '_> {
        Box::new(self.entity_types.clone().into_iter())
    }
    fn allowed_parent_typenames(
        &self,
        ety: &EntityType,
    ) -> Option<Box<dyn Iterator<Item = EntityType> + '_>> {
        self.allowed_parent_typenames(ety)
            .map(|iter| Box::new(iter) as Box<dyn Iterator<Item = EntityType> + '_>)
    }
    fn attribute_by_entity_type(
        &self,
        ety: &EntityType,
    ) -> Option<(BTreeMap<SmolStr, QualifiedType>, bool)> {
        self.attribute_by_entity_type(ety)
    }
    fn tag_type_by_entity_type(&self, ety: &EntityType) -> Option<Option<abac::Type>> {
        self.tag_type_by_entity_type(ety)
    }
    fn get_abac_settings(&self) -> &ABACSettings {
        &self.settings
    }
    fn exprgenerator<'s>(&'s self, hierarchy: Option<&'s Hierarchy>) -> ExprGenerator<'s> {
        self.exprgenerator(hierarchy)
    }
}
