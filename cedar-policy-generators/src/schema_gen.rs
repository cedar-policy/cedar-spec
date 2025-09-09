use crate::{
    abac::{self, QualifiedType},
    err::Result,
    schema::Schema,
};
use arbitrary::Unstructured;
use cedar_policy_core::{
    ast::{self, EntityType},
    validator::{types, ValidatorSchema as CoreSchema},
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
}

/// A wrapper around the validator schema of core
#[derive(Debug)]
pub struct ValidatorSchema<'a> {
    core_schema: &'a CoreSchema,
    entity_types: Vec<EntityType>,
    attributes: Vec<(SmolStr, abac::Type)>,
}

impl<'a> ValidatorSchema<'a> {
    /// Create such wrapper
    pub fn new(core_schema: &'a CoreSchema) -> Self {
        let entity_types = core_schema.entity_type_names().cloned().collect();
        Self {
            core_schema,
            entity_types,
            attributes: Self::build_attributes(core_schema),
        }
    }
    fn build_attributes(core_schema: &'a CoreSchema) -> Vec<(SmolStr, abac::Type)> {
        let mut attributes = Vec::new();
        for et in core_schema.entity_types() {
            for (attr, ty) in et.attributes().iter() {
                attributes.push((attr.clone(), abac::Type::from(ty.attr_type.clone())));
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
        todo!()
    }
    fn arbitrary_entity_type_with_tag_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityType> {
        todo!()
    }
    fn arbitrary_attr_of_entity_type(
        &self,
        entity_type: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<SmolStr> {
        todo!()
    }
    fn arbitrary_action_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        todo!()
    }
    fn arbitrary_principal_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        todo!()
    }
    fn arbitrary_resource_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        todo!()
    }
    fn get_uid_enum_choices(&self, ty: &ast::EntityType) -> Vec<SmolStr> {
        todo!()
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
        todo!()
    }
    fn arbitrary_entity_type_with_tag_type(
        &self,
        target_type: &abac::Type,
        u: &mut Unstructured<'_>,
    ) -> Result<ast::EntityType> {
        todo!()
    }
    fn arbitrary_attr_of_entity_type(
        &self,
        entity_type: &ast::EntityType,
        u: &mut Unstructured<'_>,
    ) -> Result<SmolStr> {
        todo!()
    }
    fn arbitrary_action_uid(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityUID> {
        todo!()
    }
    fn arbitrary_principal_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        todo!()
    }
    fn arbitrary_resource_type(&self, u: &mut Unstructured<'_>) -> Result<ast::EntityType> {
        todo!()
    }
    fn get_uid_enum_choices(&self, ty: &ast::EntityType) -> Vec<SmolStr> {
        todo!()
    }
}
