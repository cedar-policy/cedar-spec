use crate::{err::Result, schema::Schema};
use arbitrary::Unstructured;
use cedar_policy_core::{ast::EntityType, validator::ValidatorSchema as CoreSchema};

pub trait SchemaGen: std::fmt::Debug {
    fn arbitrary_entity_type(&self, u: &mut Unstructured<'_>) -> Result<EntityType>;
}

#[derive(Debug)]
pub struct ValidatorSchema<'a> {
    core_schema: &'a CoreSchema,
    entity_types: Vec<EntityType>,
}

impl<'a> ValidatorSchema<'a> {
    pub fn new(core_schema: &'a CoreSchema) -> Self {
        let entity_types = core_schema.entity_type_names().cloned().collect();
        Self {
            core_schema,
            entity_types,
        }
    }
}

impl SchemaGen for ValidatorSchema<'_> {
    fn arbitrary_entity_type(&self, u: &mut Unstructured<'_>) -> Result<EntityType> {
        Ok(u.choose(&self.entity_types)?.clone())
    }
}

impl SchemaGen for Schema {
    fn arbitrary_entity_type(&self, u: &mut Unstructured<'_>) -> Result<EntityType> {
        Ok(u.choose(&self.entity_types)?.clone())
    }
}
