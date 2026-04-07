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

use std::collections::BTreeMap;

use crate::{
    abac::{ConstantPool, QualifiedType, Type},
    err::Result,
    schema_gen::SchemaGen,
    settings::ABACSettings,
};
use arbitrary::Unstructured;

/// Generates types based on string constants and entity types available
#[derive(Debug)]
pub struct TypeGenerator<'a> {
    /// Schema, used to generate entity types drawn from the schema
    pub schema: &'a dyn SchemaGen,
    /// Constant pool, used to generate attribute names for record types
    pub constant_pool: &'a ConstantPool,
    /// General abac settings. Used here for maximum width of a type (number of attributes in record).
    pub settings: &'a ABACSettings,
}

impl TypeGenerator<'_> {
    /// Generate an arbitrary type, respecting `max_depth` and `max_width`
    pub fn generate_type(&self, max_depth: usize, u: &mut Unstructured<'_>) -> Result<Type> {
        if max_depth == 0 {
            // Reached max-depth, so no recursion. Record types are empty and
            // skips generating set types entirely. All other types generated.
            uniform!(
                u,
                Ok(Type::bool()),
                Ok(Type::long()),
                Ok(Type::string()),
                Ok(Type::ipaddr()),
                Ok(Type::decimal()),
                Ok(Type::datetime()),
                Ok(Type::duration()),
                Ok(Type::entity(self.schema.arbitrary_entity_type(u)?,)),
                Ok(Type::record([]))
            )
        } else {
            uniform!(
                u,
                Ok(Type::bool()),
                Ok(Type::long()),
                Ok(Type::string()),
                Ok(Type::ipaddr()),
                Ok(Type::decimal()),
                Ok(Type::datetime()),
                Ok(Type::duration()),
                Ok(Type::entity(self.schema.arbitrary_entity_type(u)?,)),
                Ok(Type::set_of(self.generate_type(max_depth - 1, u)?)),
                self.generate_record_type(max_depth, u)
            )
        }
    }

    pub(crate) fn generate_record_type(
        &self,
        max_depth: usize,
        u: &mut Unstructured<'_>,
    ) -> Result<Type> {
        let mut attrs = BTreeMap::new();
        u.arbitrary_loop(Some(0), Some(self.settings.max_width as u32), |u| {
            let ty = QualifiedType {
                ty: self.generate_type(max_depth - 1, u)?,
                required: u.arbitrary()?,
            };
            attrs.insert(self.constant_pool.arbitrary_string_constant(u)?, ty);
            Ok(std::ops::ControlFlow::Continue(()))
        })?;
        Ok(Type::record(attrs))
    }
}
