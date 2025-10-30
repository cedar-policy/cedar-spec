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

#![no_main]
use cedar_drt_inner::fuzz_target;

use cedar_policy::{Entities, PartialEntities, Schema};

use cedar_policy_generators::{
    hierarchy::Hierarchy, hierarchy::HierarchyGenerator, schema, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use similar_asserts::assert_eq;

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated hierarchy
    pub hierarchy: Hierarchy,
}

const SETTINGS: ABACSettings = ABACSettings::type_directed();

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        Ok(Self { schema, hierarchy })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    if let Ok(schema) = Schema::try_from(input.schema) {
        if let Ok(entities) = Entities::try_from(input.hierarchy) {
            // Absent tags are 
            if entities.iter().all(|e| e.as_ref().tags_len() != 0) {
                let partial_entities_from_entities =
                    PartialEntities::from_concrete(entities.clone(), &schema).unwrap();
                let entities_json_value = entities.as_ref().to_json_value().unwrap();
                let partial_entities_from_json =
                    PartialEntities::from_json_value(entities_json_value, &schema).unwrap();
                assert_eq!(
                    from_entities: partial_entities_from_entities.as_ref(),
                    from_json: partial_entities_from_json.as_ref()
                );
            }
        }
    }
});
