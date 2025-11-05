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

use cedar_drt_inner::{fuzz_target, roundtrip_entities};

use cedar_policy::{Entities, Schema};

use cedar_policy_generators::{
    hierarchy::HierarchyGenerator, schema, schema_gen::SchemaGen, settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};

#[derive(Debug)]
struct FuzzTargetInput {
    pub schema: Schema,
    pub entities: Entities,
}

const SETTINGS: ABACSettings = ABACSettings {
    max_depth: 10,
    max_width: 10,
    ..ABACSettings::type_directed()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let entities: Entities = schema
            .arbitrary_hierarchy(u)?
            .try_into()
            .expect("Should be able to get entities from hierarchy.");
        let schema =
            Schema::try_from(schema).expect("Should be able to get validator schema from schema.");
        Ok(Self { entities, schema })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    roundtrip_entities::fuzz_target(input.entities, Some(input.schema));
});
