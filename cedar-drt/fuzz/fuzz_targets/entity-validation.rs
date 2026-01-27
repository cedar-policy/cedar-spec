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
use cedar_drt::{
    logger::{TOTAL_MSG, initialize_log},
    tests::run_ent_val_test,
};
use cedar_drt_inner::fuzz_target;

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Entities, Schema};
use cedar_testing::cedar_test_impl::time_function;

use cedar_policy_generators::{
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema,
    schema_gen::SchemaGen,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::{debug, info};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated hierarchy
    pub hierarchy: Hierarchy,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    enable_additional_attributes: true,
    ..ABACSettings::undirected()
};

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
    initialize_log();

    let engine = CedarLeanFfi::new();

    // generate a schema
    if let Ok(schema) = Schema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        if let Ok(entities) = Entities::try_from(input.hierarchy) {
            let (_, total_dur) = time_function(|| run_ent_val_test(&engine, schema, entities));
            info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
        }
    }
});
