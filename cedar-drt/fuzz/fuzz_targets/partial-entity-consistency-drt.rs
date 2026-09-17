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

//! DRT fuzz target checking that Rust and Lean agree on whether partial entities
//! are consistent with concrete entities.

#![no_main]
use cedar_drt::{logger::initialize_log, tests::drop_some_entities};
use cedar_drt_inner::{
    fuzz_target,
    tpe::{
        arbitrary_schema_and_entities, entities_to_partial_entities, schema_and_entities_size_hint,
        test_partial_entity_consistency_equiv,
    },
};

use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Entities, PartialEntities};

use cedar_policy_generators::settings::ABACSettings;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

/// Input expected by this fuzz target
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// partial entities derived from a generated hierarchy, with their attributes and
    /// tags optionally shuffled so that mismatched values are reachable
    pub partial_entities: PartialEntities,
    /// the same hierarchy with some entities dropped, so that missing entities and
    /// mismatched ancestors are reachable
    pub entities: Entities,
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let (schema, entities) = arbitrary_schema_and_entities(ABACSettings::undirected(), u)?;
        let partial_entities =
            entities_to_partial_entities(entities.iter(), u.arbitrary()?, u, &schema)?;
        Ok(Self {
            partial_entities,
            entities: drop_some_entities(entities, u)?,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        schema_and_entities_size_hint(depth)
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    test_partial_entity_consistency_equiv(
        &CedarLeanFfi::new(),
        &input.entities,
        &input.partial_entities,
    );
});
