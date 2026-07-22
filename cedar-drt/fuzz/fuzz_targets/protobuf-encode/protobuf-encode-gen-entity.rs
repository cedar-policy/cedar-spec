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
use cedar_drt_inner::props::entity_protobuf_decodes;

use cedar_policy::Entity;
use cedar_policy::proto::traits::{EncodeError, Protobuf};

use cedar_policy_generators::schema_gen::SchemaGen;
use cedar_policy_generators::{hierarchy::HierarchyGenerator, schema, settings::ABACSettings};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};

#[derive(Debug, Clone)]
struct FuzzTargetInput {
    entity: Entity,
}

const SETTINGS: ABACSettings = ABACSettings {
    enable_arbitrary_func_call: false,
    ..ABACSettings::undirected()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let entities: Vec<_> = hierarchy.entities().collect();
        if entities.is_empty() {
            return Err(arbitrary::Error::NotEnoughData);
        }
        let entity = (*u.choose(&entities)?).clone();
        Ok(Self {
            entity: Entity::from(entity),
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
        ]))
    }
}

// Generate an Entity using the ABAC generators, then encode to protobuf.
// Property: encoding a well-formed Entity must not panic, and decoding
// the result must produce an equivalent Entity.
fuzz_target!(|input: FuzzTargetInput| {
    let buf = match input.entity.encode() {
        Ok(buf) => buf,
        Err(EncodeError::MaxDepthExceeded) => return,
        Err(e) => panic!("only error expected encoding Entity is MaxDepthExceeded, got {e}"),
    };
    entity_protobuf_decodes(&buf[..], &input.entity);
});
