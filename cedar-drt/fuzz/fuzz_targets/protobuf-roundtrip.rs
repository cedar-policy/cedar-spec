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

use cedar_drt_inner::roundtrip_entities;
use cedar_drt_inner::{fuzz_target, schemas::Equiv};

use cedar_policy::{proto, Entities, Entity, Policy, PolicySet, Request, Schema};

use libfuzzer_sys::arbitrary::{self, MaxRecursionReached};
use prost::Message;

use crate::arbitrary::Arbitrary;
use crate::arbitrary::Unstructured;
use cedar_policy_generators::{
    abac::ABACPolicy, abac::ABACRequest, hierarchy::HierarchyGenerator, schema,
    settings::ABACSettings,
};

#[derive(Debug, Clone)]
struct FuzzTargetInput {
    request: ABACRequest,
    policy: ABACPolicy,
    entities: Entities,
    schema: Schema,
}

// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    enable_arbitrary_func_call: false,
    ..ABACSettings::undirected()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let request = schema.arbitrary_request(&hierarchy, u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;

        let entities = Entities::from_entities(
            hierarchy.entities().map(|x| Entity::from(x.to_owned())),
            None,
        )
        .expect("Failed to create entities");

        let schema = schema
            .try_into()
            .expect("Failed to convert schema to ValidatorSchema");

        Ok(Self {
            request,
            policy,
            entities,
            schema,
        })
    }

    fn try_size_hint(depth: usize) -> Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    let policy = Policy::from(input.policy);
    let mut policies = PolicySet::new();
    policies.add(policy).expect("Failed to add policy");
    let request = Request::from(input.request);

    roundtrip_policies(policies);
    roundtrip_request(request);
    roundtrip_entities(input.entities);
    roundtrip_schema(input.schema);
});

fn roundtrip_policies(policies: PolicySet) {
    let policies_proto = proto::models::PolicySet::from(&policies);
    let buf = policies_proto.encode_to_vec();
    let roundtripped_proto = proto::models::PolicySet::decode(&buf[..])
        .expect("Failed to deserialize PolicySet from proto");
    let roundtripped = PolicySet::try_from(&roundtripped_proto)
        .expect("Failed to convert from proto to PolicySet");
    assert_eq!(policies, roundtripped);
}

fn roundtrip_entities(entities: Entities) {
    let entities_proto = proto::models::Entities::from(&entities);
    let buf = entities_proto.encode_to_vec();
    let roundtriped_proto = proto::models::Entities::decode(&buf[..])
        .expect("Failed to deserialize Entities from proto");
    let roundtripped = Entities::from(&roundtriped_proto);
    roundtrip_entities::pretty_assert_entities_deep_eq(&entities, &roundtripped);
}

fn roundtrip_request(request: Request) {
    let request_proto = proto::models::Request::from(&request);
    let buf = request_proto.encode_to_vec();
    let roundtriped_proto =
        proto::models::Request::decode(&buf[..]).expect("Failed to deserialize Request from proto");
    let roundtripped = Request::from(&roundtriped_proto);
    assert_eq!(
        request.principal().map(|p| p.id()),
        roundtripped.principal().map(|p| p.id())
    );
    assert_eq!(
        request.action().map(|a| a.id()),
        roundtripped.action().map(|a| a.id())
    );
    assert_eq!(
        request.resource().map(|r| r.id()),
        roundtripped.resource().map(|r| r.id())
    );
    assert_eq!(
        request.context().map(|c| c.as_ref()),
        roundtripped.context().map(|c| c.as_ref())
    );
}

fn roundtrip_schema(schema: Schema) {
    let schema_proto = proto::models::Schema::from(&schema);
    let buf = schema_proto.encode_to_vec();
    let roundtriped_proto =
        proto::models::Schema::decode(&buf[..]).expect("Failed to deserialize Schema from proto");
    let roundtripped = Schema::from(&roundtriped_proto);
    Equiv::equiv(schema.as_ref(), roundtripped.as_ref()).unwrap();
}
