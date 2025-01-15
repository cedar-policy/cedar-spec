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

use libfuzzer_sys::arbitrary::{self, MaxRecursionReached};
use prost::Message;

use crate::arbitrary::Arbitrary;
use crate::arbitrary::Unstructured;
use cedar_drt::{AuthorizationRequestMsg, OwnedAuthorizationRequestMsg};
use cedar_drt_inner::{fuzz_target, schemas::Equiv};
use cedar_policy_core::{
    ast, entities::Entities, entities::NoEntitiesSchema, entities::TCComputation,
    extensions::Extensions,
};
use cedar_policy_generators::{
    abac::ABACPolicy, abac::ABACRequest, hierarchy::HierarchyGenerator, schema::Schema,
    settings::ABACSettings,
};

#[derive(Debug)]
struct FuzzTargetInput {
    request: ABACRequest,
    policy: ABACPolicy,
    entities: Entities,
    schema: cedar_policy_validator::ValidatorSchema,
}

// settings for this fuzz target
// copy-pasted from abac.rs
const SETTINGS: ABACSettings = ABACSettings {
    match_types: false,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: false,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
    // It's Ok to enable this flag because this target is PBT
    enable_datetime_extension: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let request = schema.arbitrary_request(&hierarchy, u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;

        let entities: Entities = Entities::from_entities(
            hierarchy.entities().map(|x| x.to_owned()),
            None::<&NoEntitiesSchema>,
            TCComputation::AssumeAlreadyComputed,
            Extensions::none(),
        )
        .expect("Failed to create entities");

        Ok(Self {
            request,
            policy,
            entities,
            schema: schema
                .try_into()
                .expect("Failed to convert schema to ValidatorSchema"),
        })
    }

    fn try_size_hint(depth: usize) -> Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ]))
    }
}

fuzz_target!(|input: FuzzTargetInput| {
    let s_policy: ast::StaticPolicy = input.policy.into();
    let mut policies: ast::PolicySet = ast::PolicySet::new();
    policies.add(s_policy.into()).expect("Failed to add policy");
    roundtrip_authz_request_msg(AuthorizationRequestMsg {
        request: &input.request.into(),
        policies: &policies,
        entities: &input.entities,
    });
    roundtrip_schema(input.schema);
});

fn roundtrip_authz_request_msg(auth_request: AuthorizationRequestMsg) {
    // AST -> Protobuf
    let auth_request_proto = cedar_drt::proto::AuthorizationRequestMsg::from(&auth_request);

    // Protobuf -> Bytes
    let buf = auth_request_proto.encode_to_vec();

    // Bytes -> Protobuf
    let roundtripped_proto = cedar_drt::proto::AuthorizationRequestMsg::decode(&buf[..])
        .expect("Failed to deserialize AuthorizationRequestMsg from proto");

    // Protobuf -> AST
    let roundtripped = OwnedAuthorizationRequestMsg::from(roundtripped_proto);

    // Checking request equality (ignores loc field)
    assert_eq!(
        auth_request.request.principal().uid(),
        roundtripped.request.principal().uid()
    );
    assert_eq!(
        auth_request.request.action().uid(),
        roundtripped.request.action().uid()
    );
    assert_eq!(
        auth_request.request.resource().uid(),
        roundtripped.request.resource().uid()
    );
    assert_eq!(
        auth_request.request.context(),
        roundtripped.request.context()
    );

    // Checking policy set equality
    assert_eq!(auth_request.policies, &roundtripped.policies);

    // Checking entities equality
    assert_eq!(auth_request.entities, &roundtripped.entities);
}

fn roundtrip_schema(schema: cedar_policy_validator::ValidatorSchema) {
    // AST -> Protobuf bytes
    let schema_proto = cedar_policy_validator::proto::ValidatorSchema::from(&schema);

    // Protobuf -> Bytes
    let buf = schema_proto.encode_to_vec();

    // Bytes -> Protobuf
    let roundtripped_proto = cedar_policy_validator::proto::ValidatorSchema::decode(&buf[..])
        .expect("Failed to deserialize Schema from proto");

    // Protobuf -> AST
    let roundtripped = cedar_policy_validator::ValidatorSchema::from(&roundtripped_proto);

    // Checking schema equivalence
    Equiv::equiv(&schema, &roundtripped).unwrap();
}
