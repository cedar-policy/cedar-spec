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

//! Holds common structures used for defining the inputs to ABAC fuzz targets.

use cedar_drt::tests::drop_some_entities;
use cedar_policy::{Entities, Schema};
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    hierarchy::HierarchyGenerator,
    schema,
    schema_gen::SchemaGen,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Error, MaxRecursionReached, Unstructured};

use crate::schemas;

/// Common input used by ABAC fuzz targets:
/// An ABAC hierarchy, policy, and 8 associated requests
#[derive(Debug, Clone)]
pub struct FuzzTargetInput<const TYPE_DIRECTED: bool> {
    /// generated schema
    pub schema: schema::Schema,
    /// generated entity slice
    pub entities: Entities,
    /// generated policy
    pub policy: ABACPolicy,
    /// the requests to try for this hierarchy and policy. We try 8 requests per
    /// policy/hierarchy
    pub requests: [ABACRequest; 8],
}

impl<const TYPE_DIRECTED: bool> FuzzTargetInput<TYPE_DIRECTED> {
    pub const fn settings() -> ABACSettings {
        ABACSettings {
            max_depth: 3,
            max_width: 3,
            ..if TYPE_DIRECTED {
                ABACSettings::type_directed()
            } else {
                ABACSettings::undirected()
            }
        }
    }
}

impl<'a, const TYPE_DIRECTED: bool> Arbitrary<'a> for FuzzTargetInput<TYPE_DIRECTED> {
    fn arbitrary(u: &mut Unstructured<'_>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(Self::settings(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;

        let requests = [
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
        ];
        let all_entities = Entities::try_from(hierarchy).map_err(|_| Error::NotEnoughData)?;
        let cedar_schema = Schema::try_from(schema.clone()).unwrap();
        let entities = drop_some_entities(all_entities.into(), u)?.into();
        let entities = schemas::add_actions_to_entities(&cedar_schema, entities)?;
        Ok(Self {
            schema,
            entities,
            policy,
            requests,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&Self::settings(), depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}
