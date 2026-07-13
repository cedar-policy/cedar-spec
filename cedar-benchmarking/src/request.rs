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

use arbitrary::Unstructured;
use cedar_policy::Request;
use cedar_policy_core::ast;
use cedar_policy_core::validator::{json_schema::Fragment, RawName};
use cedar_policy_generators::{hierarchy::Hierarchy, settings::ABACSettings};
use rand::{rngs::StdRng, Rng, SeedableRng};

struct RandomBytes {
    bytes: Vec<u8>,
    rng: StdRng,
}

impl RandomBytes {
    fn new() -> Self {
        Self {
            bytes: vec![],
            rng: StdRng::seed_from_u64(666),
        }
    }

    fn unstructured(&mut self, num_bytes: usize) -> Unstructured<'_> {
        self.bytes.clear();
        self.bytes.resize_with(num_bytes, || self.rng.random());
        Unstructured::new(&self.bytes)
    }
}

/// Generate authorization requests from entities and a JSON schema fragment
pub fn generate_requests(
    entities: &cedar_policy_core::entities::Entities,
    schema: &Fragment<RawName>,
) -> Vec<Request> {
    let mut bytes = RandomBytes::new();
    let u = &mut bytes.unstructured(4096);
    let hierarchy: Hierarchy = entities.clone().into();
    let settings = ABACSettings::type_directed();
    #[expect(
        deprecated,
        reason = "from_raw_schemafrag is the only available constructor"
    )]
    let schema =
        cedar_policy_generators::schema::Schema::from_raw_schemafrag(schema.clone(), settings, u)
            .expect("should be a valid schema fragment");

    let mut requests: Vec<ast::Request> = Vec::with_capacity(500);
    requests.resize_with(500, || loop {
        let request: ast::Request = match schema.arbitrary_request(&hierarchy, u) {
            Ok(r) => r.into(),
            Err(_) => continue,
        };
        // Only keep requests with valid principal and resource from the hierarchy
        if hierarchy
            .uids()
            .iter()
            .any(|uid| request.principal().uid() == Some(uid))
            && hierarchy
                .uids()
                .iter()
                .any(|uid| request.resource().uid() == Some(uid))
        {
            break request;
        }
    });

    requests
        .into_iter()
        .map(|r| {
            Request::new(
                r.principal().uid().unwrap().to_string().parse().unwrap(),
                r.action().uid().unwrap().to_string().parse().unwrap(),
                r.resource().uid().unwrap().to_string().parse().unwrap(),
                r.context().unwrap().clone().into(),
                None,
            )
            .unwrap()
        })
        .collect()
}
