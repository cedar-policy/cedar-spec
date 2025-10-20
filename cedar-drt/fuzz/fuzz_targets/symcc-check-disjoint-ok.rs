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
use cedar_drt::logger::initialize_log;

use cedar_drt_inner::{
    fuzz_target,
    symcc::{total_action_request_env_limit, PolicySetPairTask, ValidationTask},
};

use cedar_policy::{PolicySet, Schema};

use cedar_policy_generators::{
    abac::ABACPolicy, hierarchy::HierarchyGenerator, schema, settings::ABACSettings,
};

use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use std::convert::TryFrom;
use std::sync::LazyLock;

static RUNTIME: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
    tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
});

/// Input expected by this fuzz target.
#[derive(Debug, Clone)]
pub struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated policy
    pub policy1: ABACPolicy,
    /// generated policy
    pub policy2: ABACPolicy,
}

/// Settings for this fuzz target.
const SETTINGS: ABACSettings = ABACSettings {
    max_depth: 3,
    max_width: 3,
    total_action_request_env_limit: total_action_request_env_limit(),
    ..ABACSettings::type_directed()
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy1 = schema.arbitrary_policy(&hierarchy, u)?;
        let policy2 = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self {
            schema,
            policy1,
            policy2,
        })
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
    initialize_log();
    let mut policy_set1 = PolicySet::new();
    policy_set1.add(input.policy1.into()).unwrap();
    let mut policy_set2 = PolicySet::new();
    policy_set2.add(input.policy2.into()).unwrap();
    // Attempt to convert the generator schema to an actual schema.
    if let Ok(schema) = Schema::try_from(input.schema) {
        RUNTIME
            .block_on(PolicySetPairTask::CheckDisjoint.check_ok(schema, (policy_set1, policy_set2)))
            .unwrap();
    }
});
