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
use cedar_drt_inner::{schemas::validator_schema_attr_types_equivalent, *};
use cedar_policy_core::ast;
use cedar_policy_generators::{
    schema::{downgrade_frag_to_raw, Schema},
    settings::ABACSettings,
};
use cedar_policy_validator::json_schema;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::info;
use serde::Serialize;
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize)]
struct Input {
    pub schema: json_schema::Fragment<ast::InternalName>,
    pub schema_with_common_types: json_schema::Fragment<ast::InternalName>,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: false,
    enable_extensions: true,
    max_depth: 3,
    max_width: 7,
    enable_additional_attributes: false,
    enable_like: true,
    // ABAC fuzzing restricts the use of action because it is used to generate
    // the corpus tests which will be run on Cedar and CedarCLI.
    // These packages only expose the restricted action behavior.
    enable_action_groups_and_attrs: false,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for Input {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let arb_schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let namespace = &arb_schema.schema;
        let name = &arb_schema.namespace;

        let schema = json_schema::Fragment(HashMap::from([(name.clone(), namespace.clone())]));

        let namespace_with_common_types = arb_schema.add_common_types(u)?;
        let schema_with_common_types = json_schema::Fragment(HashMap::from_iter([(
            name.clone(),
            namespace_with_common_types,
        )]));

        Ok(Self {
            schema,
            schema_with_common_types,
        })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        Schema::arbitrary_size_hint(depth)
    }
}

fuzz_target!(|i: Input| {
    info!("schemas: {i:?}");
    let validator_schema1: Result<cedar_policy_validator::ValidatorSchema, _> =
        downgrade_frag_to_raw(i.schema).try_into();
    let validator_schema2: Result<cedar_policy_validator::ValidatorSchema, _> =
        downgrade_frag_to_raw(i.schema_with_common_types).try_into();
    match (validator_schema1, validator_schema2) {
        (Ok(s1), Ok(s2)) => {
            assert!(
                validator_schema_attr_types_equivalent(&s1, &s2),
                "reduced to different validator schemas: {:?}\n{:?}\n",
                s1,
                s2
            );
        }
        (Err(_), Err(_)) => {}
        (Ok(s), Err(_)) | (Err(_), Ok(s)) => {
            panic!("reduction results differ, got validator schema: {:?}\n", s);
        }
    }
});
