/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
use cedar_drt_inner::schemas::equivalence_check;
use cedar_drt_inner::*;
use cedar_policy_generators::{schema::Schema, settings::ABACSettings};
use cedar_policy_validator::SchemaFragment;
use libfuzzer_sys::arbitrary::{self, Arbitrary, MaxRecursionReached, Unstructured};
use serde::Serialize;
use std::collections::HashMap;

#[derive(Debug, Clone, Serialize)]
struct Input {
    pub schema: SchemaFragment,
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
        let namespace = arb_schema.schema;
        let name = arb_schema.namespace;

        let schema = SchemaFragment(HashMap::from([(name, namespace)]));

        Ok(Self { schema })
    }

    fn try_size_hint(
        depth: usize,
    ) -> std::result::Result<(usize, Option<usize>), MaxRecursionReached> {
        Schema::arbitrary_size_hint(depth)
    }
}

fuzz_target!(|i: Input| {
    let src = i.schema.as_natural_schema().unwrap();
    let (parsed, _) = SchemaFragment::from_str_natural(&src).unwrap();
    if let Err(msg) = equivalence_check(i.schema.clone(), parsed) {
        println!("Schema: {src}");
        println!("LHS:\n{:?}", i.schema);
        println!("RHS:\n{:?}", i.schema);
        panic!("{msg}");
    }
});
