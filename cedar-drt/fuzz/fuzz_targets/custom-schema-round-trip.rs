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
use std::collections::HashMap;

use anyhow::{Context, Result};
use cedar_drt::*;
use cedar_drt_inner::*;
use cedar_policy_core::ast::{self, PolicySet};
use cedar_policy_generators::{abac::ABACPolicy, schema::Schema, settings::ABACSettings};
use cedar_policy_validator::SchemaFragment;
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use serde::Serialize;

/// Input expected by this fuzz target
#[derive(Debug, Clone, Serialize)]
struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    /// generated policy
    pub policy: ABACPolicy,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        Ok(Self { schema, policy })
    }

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
        ])
    }
}

// round-tripping of a schema
// i.e., print a JSON schema to custom schema and parse/translate it back
fn round_trip(s: &Schema, ps: &PolicySet) -> Result<()> {
    let s = cedar_policy_validator::SchemaFragment(HashMap::from_iter(std::iter::once((
        s.namespace().map_or("".into(), |n| n.to_string().into()),
        s.schemafile().clone(),
    ))));
    let custom_schema_string = s.to_string();
    log::info!("custom schema: {custom_schema_string}");
    let custom_schema_ast =
        cedar_policy_validator::custom_schema::parser::parse_schema(&custom_schema_string)
            .context("parsing")?;
    let new_json_schema: SchemaFragment = custom_schema_ast.try_into().context("translation")?;
    let old_validator = s.try_into().map(Validator::new);
    let new_validator = new_json_schema.try_into().map(Validator::new);
    assert_eq!(
        old_validator.is_ok(),
        new_validator.is_ok(),
        "validator construction does not match!"
    );
    if let (Ok(old_validator), Ok(new_validator)) = (old_validator, new_validator) {
        assert_eq!(
            old_validator
                .validate(&ps, ValidationMode::Strict)
                .validation_passed(),
            new_validator
                .validate(&ps, ValidationMode::Strict)
                .validation_passed(),
            "validation result does not match!"
        );
    }
    Ok(())
}

// The main fuzz target
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    // generate a policy
    let mut policyset = ast::PolicySet::new();
    let policy: ast::StaticPolicy = input.policy.into();
    policyset.add_static(policy).unwrap();
    log::info!("Policies: {policyset}");
    let res = round_trip(&input.schema, &policyset);

    assert!(res.is_ok(), "{:?}", res.unwrap_err());
});
