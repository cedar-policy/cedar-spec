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
use cedar_drt::entities::conformance::err;
use cedar_drt_inner::schemas::equivalence_check;
use cedar_drt_inner::*;
use cedar_policy_core::extensions::Extensions;
use cedar_policy_generators::settings::ABACSettings;
use cedar_policy_generators::{schema_grammar::*, size_hint_utils};
use cedar_policy_validator::SchemaFragment;
use cedar_policy_validator::{RawName, SchemaFragment};
use libfuzzer_sys::arbitrary::{self, size_hint, Arbitrary, Unstructured};
use serde::Serialize;
use similar_asserts::SimpleDiff;
use std::io::Write;
use std::path::Path;
use std::str::FromStr;

/// Input expected by this fuzz target: a JSON string of schema
#[derive(Debug, Clone, Serialize, Arbitrary)]
pub struct FuzzTargetInput {
    pub schema: SchemaFragment,
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 3,
    max_width: 3,
    enable_additional_attributes: false,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    enable_unspecified_apply_spec: true,
};

// impl<'a> Arbitrary<'a> for FuzzTargetInput {
//     fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
//         let schema = arbitrary_schema_json_str(&SETTINGS, 0, u)?;
//         Ok(Self { schema })
//     }

//     fn size_hint(depth: usize) -> (usize, Option<usize>) {
//         size_hint_utils::size_hint_for_range(0, SETTINGS.max_depth * SETTINGS.max_width * depth)
//     }
// }

// JSON String -> SchemaFragment -> Natural String -> SchemaFragment
// Assert that schema fragments are equivalent. By starting with a JSON String
// we test for the existence of schema that are valid in JSON but with an
// invalid natural schema conversion.
fuzz_target!(|input: FuzzTargetInput| {
    let json = serde_json::to_value(input.schema.clone()).unwrap();
    println!("orig schema json: {:?}", json.to_string());
    let parsed = SchemaFragment::from_json_value(json);
    if let Ok(parsed) = parsed {
        if TryInto::<ValidatorSchema>::try_into(parsed.clone()).is_err() {
            return;
        }
        let natural_src = parsed
            .as_natural_schema()
            .expect("Failed to convert the JSON schema into a human readable schema");
        println!("natural: {}", natural_src);
        let natural_parsed = SchemaFragment::from_str_natural(&natural_src);
        if let Ok((natural_parsed, _)) = natural_parsed {
            if let Err(msg) = equivalence_check(parsed.clone(), natural_parsed.clone()) {
                println!("Schema: {}", parsed.clone());
                println!(
                    "{}",
                    SimpleDiff::from_str(
                        &format!("{:#?}", parsed),
                        &format!("{:#?}", natural_parsed),
                        "Parsed JSON",
                        "Human Round tripped"
                    )
                );
                panic!("{}", msg);
            }
        }
    }
});
