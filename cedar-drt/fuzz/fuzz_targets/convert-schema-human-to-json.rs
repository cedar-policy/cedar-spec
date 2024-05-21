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
use cedar_drt_inner::schemas::equivalence_check;
use cedar_drt_inner::*;
use cedar_policy_validator::SchemaFragment;
use similar_asserts::SimpleDiff;

// Natural String -> SchemaFragment -> JSON String -> SchemaFragment
// Assert that schema fragments are equivalent. By starting with a Natural
// String we test for the existence of schema that are valid in the natural
// format but with an invalid json schema conversion.
fuzz_target!(|src: String| {
    if let Ok((parsed, _)) = SchemaFragment::from_str_natural(&src) {
        if TryInto::<ValidatorSchema>::try_into(parsed.clone()).is_err() {
            return;
        }
        let json = serde_json::to_value(parsed.clone()).expect("Failed to convert human readable schema to JSON");
        let json_parsed = SchemaFragment::from_json_value(json).expect("Failed to parse converted JSON schema");
        if let Err(msg) = equivalence_check(parsed.clone(), json_parsed.clone()) {
            println!("Schema: {src}");
            println!(
                "{}",
                SimpleDiff::from_str(
                    &format!("{:#?}", parsed),
                    &format!("{:#?}", json_parsed),
                    "Parsed human readable",
                    "JSON round-tripped"
                )
            );
            panic!("{msg}");
        }
    }
});
