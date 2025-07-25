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
use cedar_drt_inner::{fuzz_target, schemas::equivalence_check};
#[cfg(feature = "prt")]
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

use cedar_policy_core::extensions::Extensions;
use cedar_policy_core::validator::{json_schema, RawName, ValidatorSchema};
use similar_asserts::SimpleDiff;

// Natural String -> json_schema::Fragment -> JSON String -> json_schema::Fragment
// Assert that schema fragments are equivalent. By starting with a Natural
// String we test for the existence of schema that are valid in the Cedar
// format but with an invalid json schema conversion.
fuzz_target!(|src: String| {
    if let Ok((parsed, _)) =
        json_schema::Fragment::<RawName>::from_cedarschema_str(&src, Extensions::all_available())
    {
        if TryInto::<ValidatorSchema>::try_into(parsed.clone()).is_err() {
            return;
        }
        let json =
            serde_json::to_value(parsed.clone()).expect("Failed to convert Cedar schema to JSON");
        let json_parsed = json_schema::Fragment::from_json_value(json)
            .expect("Failed to parse converted JSON schema");
        if let Err(msg) = equivalence_check(&parsed, &json_parsed) {
            println!("Schema: {src}");
            println!(
                "{}",
                SimpleDiff::from_str(
                    &format!("{:#?}", parsed),
                    &format!("{:#?}", json_parsed),
                    "Parsed Cedar",
                    "JSON round-tripped"
                )
            );
            panic!("{msg}");
        }
    }
});
