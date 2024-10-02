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
use cedar_policy_core::extensions::Extensions;
use cedar_policy_validator::{json_schema, RawName};
use similar_asserts::SimpleDiff;

// JSON String -> json_schema::Fragment -> Natural String -> json_schema::Fragment
// Assert that schema fragments are equivalent. By starting with a JSON String
// we test for the existence of schema that are valid in JSON but with an
// invalid cedar schema conversion.
fuzz_target!(|src: String| {
    if let Ok(parsed) = json_schema::Fragment::<RawName>::from_json_str(&src) {
        if TryInto::<ValidatorSchema>::try_into(parsed.clone()).is_err() {
            return;
        }
        let cedar_src = parsed
            .to_cedarschema()
            .expect("Failed to convert the JSON schema into a Cedar schema");
        let (cedar_parsed, _) = json_schema::Fragment::<RawName>::from_cedarschema_str(
            &cedar_src,
            Extensions::all_available(),
        )
        .expect("Failed to parse converted Cedar schema");
        if let Err(msg) = equivalence_check(&parsed, &cedar_parsed) {
            println!("Original JSON schema: {src}");
            println!("Converted to Cedar format:\n{cedar_src}");
            println!(
                "{}",
                SimpleDiff::from_str(
                    &format!("{:#?}", parsed),
                    &format!("{:#?}", cedar_parsed),
                    "Parsed JSON",
                    "Cedar Round tripped"
                )
            );
            panic!("{msg}");
        }
    }
});
