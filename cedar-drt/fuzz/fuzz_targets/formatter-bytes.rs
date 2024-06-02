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

use cedar_drt_inner::{check_for_internal_errors, fuzz_target};
use cedar_policy_core::parser::parse_policyset;
use cedar_policy_formatter::{policies_str_to_pretty, Config};

fuzz_target!(|input: String| {
    match parse_policyset(&input) {
        Ok(policy_set) => {
            if !policy_set.is_empty() {
                let config = Config {
                    indent_width: 2,
                    line_width: 80,
                };
                // `policies_str_to_pretty` applies soundness checks, so we will panic
                // if the policy definitions changed in any way.
                policies_str_to_pretty(&input, &config).expect("pretty-printing should not fail");
            }
        }
        Err(errs) => check_for_internal_errors(errs),
    }
});
