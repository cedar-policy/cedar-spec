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

use cedar_drt_inner::fuzz_target;
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy_core::parser::parse_policyset;

// Differentially test the Lean policy parser against the Rust parser, comparing
// only whether they agree on parse+translate success (not the resulting ASTs).
fuzz_target!(|input: String| {
    let ffi = CedarLeanFfi::new();

    let rust_ok = parse_policyset(&input).is_ok();
    let lean_ok = ffi
        .parse_policies(&input)
        .expect("Lean call unexpectedly failed for parse_policies");

    assert_eq!(
        lean_ok, rust_ok,
        "Lean and Rust disagree on parse+translate success for input:\n{input:?}\n\
         (lean_ok = {lean_ok}, rust_ok = {rust_ok})"
    );
});
