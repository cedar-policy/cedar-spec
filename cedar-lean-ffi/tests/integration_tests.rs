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

//! Integration test that runs the handwritten test cases from
//! `cedar-integration-tests` on the definitional implementation.

#![cfg(feature = "integration-testing")]

use cedar_lean_ffi::CedarLeanFfi;
use cedar_testing::cedar_test_impl::CedarTestImplementation;
use cedar_testing::integration_testing::{
    perform_integration_test_from_json_custom, resolve_integration_test_path,
};
use cedar_testing::test_files::{get_corpus_tests, get_integration_tests};

use rstest::rstest;
use std::path::PathBuf;

fn run_tests(custom_impl: &impl CedarTestImplementation, tests: impl Iterator<Item = PathBuf>) {
    for test_json in tests {
        perform_integration_test_from_json_custom(&test_json, custom_impl);
    }
}

fn run_integration_tests(custom_impl: &impl CedarTestImplementation) {
    run_tests(custom_impl, get_integration_tests());
}

fn run_corpus_tests(custom_impl: &impl CedarTestImplementation, prefix: &str) {
    run_tests(custom_impl, get_corpus_tests(prefix));
}

#[test]
fn integration_tests() {
    let lean_def_impl = CedarLeanFfi::new();
    run_integration_tests(&lean_def_impl);
}

#[rstest]
fn corpus_tests(
    #[values(
        "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "a", "b", "c", "d", "e", "f"
    )]
    prefix: &str,
) {
    let lean_def_impl = CedarLeanFfi::new();
    run_corpus_tests(&lean_def_impl, prefix);
}
