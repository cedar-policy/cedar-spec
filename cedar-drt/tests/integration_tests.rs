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

//! Integration test that runs the handwritten test cases from
//! `cedar-integration-tests` on the definitional implementation.

use cedar_policy::integration_testing::{
    perform_integration_test_from_json_custom, resolve_integration_test_path, CustomCedarImpl,
};

use cedar_drt::*;
use std::path::Path;

/// Path of the folder containing the integration tests
fn folder() -> &'static Path {
    Path::new("tests")
}

fn run_integration_tests(custom_impl: &dyn CustomCedarImpl) {
    let integration_tests_folder = resolve_integration_test_path(folder());
    // Hard-code the list of tests that the cedar-policy package
    // currently runs (last updated 2023-09-25).
    let test_jsons = vec![
        "decimal/1.json",
        "decimal/2.json",
        "example_use_cases_doc/1a.json",
        "example_use_cases_doc/2a.json",
        "example_use_cases_doc/2b.json",
        "example_use_cases_doc/2c.json",
        "example_use_cases_doc/3a.json",
        "example_use_cases_doc/3b.json",
        "example_use_cases_doc/3c.json",
        "example_use_cases_doc/4a.json",
        "example_use_cases_doc/4d.json",
        "example_use_cases_doc/4e.json",
        "example_use_cases_doc/4f.json",
        "example_use_cases_doc/5b.json",
        "ip/1.json",
        "ip/2.json",
        "ip/3.json",
        "multi/1.json",
        "multi/2.json",
        "multi/3.json",
        "multi/4.json",
    ]
    .into_iter()
    .map(|p| integration_tests_folder.join(p));
    for test_json in test_jsons {
        // These messages are for progress reporting and so that if the
        // `#[test]` fails, the user can know which test case failed by looking
        // for the last "Running integration test" message before the failure.
        println!("Running integration test: {:?}", test_json);
        perform_integration_test_from_json_custom(&test_json, Some(custom_impl));
        println!("Integration test succeeded: {:?}", test_json);
    }
}

#[test]
fn integration_tests_on_java_def_impl() {
    let java_def_impl =
        JavaDefinitionalEngine::new().expect("failed to create definitional engine");
    run_integration_tests(&java_def_impl)
}

#[test]
fn integration_tests_on_lean_def_impl() {
    let lean_def_impl = LeanDefinitionalEngine::new();
    run_integration_tests(&lean_def_impl)
}
