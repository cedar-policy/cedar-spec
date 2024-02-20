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
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

/// Path of the folder containing the integration tests
fn folder() -> &'static Path {
    Path::new("tests")
}

/// Pull out the relevant tests in `folder()`
pub fn get_tests() -> impl Iterator<Item = PathBuf> {
    let integration_tests_folder = resolve_integration_test_path(folder());
    // find all `*.json` files in the integration tests folder
    WalkDir::new(&integration_tests_folder)
        .into_iter()
        .map(|e| e.expect("failed to access file in tests").into_path())
        // ignore non-JSON files (and directories, which don't have an extension)
        .filter(|p| {
            p.extension()
                .map(|ext| ext.eq_ignore_ascii_case("json"))
                .unwrap_or(false)
        })
}

fn run_integration_tests(custom_impl: &dyn CustomCedarImpl) {
    for test_json in get_tests() {
        // These messages are for progress reporting and so that if the
        // `#[test]` fails, the user can know which test case failed by looking
        // for the last "Running integration test" message before the failure.
        println!("Running integration test: {:?}", test_json);
        perform_integration_test_from_json_custom(&test_json, Some(custom_impl));
        println!("Integration test succeeded: {:?}", test_json);
    }
}

// #[test]
fn integration_tests_on_def_impl() {
    let lean_def_impl = LeanDefinitionalEngine::new();
    run_integration_tests(&lean_def_impl);
}
