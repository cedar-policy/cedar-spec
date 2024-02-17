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

//! Run the standard and definitional implementations of Cedar on the integration
//! tests are record performance results.

mod integration_tests;

use cedar_drt::ast::{PolicySet, Request};
use cedar_drt::cedar_test_impl::*;
use cedar_drt::{ValidatorSchema, ValidationMode};
use cedar_drt::{Entities, JavaDefinitionalEngine, LeanDefinitionalEngine};
use cedar_policy::integration_testing::*;
use integration_tests::get_tests;
use statrs::statistics::{Data, OrderStatistics};
use std::{collections::HashMap, path::Path};

const NUM_TRIALS: u32 = 10;

/// Parse a file in the integration test format, ignoring the expected
/// authorization/validation results.
fn parse_test(jsonfile: impl AsRef<Path>) -> (PolicySet, Entities, ValidatorSchema, Vec<Request>) {
    let jsonfile = resolve_integration_test_path(jsonfile);
    let test_name: String = jsonfile.display().to_string();
    let jsonstr = std::fs::read_to_string(jsonfile.as_path())
        .unwrap_or_else(|e| panic!("error reading from file {test_name}: {e}"));
    let test: JsonTest =
        serde_json::from_str(&jsonstr).unwrap_or_else(|e| panic!("error parsing {test_name}: {e}"));
    let policies = parse_policies_from_test_internal(&test);
    let schema = parse_schema_from_test(&test);
    let schema_internal = parse_schema_from_test_internal(&test);
    let entities = parse_entities_from_test_internal(&test, &schema);
    let requests = test
        .requests
        .into_iter()
        .map(|json_request| parse_request_from_test_internal(&json_request, &schema, &test_name))
        .collect();
    (policies, entities, schema_internal, requests)
}

fn median(data: Vec<f64>) -> f64 {
    let mut data = Data::new(data);
    data.median()
}

fn p90(data: Vec<f64>) -> f64 {
    let mut data = Data::new(data);
    data.percentile(90)
}

fn p99(data: Vec<f64>) -> f64 {
    let mut data = Data::new(data);
    data.percentile(99)
}

/// Run every input in `folder()` through the provided Cedar test implementation,
/// recording the time(s) required for authorization over NUM_TRIALS trials. The
/// output reports the median trial value for each input.
///
/// There are two statistics measured: "total" for end-to-end authorization time
/// and (optionally) "authorize" for the reported _core_ authorization time, which
/// ignores time required to interface with the test implementation.
fn get_authorization_timing_results(
    custom_impl: &dyn CedarTestImplementation,
) -> HashMap<&str, Vec<f64>> {
    let tests = get_tests();
    let mut results = HashMap::new();
    results.insert("total", Vec::new());
    results.insert("authorize", Vec::new());
    for test in tests {
        let test_name = String::from(test.file_name().unwrap().to_str().unwrap());
        println!("Running test: {:?}", test_name);
        let (policies, entities, _schema, requests) = parse_test(test);
        for request in requests {
            let mut total_results = Vec::new();
            let mut auth_results = Vec::new();
            for _i in 0..NUM_TRIALS {
                let (response, duration) =
                    time_function(|| custom_impl.is_authorized(&request, &policies, &entities));
                let response = response.expect("Unexpected test failure");
                total_results.push(duration.as_micros() as f64);
                if response.timing_info.contains_key("authorize") {
                    auth_results.push(response.timing_info["authorize"] as f64);
                }
            }
            results
                .get_mut("total")
                .unwrap()
                .push(median(total_results));
            results
                .get_mut("authorize")
                .unwrap()
                .push(median(auth_results));
        }
    }
    results
}

/// Run every input in `folder()` through the provided Cedar test implementation,
/// recording the time(s) required for validation over NUM_TRIALS trials. The
/// output reports the median trial value for each input.
///
/// There are two statistics measured: "total" for end-to-end validation time
/// and (optionally) "validate" for the reported _core_ validation time, which
/// ignores time required to interface with the test implementation.
fn get_validation_timing_results(
    custom_impl: &dyn CedarTestImplementation,
) -> HashMap<&str, Vec<f64>> {
    let tests = get_tests();
    let mut results = HashMap::new();
    results.insert("total", Vec::new());
    results.insert("validate", Vec::new());
    for test in tests {
        let test_name = String::from(test.file_name().unwrap().to_str().unwrap());
        println!("Running test: {:?}", test_name);
        let (policies, _entities, schema, _requests) = parse_test(test);
        let mut total_results = Vec::new();
        let mut val_results = Vec::new();
        for _i in 0..NUM_TRIALS {
            let (response, duration) =
                time_function(|| custom_impl.validate(&schema, &policies, ValidationMode::Strict));
            let response = response.expect("Unexpected test failure");
            total_results.push(duration.as_micros() as f64);
            if response.timing_info.contains_key("validate") {
                val_results.push(response.timing_info["validate"] as f64);
            }
        }
        results
            .get_mut("total")
            .unwrap()
            .push(median(total_results));
        results
            .get_mut("validate")
            .unwrap()
            .push(median(val_results));
    }
    results
}

/// Print out a summary of the results
fn print_summary(auth_times: HashMap<&str, Vec<f64>>, val_times: HashMap<&str, Vec<f64>>) {
    for (key, value) in auth_times.into_iter() {
        println!("Authorization - {key}");
        println!("\tMedian: {:.1} micros", median(value.clone()));
        println!("\tp90: {:.1} micros", p90(value.clone()));
        println!("\tp99: {:.1} micros", p99(value));
    }
    for (key, value) in val_times.into_iter() {
        println!("Validation - {key}");
        println!("\tMedian: {:.1} micros", median(value.clone()));
        println!("\tp90: {:.1} micros", p90(value.clone()));
        println!("\tp99: {:.1} micros", p99(value));
    }
}

#[test]
fn run_all_tests() {
    let rust_impl = RustEngine::new();
    let lean_def_impl = LeanDefinitionalEngine::new();
    let java_def_impl =
        JavaDefinitionalEngine::new().expect("failed to create Dafny definitional engine");

    let auth_times = get_authorization_timing_results(&rust_impl);
    let val_times = get_validation_timing_results(&rust_impl);
    print_summary(auth_times, val_times);

    let auth_times = get_authorization_timing_results(&rust_impl);
    let val_times = get_validation_timing_results(&rust_impl);
    print_summary(auth_times, val_times);

    let auth_times = get_authorization_timing_results(&rust_impl);
    let val_times = get_validation_timing_results(&rust_impl);
    print_summary(auth_times, val_times);
}
