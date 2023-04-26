//! Integration test that runs the handwritten test cases from
//! `CedarIntegrationTests` on the definitional implementation. See the
//! "Integration test" section of README.md for more information.

use amzn_cedar::integration_testing::{
    perform_integration_test_from_json_custom, resolve_integration_test_path, CustomCedarImpl,
    IntegrationTestValidationResult,
};

use amzn_cedar_drt::*;
use std::path::Path;

// Loosely based on `DifferentialTester`
struct DefinitionalImplementation<'e> {
    /// Definitional engine instance
    def_engine: DefinitionalEngine<'e>,
    /// Definitional validator instance
    def_validator: DefinitionalValidator<'e>,
}

impl<'e> DefinitionalImplementation<'e> {
    pub fn new() -> Self {
        Self {
            def_engine: DefinitionalEngine::new().expect("failed to create definitional engine"),
            def_validator: DefinitionalValidator::new()
                .expect("failed to create definitional validator"),
        }
    }
}

impl<'e> CustomCedarImpl for DefinitionalImplementation<'e> {
    fn is_authorized(
        &self,
        r: &ast::Request,
        p: &ast::PolicySet,
        e: &entities::Entities,
    ) -> authorizer::Answer {
        self.def_engine.is_authorized(r, p, e)
    }

    fn validate(
        &self,
        schema: amzn_cedar_validator::ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> amzn_cedar::integration_testing::IntegrationTestValidationResult {
        let definitional_ans = self.def_validator.validate(schema.clone(), policies);
        assert!(
            definitional_ans.parsing_succeeded(),
            "Dafny json parsing failed for:\nPolicies:\n{}\nSchema:\n{:?}Errors:\n{:?}",
            &policies,
            schema,
            definitional_ans.parse_errors
        );
        IntegrationTestValidationResult {
            validation_passed: definitional_ans.validation_passed(),
            validation_errors_debug: format!("{:?}", definitional_ans.validation_errors),
        }
    }
}

// Note: Some of the following code is based on Cedar/tests/corpus_tests.rs, but
// there probably isn't enough commonality left to be worth trying to share the
// code.

/// Path of the folder containing the integration tests
fn folder() -> &'static Path {
    Path::new("tests")
}

// for now we have a single #[test] that runs all the integration tests.
// The disadvantage of this is that only one error message will be displayed,
// even if many of the integration tests fail.
// TODO for the future: figure out if we can procedurally generate one #[test]
// per integration test. In fact, as long as we have a hard-coded list of tests
// below, we could write out the individual `#[test]`s manually, but the
// improved error reporting doesn't seem to justify the boilerplate. Under any
// approach with multiple `#[test]`s, we'd have to either find a way to share
// `def_impl` or accept the performance cost of re-creating it each time.
#[test]
fn integration_tests_on_def_impl() {
    let def_impl = DefinitionalImplementation::new();
    let integration_tests_folder = resolve_integration_test_path(folder());
    // Unfortunately, we cannot just scan for all `*.json` files because many of
    // the integration tests are currently failing and are skipped by the Cedar
    // package. Instead, hard-code the list of tests that the Cedar package
    // currently runs (last updated 2023-03-23).
    /*
    let test_jsons =
        walkdir::WalkDir::new(&integration_tests_folder)
        .into_iter()
        .map(|e| e.expect("failed to access file in tests").into_path())
        // ignore non-JSON files (and directories, which don't have an extension)
        .filter(|p| p.extension()
            .map(|ext| ext.eq_ignore_ascii_case("json"))
            .unwrap_or(false)
        );
    */
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
        "ip/1.json",
        "ip/2.json",
        "ip/3.json",
        "multi/1.json",
        "multi/2.json",
    ]
    .into_iter()
    .map(|p| integration_tests_folder.join(p));
    for test_json in test_jsons {
        // These messages are for progress reporting and so that if the
        // `#[test]` fails, the user can know which test case failed by looking
        // for the last "Running integration test" message before the failure.
        println!("Running integration test: {:?}", test_json);
        perform_integration_test_from_json_custom(&test_json, Some(&def_impl));
        println!("Integration test succeeded: {:?}", test_json);
    }
}
