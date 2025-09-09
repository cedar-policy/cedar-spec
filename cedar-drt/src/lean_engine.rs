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

use cedar_policy::{
    ffi, Entities, EvalResult, Expression, PolicySet, Request, Schema, ValidationMode,
};

use cedar_testing::cedar_test_impl::{
    CedarTestImplementation, ErrorComparisonMode, Micros, TestResponse, TestResult,
    TestValidationResult, ValidationComparisonMode,
};

use cedar_lean_ffi::{CedarLeanFfi, TimedResult, ValidationResponse};
use miette::miette;
use std::collections::HashMap;

pub struct CedarLeanEngine {
    lean_ffi: CedarLeanFfi,
}

impl CedarLeanEngine {
    pub fn new() -> Self {
        Self {
            lean_ffi: CedarLeanFfi::new(),
        }
    }

    fn validation_to_test_result(
        lean_validation_response: TimedResult<ValidationResponse>,
    ) -> TestResult<TestValidationResult> {
        let errors = match lean_validation_response.result() {
            ValidationResponse::Ok(_) => Vec::new(),
            ValidationResponse::Error(err) => vec![err.clone()],
        };
        TestResult::Success(TestValidationResult {
            errors,
            timing_info: HashMap::from([(
                "validate".into(),
                Micros(lean_validation_response.duration() / 1000),
            )]),
        })
    }

    fn filter_warnings(
        validation_result: TestResult<TestValidationResult>,
    ) -> TestResult<TestValidationResult> {
        validation_result.map(|res| {
            let errors = res
                .errors
                .into_iter()
                .filter(|x| x != "impossiblePolicy")
                .collect();
            TestValidationResult { errors, ..res }
        })
    }

    pub fn get_ffi<'a>(&'a self) -> &'a CedarLeanFfi {
        &self.lean_ffi
    }
}

impl CedarTestImplementation for CedarLeanEngine {
    fn is_authorized(
        &self,
        request: &Request,
        policies: &PolicySet,
        entities: &Entities,
    ) -> TestResult<TestResponse> {
        match self
            .lean_ffi
            .is_authorized_timed(policies, entities, request)
        {
            Ok(timed_resp) => {
                let errors = timed_resp
                    .result()
                    .erroring_policies()
                    .iter()
                    .map(|policy_id| {
                        ffi::AuthorizationError::new_from_report(
                            policy_id.clone(),
                            miette!("{policy_id}"),
                        )
                    })
                    .collect();
                TestResult::Success(TestResponse {
                    response: ffi::Response::new(
                        timed_resp.result().decision(),
                        timed_resp.result().determining_policies().clone(),
                        errors,
                    ),
                    timing_info: HashMap::from([(
                        "authorize".into(),
                        Micros(timed_resp.duration() / 1000),
                    )]),
                })
            }
            Err(err) => TestResult::Failure(err.to_string()),
        }
    }

    /// Custom evaluator entry point. The bool return value indicates the whether
    /// evaluating the provided expression produces the expected value.
    /// `expected` is optional to allow for the case where no return value is
    /// expected due to errors.
    fn interpret(
        &self,
        request: &Request,
        entities: &Entities,
        expr: &Expression,
        expected: Option<EvalResult>,
    ) -> TestResult<bool> {
        let expected = expected.map(Expression::from);
        match self
            .lean_ffi
            .check_evaluate(expr, entities, request, expected.as_ref())
        {
            Ok(b) => TestResult::Success(b),
            Err(e) => TestResult::Failure(e.to_string()),
        }
    }

    /// Custom validator entry point.
    fn validate(
        &self,
        schema: &Schema,
        policies: &PolicySet,
        mode: ValidationMode,
    ) -> TestResult<TestValidationResult> {
        assert_eq!(
            mode,
            ValidationMode::Strict,
            "Lean definitional validator only supports `Strict` mode"
        );
        match self.lean_ffi.validate_timed(policies, schema, &mode) {
            Ok(timed_result) => {
                Self::filter_warnings(Self::validation_to_test_result(timed_result))
            }
            Err(e) => TestResult::Failure(e.to_string()),
        }
    }

    /// Custom validator entry point with level.
    fn validate_with_level(
        &self,
        schema: &Schema,
        policies: &PolicySet,
        mode: ValidationMode,
        level: i32,
    ) -> TestResult<TestValidationResult> {
        assert_eq!(
            mode,
            ValidationMode::Strict,
            "Lean definitional validator only supports `Strict` mode"
        );
        match self.lean_ffi.level_validate_timed(policies, schema, level) {
            Ok(timed_result) => {
                Self::filter_warnings(Self::validation_to_test_result(timed_result))
            }
            Err(e) => TestResult::Failure(e.to_string()),
        }
    }

    fn validate_request(
        &self,
        schema: &Schema,
        request: &Request,
    ) -> TestResult<TestValidationResult> {
        match self.lean_ffi.validate_request_timed(schema, request) {
            Ok(timed_result) => {
                Self::filter_warnings(Self::validation_to_test_result(timed_result))
            }
            Err(e) => TestResult::Failure(e.to_string()),
        }
    }

    fn validate_entities(
        &self,
        schema: &Schema,
        entities: &Entities,
    ) -> TestResult<TestValidationResult> {
        match self.lean_ffi.validate_entities_timed(schema, entities) {
            Ok(timed_result) => {
                Self::filter_warnings(Self::validation_to_test_result(timed_result))
            }
            Err(e) => TestResult::Failure(e.to_string()),
        }
    }

    /// `ErrorComparisonMode` that should be used for this `CedarTestImplementation`
    fn error_comparison_mode(&self) -> ErrorComparisonMode {
        ErrorComparisonMode::PolicyIds
    }

    /// `ValidationComparisonMode` that should be used for this `CedarTestImplementation`
    fn validation_comparison_mode(&self) -> ValidationComparisonMode {
        ValidationComparisonMode::AgreeOnValid
    }
}
