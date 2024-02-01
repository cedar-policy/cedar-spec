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

//! Definition of a general `CedarTestImplementation` trait that describes an
//! implementation of Cedar to use during testing.

use cedar_policy::frontend::is_authorized::InterfaceResponse;
pub use cedar_policy::Response;
use cedar_policy_core::ast::{Expr, PolicySet, Request, Value};
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidationResult, ValidatorSchema};
pub use entities::Entities;
use serde::Deserialize;

/// Type alias for convenience. Errors are represented as strings to make
/// (de)serialization as simple as possible. For an `InterfaceResult`, an
/// error represents a case where the external Cedar implementation failed
/// to execute the request (e.g., due to a parse error).
pub type InterfaceResult<T> = std::result::Result<T, String>;

/// "Interface" type for `ValidationResult` which represents validation
/// errors as strings.
#[derive(Debug, Deserialize)]
pub struct InterfaceValidationResult {
    #[serde(rename = "validationErrors")]
    pub validation_errors: Vec<String>,
}

impl InterfaceValidationResult {
    pub fn validation_passed(&self) -> bool {
        self.validation_errors.is_empty()
    }
}

/// A custom implementation of the Cedar authorizer and validator used for testing.
pub trait CedarTestImplementation {
    /// Custom authorizer entry point.
    fn is_authorized(
        &self,
        request: Request,
        policies: &PolicySet,
        entities: &Entities,
    ) -> InterfaceResult<InterfaceResponse>;

    /// Custom evaluator entry point. The bool return value indicates the whether
    /// evaluating the provided expression produces the expected value.
    /// `expected` is optional to allow for the case where no return value is
    /// expected due to errors.
    fn interpret(
        &self,
        request: Request,
        entities: &Entities,
        expr: &Expr,
        expected: Option<Value>,
    ) -> InterfaceResult<bool>;

    /// Custom validator entry point.
    fn validate(
        &self,
        schema: &ValidatorSchema,
        policies: &PolicySet,
        mode: ValidationMode,
    ) -> InterfaceResult<InterfaceValidationResult>;

    /// `ErrorComparisonMode` that should be used for this `CedarTestImplementation`
    fn error_comparison_mode(&self) -> ErrorComparisonMode;
}

/// Specifies how errors coming from a `CedarTestImplementation` should be
/// compared against errors coming from the Rust implementation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ErrorComparisonMode {
    /// Don't compare errors at all; the `CedarTestImplementation` is not
    /// expected to produce errors matching the Rust implementation's errors in
    /// any way.
    /// In fact, the `CedarTestImplementation` will be expected to never report
    /// errors.
    Ignore,
    /// The `CedarTestImplementation` is expected to produce "error messages" that
    /// are actually just the id of the erroring policy. This will be compared to
    /// ensure that the `CedarTestImplementation` agrees with the Rust
    /// implementation on which policies produce errors.
    PolicyIds,
    /// The `CedarTestImplementation` is expected to produce error messages that
    /// exactly match the Rust implementation's error messages' `Display` text.
    Full,
}
