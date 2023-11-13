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


use crate::cedar_test_impl::*;
use cedar_policy::frontend::is_authorized::InterfaceResponse;
pub use cedar_policy::Response;
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidationResult, ValidatorSchema};
pub use entities::Entities;
use serde::{Deserialize, Serialize};

/// Times to (de)serialize JSON content sent to / received from the Dafny-Java
/// implementation.
pub const RUST_SERIALIZATION_MSG: &str = "rust_serialization (ns) : ";
pub const RUST_DESERIALIZATION_MSG: &str = "rust_deserialization (ns) : ";

/// Times for cedar-policy authorization and validation.
pub const RUST_AUTH_MSG: &str = "rust_auth (ns) : ";
pub const RUST_VALIDATION_MSG: &str = "rust_validation (ns) : ";


#[derive(Debug, Serialize)]
pub struct RequestForDefEngine<'a> {
    pub request: &'a ast::Request,
    pub policies: &'a ast::PolicySet,
    pub entities: &'a Entities,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DefinitionalAuthResponse {
    serialization_nanos: i64,
    deserialization_nanos: i64,
    auth_nanos: i64,
    response: InterfaceResponse,
}

#[derive(Debug, Serialize)]
struct EvalRequestForDefEngine<'a> {
    request: &'a ast::Request,
    entities: &'a Entities,
    expr: &'a ast::Expr,
    expected: Option<&'a ast::Expr>,
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy)]
#[repr(transparent)]
struct DefinitionalEvalResponse {
    matches: bool,
}

#[derive(Debug, Serialize)]
struct RequestForDefValidator<'a> {
    schema: &'a ValidatorSchema,
    policies: &'a ast::PolicySet,
    mode: ValidationMode,
}

#[derive(Debug, Deserialize)]
pub struct DefinitionalValResponse {
    serialization_nanos: i64,
    deserialization_nanos: i64,
    validation_nanos: i64,
    response: ValidationInterfaceResponse,
}
