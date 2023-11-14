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

#[derive(Debug, Serialize)]
pub struct RequestForDefEngine<'a> {
    pub request: &'a ast::Request,
    pub policies: &'a ast::PolicySet,
    pub entities: &'a Entities,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DefinitionalAuthResponse {
    pub serialization_nanos: i64,
    pub deserialization_nanos: i64,
    pub auth_nanos: i64,
    pub response: InterfaceResponse,
}

#[derive(Debug, Serialize)]
pub struct EvalRequestForDefEngine<'a> {
    pub request: &'a ast::Request,
    pub entities: &'a Entities,
    pub expr: &'a ast::Expr,
    pub expected: Option<&'a ast::Expr>,
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy)]
#[repr(transparent)]
pub struct DefinitionalEvalResponse {
    pub matches: bool,
}

#[derive(Debug, Serialize)]
pub struct RequestForDefValidator<'a> {
    pub schema: &'a ValidatorSchema,
    pub policies: &'a ast::PolicySet,
    pub mode: ValidationMode,
}

#[derive(Debug, Deserialize)]
pub struct DefinitionalValResponse {
    pub serialization_nanos: i64,
    pub deserialization_nanos: i64,
    pub validation_nanos: i64,
    pub response: ValidationInterfaceResponse,
}
