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

//! Implementation of the [`CedarTestImplementation`] trait for the Cedar Lean
//! implementation.

use core::panic;
use std::{collections::HashSet, ffi::CString};

use crate::cedar_test_impl::*;
use crate::dafny_java_impl::RequestForDefEngine;
use cedar_policy::frontend::is_authorized::InterfaceResponse;
use cedar_policy::integration_testing::{CustomCedarImpl, IntegrationTestValidationResult};
pub use cedar_policy::Response;
use cedar_policy_core::ast::{Expr, Value};
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidationResult, ValidatorSchema};
pub use entities::Entities;
pub use lean_sys::init::lean_initialize;
pub use lean_sys::lean_object;
pub use lean_sys::string::lean_mk_string;
use lean_sys::{lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_io_mk_world};

/// Times for JSON (de)serialization, authorization, and validation as reported
/// by the Lean implementation.
pub const LEAN_SERIALIZATION_MSG: &str = "lean_serialization (ns) : ";
pub const LEAN_DESERIALIZATION_MSG: &str = "lean_deserialization (ns) : ";
pub const LEAN_AUTH_MSG: &str = "lean_auth (ns) : ";
pub const LEAN_VALIDATION_MSG: &str = "lean_validation (ns) : ";

#[link(name = "Cedar")]
#[link(name = "Lean")]
#[link(name = "Std")]
extern "C" {
    fn isAuthorizedDRT(req: *mut lean_object) -> *mut lean_object;
    fn initialize_Cedar(builtin: i8, ob: *mut lean_object) -> *mut lean_object;
}

pub struct LeanDefinitionalEngine {}

impl LeanDefinitionalEngine {
    pub fn new() -> Self {
        Self {}
    }

    fn serialize_request(
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> *mut lean_object {
        let request: String = serde_json::to_string(&RequestForDefEngine {
            request,
            policies,
            entities,
        })
        .expect("Failed to serialize request, policies, or entities");
        eprintln!("{request}");
        println!("{:?}", request.clone().as_ptr());
        let cstring = CString::new(request).expect("CString::new failed");
        let s = unsafe { lean_mk_string(cstring.as_ptr() as *const u8) };
        return s;
    }

    fn deserialize_response(response: *mut lean_object) -> InterfaceResponse {
        println!("{:?}", response);
        InterfaceResponse::new(authorizer::Decision::Deny, HashSet::new(), HashSet::new())
    }

    /// Ask the definitional engine whether `isAuthorized` for the given `request`,
    /// `policies`, and `entities`
    pub fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResponse {
        unsafe { lean_initialize_runtime_module() };
        unsafe { lean_initialize() };
        unsafe { initialize_Cedar(1, lean_io_mk_world()) };
        unsafe { lean_io_mark_end_initialization() };

        let req = Self::serialize_request(request, policies, entities);
        let response = unsafe { isAuthorizedDRT(req) };
        Self::deserialize_response(response)
    }
}

impl CedarTestImplementation for LeanDefinitionalEngine {
    fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResponse {
        self.is_authorized(request, policies, entities)
    }

    fn interpret(
        &self,
        _request: &ast::Request,
        _entities: &Entities,
        _expr: &Expr,
        _expected: Option<Value>,
    ) -> bool {
        panic!("Unimplemented: interpret");
    }

    fn validate(
        &self,
        _schema: &cedar_policy_validator::ValidatorSchema,
        _policies: &ast::PolicySet,
        _mode: ValidationMode,
    ) -> ValidationInterfaceResponse {
        panic!("Unimplemented: validate");
    }
}

/// Implementation of the trait used for integration testing.
impl CustomCedarImpl for LeanDefinitionalEngine {
    fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResponse {
        self.is_authorized(request, policies, entities)
    }

    fn validate(
        &self,
        _schema: cedar_policy_validator::ValidatorSchema,
        _policies: &ast::PolicySet,
    ) -> IntegrationTestValidationResult {
        panic!("Unimplemented: validate (test)");
    }
}
