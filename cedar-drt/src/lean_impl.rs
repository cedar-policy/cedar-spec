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

//NOTE: We use the env var RUST_LEAN_INTERFACE_INIT to save the fact that
//we've already initialized

use core::panic;
use std::{collections::HashSet, env, ffi::CString};

use crate::cedar_test_impl::*;
use crate::definitional_request_types::*;
use cedar_policy::frontend::is_authorized::InterfaceResponse;
use cedar_policy::integration_testing::{CustomCedarImpl, IntegrationTestValidationResult};
use cedar_policy::Diagnostics;
pub use cedar_policy::Response;
use cedar_policy_core::ast::{Expr, Value};
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidationResult, ValidatorSchema};
pub use entities::Entities;
pub use lean_sys::init::lean_initialize;
pub use lean_sys::lean_object;
pub use lean_sys::string::lean_mk_string;
use lean_sys::{
    lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_io_mk_world,
    lean_string_cstr,
};
use serde::{Deserialize, Serialize};
use std::ffi::CStr;
use std::str::FromStr;

/// Times for JSON (de)serialization, authorization, and validation as reported
/// by the Lean implementation.
pub const LEAN_SERIALIZATION_MSG: &str = "lean_serialization (ns) : ";
pub const LEAN_DESERIALIZATION_MSG: &str = "lean_deserialization (ns) : ";
pub const LEAN_AUTH_MSG: &str = "lean_auth (ns) : ";
pub const LEAN_VALIDATION_MSG: &str = "lean_validation (ns) : ";

#[link(name = "Cedar", kind = "static")]
#[link(name = "Std", kind = "static")]
#[link(name = "DiffTest", kind = "static")]
#[link(name = "leanshared", kind = "dylib")]
#[link(name = "Mathlib", kind = "static")]
#[link(name = "Qq", kind = "static")]
#[link(name = "ProofWidgets", kind = "static")]
#[link(name = "Aesop", kind = "static")]
extern "C" {
    fn isAuthorizedDRT(req: *mut lean_object) -> *mut lean_object;
    fn initialize_DiffTest_Main(builtin: i8, ob: *mut lean_object) -> *mut lean_object;
}

#[derive(Serialize, Deserialize)]
struct ListDef<String> {
    l: Vec<String>,
}

#[derive(Serialize, Deserialize)]
struct SetDef<String> {
    mk: ListDef<String>,
}

#[derive(Serialize, Deserialize)]
struct ResponseDef {
    policies: SetDef<String>,
    decision: String,
}

#[derive(Debug)]
pub enum LeanDefEngineError {}

pub struct LeanDefinitionalEngine {
    initialized: bool,
}

fn lean_obj_to_string(o: *mut lean_object) -> String {
    let lean_obj_p = unsafe { lean_string_cstr(o) };
    let lean_obj_cstr = unsafe { CStr::from_ptr(lean_obj_p as *const i8) };
    lean_obj_cstr.to_string_lossy().into_owned() //TODO: lossy
}

impl LeanDefinitionalEngine {
    pub fn new() -> Result<Self, LeanDefEngineError> {
        if env::var("RUST_LEAN_INTERFACE_INIT").is_err() {
            unsafe { lean_initialize_runtime_module() };
            unsafe { lean_initialize() };
            unsafe { initialize_DiffTest_Main(1, lean_io_mk_world()) };
            unsafe { lean_io_mark_end_initialization() };
            env::set_var("RUST_LEAN_INTERFACE_INIT", "1");
        }
        Ok(Self { initialized: true })
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
        let cstring = CString::new(request).expect("CString::new failed");
        let s = unsafe { lean_mk_string(cstring.as_ptr() as *const u8) };
        return s;
    }

    fn deserialize_response(response: *mut lean_object) -> InterfaceResponse {
        let response_string = lean_obj_to_string(response);
        let resp: ResponseDef =
            serde_json::from_str(&response_string).expect("could not convert string to json");
        let dec: authorizer::Decision = if resp.decision == "allow" {
            authorizer::Decision::Allow
        } else if resp.decision == "deny" {
            authorizer::Decision::Deny
        } else {
            panic!("unknown decision")
        };

        let reason = resp
            .policies
            .mk
            .l
            .into_iter()
            .map(|x| cedar_policy::PolicyId::from_str(&x).expect("could not coerce policyId"))
            .collect();
        InterfaceResponse::new(dec, reason, HashSet::new())
    }

    /// Ask the definitional engine whether `isAuthorized` for the given `request`,
    /// `policies`, and `entities`
    pub fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResponse {
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
        println!("Running is_authorized");
        self.is_authorized(request, policies, entities)
    }

    fn interpret(
        &self,
        _request: &ast::Request,
        _entities: &Entities,
        _expr: &Expr,
        _expected: Option<Value>,
    ) -> bool {
        unimplemented!("Unimplemented: interpret");
    }

    fn validate(
        &self,
        _schema: &cedar_policy_validator::ValidatorSchema,
        _policies: &ast::PolicySet,
        _mode: ValidationMode,
    ) -> ValidationInterfaceResponse {
        unimplemented!("Unimplemented: validate");
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
        unimplemented!("Unimplemented: validate");
    }
}
