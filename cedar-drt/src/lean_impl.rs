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
use lean_sys::{
    lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_io_mk_world,
    lean_string_cstr,
};
use serde::{Deserialize, Serialize};
use std::ffi::CStr;
use std::str::FromStr;

use crate::definitional_request_types::*;

#[link(name = "Cedar", kind = "static")]
// #[link(name = "Lean")]
#[link(name = "Std", kind = "static")]
#[link(name = "DiffTest", kind = "static")]
#[link(name = "leanshared", kind = "dylib")]
#[link(name = "Mathlib", kind = "static")]
#[link(name = "Qq", kind = "static")]
#[link(name = "ProofWidgets", kind = "static")]
#[link(name = "Aesop", kind = "static")]
extern "C" {
    fn isAuthorizedDRT(req: *mut lean_object) -> *mut lean_object;
    fn validateDRT(req: *mut lean_object) -> *mut lean_object;
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

#[derive(Serialize, Deserialize)]
struct ValResponseDef {
    errors: SetDef<String>,
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
        Ok(Self { initialized: false })
    }

    fn initialize() {
        if env::var("RUST_LEAN_INTERFACE_INIT").is_err() {
            unsafe { lean_initialize_runtime_module() };
            unsafe { lean_initialize() };
            unsafe { initialize_DiffTest_Main(1, lean_io_mk_world()) };
            unsafe { lean_io_mark_end_initialization() };
            env::set_var("RUST_LEAN_INTERFACE_INIT", "1");
        }
    }

    fn serialize_authorization_request(
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
        let cstring = CString::new(request).expect("CString::new failed");
        let s = unsafe { lean_mk_string(cstring.as_ptr() as *const u8) };
        return s;
    }

    fn deserialize_authorization_response(response: *mut lean_object) -> InterfaceResponse {
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
        Self::initialize();
        let req = Self::serialize_authorization_request(request, policies, entities);
        let response = unsafe { isAuthorizedDRT(req) };
        Self::deserialize_authorization_response(response)
    }

    fn serialize_validation_request(
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> *mut lean_object {
        let request: String = serde_json::to_string(&RequestForDefValidator {
            schema,
            policies,
            mode: cedar_policy_validator::ValidationMode::default(), // == Strict
        })
        .expect("Failed to serialize schema or policies");
        let cstring = CString::new(request).expect("CString::new failed");
        let s = unsafe { lean_mk_string(cstring.as_ptr() as *const u8) };
        return s;
    }

    fn deserialize_validation_response(response: *mut lean_object) -> ValidationInterfaceResponse {
        let response_string = lean_obj_to_string(response);
        print!("{response_string}");
        // let resp: ValResponseDef =
        //     serde_json::from_str(&response_string).expect("could not convert string to json");
        // let errors = resp.errors.mk.l.into_iter().collect();
        ValidationInterfaceResponse {
            validation_errors: Vec::new(),
            parse_errors: Vec::new(),
        }
    }

    /// Use the definitional validator to validate the given `policies` given a `schema`
    pub fn validate(
        &self,
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> ValidationInterfaceResponse {
        Self::initialize();
        let req = Self::serialize_validation_request(schema, policies);
        let response = unsafe { validateDRT(req) };
        Self::deserialize_validation_response(response)
    }
}

impl CedarTestImplementation for LeanDefinitionalEngine {
    fn is_authorized(
        &self,
        request: ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResponse {
        self.is_authorized(&request, policies, entities)
    }

    fn interpret(
        &self,
        _request: ast::Request,
        _entities: &Entities,
        _expr: &Expr,
        _expected: Option<Value>,
    ) -> bool {
        unimplemented!("Unimplemented: interpret");
    }

    fn validate(
        &self,
        schema: &cedar_policy_validator::ValidatorSchema,
        policies: &ast::PolicySet,
        _mode: ValidationMode,
    ) -> ValidationInterfaceResponse {
        // Note: only strict mode is supported in Lean
        self.validate(schema, policies)
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
        schema: cedar_policy_validator::ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> IntegrationTestValidationResult {
        let result = self.validate(&schema, policies);
        assert!(
            result.parsing_succeeded(),
            "Lean json parsing failed for:\nPolicies:\n{}\nSchema:\n{:?}Errors:\n{:?}",
            &policies,
            schema,
            result.parse_errors
        );
        IntegrationTestValidationResult {
            validation_passed: result.validation_passed(),
            validation_errors_debug: format!("{:?}", result.validation_errors),
        }
    }
}
