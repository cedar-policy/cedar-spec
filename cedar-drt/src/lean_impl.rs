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

// NOTE: We use the env var RUST_LEAN_INTERFACE_INIT to save the fact that
// we've already initialized.

use core::panic;
use std::{env, ffi::CString};

use crate::cedar_test_impl::*;
use crate::definitional_request_types::*;
use cedar_policy::frontend::is_authorized::InterfaceResponse;
use cedar_policy::integration_testing::{CustomCedarImpl, IntegrationTestValidationResult};
use cedar_policy_core::ast::{Expr, Value};
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidatorSchema};
pub use entities::Entities;
pub use lean_sys::init::lean_initialize;
pub use lean_sys::lean_object;
pub use lean_sys::string::lean_mk_string;
use lean_sys::{
    lean_initialize_runtime_module, lean_io_mark_end_initialization, lean_io_mk_world,
    lean_string_cstr,
};
use log::info;
use serde::Deserialize;
use std::ffi::CStr;
use std::str::FromStr;

#[link(name = "Cedar", kind = "static")]
#[link(name = "Std", kind = "static")]
#[link(name = "DiffTest", kind = "static")]
extern "C" {
    fn isAuthorizedDRT(req: *mut lean_object) -> *mut lean_object;
    fn validateDRT(req: *mut lean_object) -> *mut lean_object;
    fn evaluateDRT(req: *mut lean_object) -> *mut lean_object;
    fn initialize_DiffTest_Main(builtin: i8, ob: *mut lean_object) -> *mut lean_object;
}

pub const LEAN_AUTH_MSG: &str = "Lean authorization time (ns) : ";
pub const LEAN_EVAL_MSG: &str = "Lean evaluation time (ns) : ";
pub const LEAN_VAL_MSG: &str = "Lean validation time (ns) : ";

#[derive(Debug, Deserialize)]
struct ListDef<T> {
    l: Vec<T>,
}

#[derive(Debug, Deserialize)]
struct SetDef<T> {
    mk: ListDef<T>,
}

#[derive(Debug, Deserialize)]
enum ResultDef<T> {
    /// Successful execution
    #[serde(rename = "ok")]
    Ok(T),
    /// Failure due to an error in the testing harness (e.g., a parse error on the Lean side)
    #[serde(rename = "error")]
    Error(String),
}

#[derive(Debug, Deserialize)]
struct TimedDef<T> {
    data: T,
    duration: i64,
}

#[derive(Debug, Deserialize)]
struct AuthorizationResponseInner {
    decision: String,
    #[serde(rename = "determiningPolicies")]
    determining_policies: SetDef<String>,
    #[serde(rename = "erroredPolicies")]
    errored_policies: SetDef<String>,
}

#[derive(Debug, Deserialize)]
enum ValidationResponseInner {
    /// Successful validation
    #[serde(rename = "ok")]
    Ok(()),
    /// Validation error case
    #[serde(rename = "error")]
    Error(String),
}

type AuthorizationResponse = ResultDef<TimedDef<AuthorizationResponseInner>>;
type EvaluationResponse = ResultDef<TimedDef<bool>>;
type ValidationResponse = ResultDef<TimedDef<ValidationResponseInner>>;

pub struct LeanDefinitionalEngine {}

fn lean_obj_to_string(o: *mut lean_object) -> String {
    let lean_obj_p = unsafe { lean_string_cstr(o) };
    let lean_obj_cstr = unsafe { CStr::from_ptr(lean_obj_p as *const i8) };
    lean_obj_cstr
        .to_str()
        .expect("failed to convert Lean object to string")
        .to_owned()
}

impl LeanDefinitionalEngine {
    pub fn new() -> Self {
        if env::var("RUST_LEAN_INTERFACE_INIT").is_err() {
            unsafe { lean_initialize_runtime_module() };
            unsafe { lean_initialize() };
            unsafe { initialize_DiffTest_Main(1, lean_io_mk_world()) };
            unsafe { lean_io_mark_end_initialization() };
            env::set_var("RUST_LEAN_INTERFACE_INIT", "1");
        }
        Self {}
    }

    fn serialize_authorization_request(
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> *mut lean_object {
        let request: String = serde_json::to_string(&AuthorizationRequest {
            request,
            policies,
            entities,
        })
        .expect("failed to serialize request, policies, or entities");
        let cstring = CString::new(request).expect("`CString::new` failed");
        unsafe { lean_mk_string(cstring.as_ptr() as *const u8) }
    }

    fn deserialize_authorization_response(
        response: *mut lean_object,
    ) -> InterfaceResult<InterfaceResponse> {
        let response_string = lean_obj_to_string(response);
        let resp: AuthorizationResponse =
            serde_json::from_str(&response_string).expect("could not deserialize json");
        match resp {
            AuthorizationResponse::Ok(resp) => {
                info!("{}{}", LEAN_AUTH_MSG, resp.duration);

                let resp = resp.data;
                let decision: authorizer::Decision = match resp.decision.as_str() {
                    "allow" => authorizer::Decision::Allow,
                    "deny" => authorizer::Decision::Deny,
                    _ => panic!("Lean code returned unknown decision {}", resp.decision),
                };
                let reason = resp
                    .determining_policies
                    .mk
                    .l
                    .into_iter()
                    .map(|x| {
                        cedar_policy::PolicyId::from_str(&x).expect("could not coerce policy id")
                    })
                    .collect();
                let errors = resp
                    .errored_policies
                    .mk
                    .l
                    .into_iter()
                    .map(|x| {
                        // coerce to PolicyId just to ensure it's valid
                        let pid = cedar_policy::PolicyId::from_str(&x).expect("could not coerce policy id");
                        format!("error in policy {pid}")
                    })
                    .collect();
                Ok(InterfaceResponse::new(decision, reason, errors))
            }
            AuthorizationResponse::Error(err) => Err(err),
        }
    }

    /// Ask the definitional engine whether `isAuthorized` for the given `request`,
    /// `policies`, and `entities`
    pub fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResult<InterfaceResponse> {
        let req = Self::serialize_authorization_request(request, policies, entities);
        let response = unsafe { isAuthorizedDRT(req) };
        Self::deserialize_authorization_response(response)
    }

    fn serialize_evaluation_request(
        request: &ast::Request,
        entities: &Entities,
        expr: &Expr,
        expected: Option<&Expr>,
    ) -> *mut lean_object {
        let request: String = serde_json::to_string(&EvaluationRequest {
            request,
            entities,
            expr,
            expected,
        })
        .expect("failed to serialize request, expression, or entities");
        let cstring = CString::new(request).expect("`CString::new` failed");
        unsafe { lean_mk_string(cstring.as_ptr() as *const u8) }
    }

    fn deserialize_evaluation_response(response: *mut lean_object) -> InterfaceResult<bool> {
        let response_string = lean_obj_to_string(response);
        let resp: EvaluationResponse =
            serde_json::from_str(&response_string).expect("could not deserialize json");
        match resp {
            EvaluationResponse::Ok(resp) => {
                info!("{}{}", LEAN_EVAL_MSG, resp.duration);
                Ok(resp.data)
            }
            EvaluationResponse::Error(err) => Err(err),
        }
    }

    /// Ask the definitional engine whether the input expression evaluates to the
    /// expected result. If `expected` is none, then evaluation should produce an error.
    pub fn evaluate(
        &self,
        request: &ast::Request,
        entities: &Entities,
        expr: &Expr,
        expected: Option<Value>,
    ) -> InterfaceResult<bool> {
        let expected_as_expr = expected.map(|v| v.into());
        let req =
            Self::serialize_evaluation_request(request, entities, expr, expected_as_expr.as_ref());
        let response = unsafe { evaluateDRT(req) };
        Self::deserialize_evaluation_response(response)
    }

    fn serialize_validation_request(
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> *mut lean_object {
        let request: String = serde_json::to_string(&ValidationRequest {
            schema,
            policies,
            mode: cedar_policy_validator::ValidationMode::default(), // == Strict
        })
        .expect("failed to serialize schema or policies");
        let cstring = CString::new(request).expect("`CString::new` failed");
        unsafe { lean_mk_string(cstring.as_ptr() as *const u8) }
    }

    fn deserialize_validation_response(
        response: *mut lean_object,
    ) -> InterfaceResult<InterfaceValidationResult> {
        let response_string = lean_obj_to_string(response);
        let resp: ValidationResponse =
            serde_json::from_str(&response_string).expect("could not deserialize json");
        match resp {
            ValidationResponse::Ok(resp) => {
                info!("{}{}", LEAN_VAL_MSG, resp.duration);
                let validation_errors = match resp.data {
                    ValidationResponseInner::Ok(_) => Vec::new(),
                    ValidationResponseInner::Error(err) => vec![err],
                };
                Ok(InterfaceValidationResult { validation_errors })
            }
            ValidationResponse::Error(err) => Err(err),
        }
    }

    /// Use the definitional validator to validate the given `policies` given a `schema`
    pub fn validate(
        &self,
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> InterfaceResult<InterfaceValidationResult> {
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
    ) -> InterfaceResult<InterfaceResponse> {
        self.is_authorized(&request, policies, entities)
    }

    fn interpret(
        &self,
        request: ast::Request,
        entities: &Entities,
        expr: &Expr,
        expected: Option<Value>,
    ) -> InterfaceResult<bool> {
        self.evaluate(&request, entities, expr, expected)
    }

    fn validate(
        &self,
        schema: &cedar_policy_validator::ValidatorSchema,
        policies: &ast::PolicySet,
        mode: ValidationMode,
    ) -> InterfaceResult<InterfaceValidationResult> {
        assert_eq!(
            mode,
            ValidationMode::Strict,
            "Lean definitional validator only supports `Strict` mode"
        );
        self.validate(schema, policies)
    }
}

/// Implementation of the trait used for integration testing. The integration
/// tests expect the calls to `is_authorized` and `validate` to succeed.
impl CustomCedarImpl for LeanDefinitionalEngine {
    fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResponse {
        self.is_authorized(request, policies, entities)
            .unwrap_or_else(|e| {
                panic!("Unexpected error from the Lean implementation of `is_authorized`: {e}")
            })
    }

    fn validate(
        &self,
        schema: cedar_policy_validator::ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> IntegrationTestValidationResult {
        let result = self.validate(&schema, policies).unwrap_or_else(|e| {
            panic!("Unexpected error from the Lean implementation of `validate`: {e}")
        });
        IntegrationTestValidationResult {
            validation_passed: result.validation_passed(),
            validation_errors_debug: format!("{:?}", result.validation_errors),
        }
    }
}
