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

//! Implementation of the [`CedarTestImplementation`] trait for the Cedar Lean
//! implementation.

// NOTE: We use the env var RUST_LEAN_INTERFACE_INIT to save the fact that
// we've already initialized.

use core::panic;
use std::collections::HashMap;
use std::sync::Once;

use crate::definitional_request_types::*;
use cedar_policy::ffi;
use cedar_policy_core::ast::{Expr, Value};
pub use cedar_policy_core::*;
use cedar_testing::cedar_test_impl::*;
pub use lean_sys::init::lean_initialize;
pub use lean_sys::lean_object;
pub use lean_sys::string::lean_mk_string;
use lean_sys::{
    lean_alloc_sarray, lean_dec, lean_dec_ref, lean_finalize_thread,
    lean_initialize_runtime_module_locked, lean_initialize_thread, lean_io_mark_end_initialization,
    lean_io_mk_world, lean_io_result_is_ok, lean_io_result_show_error, lean_sarray_object,
    lean_set_exit_on_panic, lean_string_cstr,
};
use log::info;
use miette::miette;
use prost::Message;
use serde::Deserialize;
use std::ffi::{c_char, CStr};
use std::str::FromStr;

#[link(name = "Cedar", kind = "static")]
#[link(name = "Protobuf", kind = "static")]
#[link(name = "CedarProto", kind = "static")]
#[link(name = "Batteries", kind = "static")]
#[link(name = "DiffTest", kind = "static")]
extern "C" {
    fn isAuthorizedDRT(req: *mut lean_object) -> *mut lean_object;
    fn validateDRT(req: *mut lean_object) -> *mut lean_object;
    fn levelValidateDRT(req: *mut lean_object) -> *mut lean_object;
    fn evaluateDRT(req: *mut lean_object) -> *mut lean_object;
    fn validateRequestDRT(req: *mut lean_object) -> *mut lean_object;
    fn validateEntitiesDRT(req: *mut lean_object) -> *mut lean_object;
    fn initialize_DiffTest_Main(builtin: u8, ob: *mut lean_object) -> *mut lean_object;
}

pub const LEAN_AUTH_MSG: &str = "Lean authorization time (ns) : ";
pub const LEAN_EVAL_MSG: &str = "Lean evaluation time (ns) : ";
pub const LEAN_VAL_MSG: &str = "Lean validation time (ns) : ";
pub const LEAN_PE_MSG: &str = "Lean partial evaluation time (ns) : ";
pub const LEAN_PA_MSG: &str = "Lean partial authorization time (ns) : ";
static START: Once = Once::new();

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
    duration: u128,
}

#[derive(Debug, Deserialize)]
struct AuthorizationResponseInner {
    decision: String,
    #[serde(rename = "determiningPolicies")]
    determining_policies: SetDef<String>,
    #[serde(rename = "erroringPolicies")]
    erroring_policies: SetDef<String>,
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

#[derive(Default)]
pub struct LeanDefinitionalEngine {}

/// Takes ownership of its argument -- do not access `lean_str_obj` after
/// calling this function
fn lean_obj_p_to_rust_string(lean_str_obj: *mut lean_object) -> String {
    let lean_obj_p = unsafe { lean_string_cstr(lean_str_obj) };
    let lean_obj_cstr = unsafe { CStr::from_ptr(lean_obj_p as *const c_char) };
    let rust_string = lean_obj_cstr
        .to_str()
        .expect("failed to convert Lean object to string")
        .to_owned();
    unsafe {
        lean_dec(lean_str_obj);
    };
    rust_string
}

fn buf_to_lean_obj(buf: &[u8]) -> *mut lean_object {
    unsafe {
        let x: *mut lean_sarray_object = lean_alloc_sarray(1, buf.len(), buf.len()).cast();
        let y = (*x).m_data.as_mut_ptr();
        for (i, byte) in buf.iter().enumerate() {
            y.add(i).write(*byte)
        }
        x.cast()
    }
}

impl LeanDefinitionalEngine {
    /// WARNING: we can only have one Lean thread
    pub fn new() -> Self {
        START.call_once(|| {
            unsafe {
                // following: https://lean-lang.org/lean4/doc/dev/ffi.html
                lean_initialize_runtime_module_locked();
                let builtin: u8 = 1;
                let res = initialize_DiffTest_Main(builtin, lean_io_mk_world());
                if lean_io_result_is_ok(res) {
                    lean_dec_ref(res);
                } else {
                    lean_io_result_show_error(res);
                    lean_dec(res);
                    panic!("Failed to initialize Lean");
                }
                lean_io_mark_end_initialization();
                // If we don't explicitly set this, Lean does not abort after hitting a panic
                lean_set_exit_on_panic(true);
            };
        });
        unsafe { lean_initialize_thread() };
        Self {}
    }

    fn deserialize_authorization_response(response_string: String) -> TestResult<TestResponse> {
        let resp: AuthorizationResponse =
            serde_json::from_str(&response_string).expect("could not deserialize json");
        match resp {
            AuthorizationResponse::Ok(resp) => {
                let auth_time = resp.duration / 1000; // nanoseconds -> microseconds
                info!("{LEAN_AUTH_MSG}{auth_time}");

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
                    .erroring_policies
                    .mk
                    .l
                    .into_iter()
                    .map(|x| {
                        // coerce to PolicyId just to ensure it's valid
                        let pid = cedar_policy::PolicyId::from_str(&x)
                            .expect("could not coerce policy id");
                        ffi::AuthorizationError::new_from_report(pid.clone(), miette!("{pid}"))
                    })
                    .collect();
                TestResult::Success(TestResponse {
                    response: ffi::Response::new(decision, reason, errors),
                    timing_info: HashMap::from([("authorize".into(), Micros(auth_time))]),
                })
            }
            AuthorizationResponse::Error(err) => TestResult::Failure(err),
        }
    }

    /// Ask the definitional engine whether `isAuthorized` for the given `request`,
    /// `policies`, and `entities`
    pub fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> TestResult<TestResponse> {
        let auth_request = AuthorizationRequest {
            request,
            policies,
            entities,
        };
        let auth_request_proto = proto::AuthorizationRequest::from(&auth_request);
        let buf = auth_request_proto.encode_to_vec();
        let req = buf_to_lean_obj(&buf);
        // Lean will decrement the reference count when we pass this object: https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h
        let response = unsafe { isAuthorizedDRT(req) };
        // req can no longer be assumed to exist
        let response_string = lean_obj_p_to_rust_string(response);
        Self::deserialize_authorization_response(response_string)
    }

    fn deserialize_evaluation_response(response_string: String) -> TestResult<bool> {
        let resp: EvaluationResponse =
            serde_json::from_str(&response_string).expect("could not deserialize json");
        match resp {
            EvaluationResponse::Ok(resp) => {
                info!("{}{}", LEAN_EVAL_MSG, resp.duration);
                TestResult::Success(resp.data)
            }
            EvaluationResponse::Error(err) => TestResult::Failure(err),
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
    ) -> TestResult<bool> {
        let expected_as_expr: Option<Expr> = expected.map(|v| v.into());
        let req = EvaluationRequest {
            request,
            entities,
            expr,
            expected: expected_as_expr.as_ref(),
        };
        let req_proto = proto::EvaluationRequest::from(&req);
        let buf = req_proto.encode_to_vec();
        let req = buf_to_lean_obj(&buf);
        // Lean will decrement the reference count when we pass this object: https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h
        let response = unsafe { evaluateDRT(req) };
        // req can no longer be assumed to exist
        let response_string = lean_obj_p_to_rust_string(response);
        Self::deserialize_evaluation_response(response_string)
    }

    fn deserialize_validation_response(
        response_string: String,
    ) -> TestResult<TestValidationResult> {
        let resp: ValidationResponse =
            serde_json::from_str(&response_string).expect("could not deserialize json");
        match resp {
            ValidationResponse::Ok(resp) => {
                info!("{}{}", LEAN_VAL_MSG, resp.duration);
                let validation_errors = match resp.data {
                    ValidationResponseInner::Ok(_) => Vec::new(),
                    ValidationResponseInner::Error(err) => vec![err],
                };
                let response = TestValidationResult {
                    errors: validation_errors,
                    timing_info: HashMap::from([("validate".into(), Micros(resp.duration / 1000))]),
                };
                TestResult::Success(response)
            }
            ValidationResponse::Error(err) => TestResult::Failure(err),
        }
    }

    /// Use the definitional validator to validate the given `policies` given a `schema`
    pub fn validate(
        &self,
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
    ) -> TestResult<TestValidationResult> {
        let val_request = ValidationRequest {
            schema,
            policies,
            mode: cedar_policy_core::validator::ValidationMode::default(),
        };
        let val_request_proto = proto::ValidationRequest::from(&val_request);
        let buf = val_request_proto.encode_to_vec();
        let req = buf_to_lean_obj(&buf);
        // Lean will decrement the reference count when we pass this object: https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h
        let response = unsafe { validateDRT(req) };
        // req can no longer be assumed to exist
        let response_string = lean_obj_p_to_rust_string(response);
        Self::deserialize_validation_response(response_string)
    }

    pub fn validate_with_level(
        &self,
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
        level: i32,
    ) -> TestResult<TestValidationResult> {
        let level_val_request = LevelValidationRequest {
            schema,
            policies,
            level,
        };
        let level_val_request_proto = proto::LevelValidationRequest::from(&level_val_request);
        let buf = level_val_request_proto.encode_to_vec();
        let req = buf_to_lean_obj(&buf);
        // Lean will decrement the reference count when we pass this object: https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h
        let response = unsafe { levelValidateDRT(req) };
        // req can no longer be assumed to exist
        let response_string = lean_obj_p_to_rust_string(response);
        Self::deserialize_validation_response(response_string)
    }

    pub fn validate_request(
        &self,
        schema: &ValidatorSchema,
        request: &ast::Request,
    ) -> TestResult<TestValidationResult> {
        let req = RequestValidationRequest { schema, request };
        let req_proto = proto::RequestValidationRequest::from(&req);
        let buf = req_proto.encode_to_vec();
        let req = buf_to_lean_obj(&buf);
        // Lean will decrement the reference count when we pass this object: https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h
        let response = unsafe { validateRequestDRT(req) };
        // req can no longer be assumed to exist
        let response_string = lean_obj_p_to_rust_string(response);
        Self::deserialize_validation_response(response_string)
    }

    pub fn validate_entities(
        &self,
        schema: &ValidatorSchema,
        entities: &Entities,
    ) -> TestResult<TestValidationResult> {
        let req = EntityValidationRequest { schema, entities };
        let req_proto = proto::EntityValidationRequest::from(&req);
        let buf = req_proto.encode_to_vec();
        let req = buf_to_lean_obj(&buf);
        // Lean will decrement the reference count when we pass this object: https://github.com/leanprover/lean4/blob/master/src/include/lean/lean.h
        let response = unsafe { validateEntitiesDRT(req) };
        // req can no longer be assumed to exist
        let response_string = lean_obj_p_to_rust_string(response);
        Self::deserialize_validation_response(response_string)
    }
}

impl Drop for LeanDefinitionalEngine {
    fn drop(&mut self) {
        unsafe { lean_finalize_thread() }
    }
}

impl LeanDefinitionalEngine {
    // We do not perform differential testing on validation warnings like
    // `impossiblePolicy`, so we drop them here. We could extend differential
    // testing to include warning (see #254).
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
}

impl CedarTestImplementation for LeanDefinitionalEngine {
    fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> TestResult<TestResponse> {
        self.is_authorized(request, policies, entities)
    }

    fn interpret(
        &self,
        request: &ast::Request,
        entities: &Entities,
        expr: &Expr,
        enable_extensions: bool,
        expected: Option<Value>,
    ) -> TestResult<bool> {
        assert!(
            enable_extensions,
            "Lean definitional interpreter expects extensions to be enabled"
        );
        self.evaluate(request, entities, expr, expected)
    }

    fn validate(
        &self,
        schema: &cedar_policy_core::validator::ValidatorSchema,
        policies: &ast::PolicySet,
        mode: ValidationMode,
    ) -> TestResult<TestValidationResult> {
        assert_eq!(
            mode,
            ValidationMode::Strict,
            "Lean definitional validator only supports `Strict` mode"
        );
        Self::filter_warnings(self.validate(schema, policies))
    }

    fn validate_with_level(
        &self,
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
        mode: ValidationMode,
        level: i32,
    ) -> TestResult<TestValidationResult> {
        assert_eq!(
            mode,
            ValidationMode::Strict,
            "Lean definitional validator only supports `Strict` mode"
        );
        Self::filter_warnings(self.validate_with_level(schema, policies, level))
    }

    fn validate_entities(
        &self,
        schema: &ValidatorSchema,
        entities: &Entities,
    ) -> TestResult<TestValidationResult> {
        let result = self.validate_entities(schema, entities);
        result.map(|res| {
            let errors = res.errors.into_iter().collect();
            TestValidationResult { errors, ..res }
        })
    }

    fn validate_request(
        &self,
        schema: &ValidatorSchema,
        request: &ast::Request,
    ) -> TestResult<TestValidationResult> {
        let result = self.validate_request(schema, request);
        result.map(|res| {
            let errors = res.errors.into_iter().collect();
            TestValidationResult { errors, ..res }
        })
    }

    fn error_comparison_mode(&self) -> ErrorComparisonMode {
        ErrorComparisonMode::PolicyIds
    }

    fn validation_comparison_mode(&self) -> ValidationComparisonMode {
        ValidationComparisonMode::AgreeOnValid
    }
}
