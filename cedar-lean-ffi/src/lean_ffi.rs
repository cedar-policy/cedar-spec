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
use crate::err::FfiError;
use crate::messages::*;

use cedar_policy::{
    Decision, Entities, Expression, Policy, PolicyId, PolicySet, Request, RequestEnv, Schema,
    ValidationMode,
};

use lean_sys::lean_object;
use lean_sys::{
    lean_alloc_sarray, lean_dec, lean_dec_ref, lean_finalize_thread,
    lean_initialize_runtime_module_locked, lean_initialize_thread, lean_io_mark_end_initialization,
    lean_io_mk_world, lean_io_result_is_ok, lean_io_result_show_error, lean_sarray_object,
    lean_set_exit_on_panic, lean_string_cstr,
};

use prost::Message;

use serde::Deserialize;

use std::collections::HashSet;
use std::ffi::{c_char, CStr};
use std::sync::Once;

// Import and signal RUST to link the exported Lean FFI code (which are C functions at this point)
#[link(name = "Cedar", kind = "static")]
#[link(name = "Cedar_SymCC", kind = "static")]
#[link(name = "Protobuf", kind = "static")]
#[link(name = "CedarProto", kind = "static")]
#[link(name = "Batteries", kind = "static")]
#[link(name = "CedarFFI", kind = "static")]
extern "C" {
    fn runCheckNeverErrors(req: *mut lean_object) -> *mut lean_object;
    fn runCheckAlwaysAllows(req: *mut lean_object) -> *mut lean_object;
    fn runCheckAlwaysDenies(req: *mut lean_object) -> *mut lean_object;
    fn runCheckEquivalent(req: *mut lean_object) -> *mut lean_object;
    fn runCheckImplies(req: *mut lean_object) -> *mut lean_object;
    fn runCheckDisjoint(req: *mut lean_object) -> *mut lean_object;

    fn printCheckNeverErrors(req: *mut lean_object) -> *mut lean_object;
    fn printCheckAlwaysAllows(req: *mut lean_object) -> *mut lean_object;
    fn printCheckAlwaysDenies(req: *mut lean_object) -> *mut lean_object;
    fn printCheckEquivalent(req: *mut lean_object) -> *mut lean_object;
    fn printCheckImplies(req: *mut lean_object) -> *mut lean_object;
    fn printCheckDisjoint(req: *mut lean_object) -> *mut lean_object;

    fn smtLibOfCheckNeverErrors(req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckAlwaysAllows(req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckAlwaysDenies(req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckEquivalent(req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckImplies(req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckDisjoint(req: *mut lean_object) -> *mut lean_object;

    fn isAuthorized(req: *mut lean_object) -> *mut lean_object;
    fn validate(req: *mut lean_object) -> *mut lean_object;
    fn levelValidate(req: *mut lean_object) -> *mut lean_object;
    fn printEvaluation(req: *mut lean_object) -> *mut lean_object;
    fn checkEvaluate(req: *mut lean_object) -> *mut lean_object;
    fn validateEntities(req: *mut lean_object) -> *mut lean_object;
    fn validateRequest(req: *mut lean_object) -> *mut lean_object;

    fn initialize_CedarFFI(builtin: u8, ob: *mut lean_object) -> *mut lean_object;
}

/// Lean can only be initialized once, use a static variable to know if lean backend needs
/// to be initialized
static START: Once = Once::new();

#[derive(Default)]
/// A struct which will initialize the lean backend (and initialize a thread running the lean runtime)
pub struct CedarLeanFfi {}

/// Lean return types

/// List type
#[derive(Debug, Deserialize)]
pub struct ListDef<T> {
    pub l: Vec<T>,
}

/// Set Type
#[derive(Debug, Deserialize)]
pub struct SetDef<T> {
    pub mk: ListDef<T>,
}

/// Lean type: Except String T
#[derive(Debug, Deserialize)]
enum ResultDef<T> {
    /// Successful execution
    #[serde(rename = "ok")]
    Ok(T),
    /// Failure case
    #[serde(rename = "error")]
    Error(String),
}

#[derive(Debug, Deserialize)]
struct TimedDef<T> {
    data: T,
    duration: u128,
}

#[derive(Debug)]
pub struct TimedResult<T> {
    result: T,
    duration: u128,
}

impl<T> TimedResult<T> {
    fn from_def(tdef: TimedDef<T>) -> Self {
        Self {
            result: tdef.data,
            duration: tdef.duration,
        }
    }

    /// The result of running the code
    pub fn result(&self) -> &T {
        &self.result
    }

    pub fn take_result(self) -> T {
        self.result
    }

    /// The duration the code ran for
    pub fn duration(&self) -> u128 {
        self.duration
    }
}

/// Authorization Response
#[derive(Debug, Deserialize)]
pub struct AuthorizationResponseInner {
    pub decision: String,
    #[serde(rename = "determiningPolicies")]
    pub determining_policies: SetDef<String>,
    #[serde(rename = "erroringPolicies")]
    pub erroring_policies: SetDef<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AuthorizationResponse {
    decision: Decision,
    determining: HashSet<PolicyId>,
    erroring: HashSet<PolicyId>,
}

impl AuthorizationResponse {
    fn from_inner(inner: AuthorizationResponseInner) -> Result<Self, FfiError> {
        let decision = match inner.decision.as_str() {
            "allow" => Decision::Allow,
            "deny" => Decision::Deny,
            _ => return Err(FfiError::LeanDeserializationError),
        };
        let determining = inner
            .determining_policies
            .mk
            .l
            .iter()
            .map(|pid| PolicyId::new(pid))
            .collect();
        let erroring = inner
            .erroring_policies
            .mk
            .l
            .iter()
            .map(|pid| PolicyId::new(pid))
            .collect();
        Ok(Self {
            decision,
            determining,
            erroring,
        })
    }

    pub fn decision(&self) -> Decision {
        self.decision
    }

    pub fn determining_policies(&self) -> &HashSet<PolicyId> {
        &self.determining
    }

    pub fn erroring_policies(&self) -> &HashSet<PolicyId> {
        &self.erroring
    }
}

/// Validation Response
#[derive(Debug, Deserialize)]
pub enum ValidationResponse {
    /// Successful validation
    #[serde(rename = "ok")]
    Ok(()),
    /// Validation error case
    #[serde(rename = "error")]
    Error(String),
}

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
        for i in 0..buf.len() {
            y.add(i).write(buf[i])
        }
        x.cast()
    }
}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! checkPolicy_func {
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            policy: &Policy,
            schema: &Schema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let lean_check_request =
                proto::CheckPolicyRequest::new(policy, schema, request_env).encode_to_vec();
            let lean_check_request = buf_to_lean_obj(&lean_check_request);
            let response = unsafe { $lean_func_name(lean_check_request) };
            let response = lean_obj_p_to_rust_string(response);
            match serde_json::from_str(&response) {
                Ok(ResultDef::Ok(t)) => Ok(TimedResult::from_def(t)),
                Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
                Err(_) => Err(FfiError::LeanDeserializationError),
            }
        }
        pub fn $untimed_func_name(
            &self,
            policy: &Policy,
            schema: &Schema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(policy, schema, request_env)?
                .take_result())
        }
    };
}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! checkPolicySet_func {
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            policyset: &PolicySet,
            schema: &Schema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let lean_check_request =
                proto::CheckPolicySetRequest::new(policyset, schema, request_env).encode_to_vec();
            let lean_check_request = buf_to_lean_obj(&lean_check_request);
            let response = unsafe { $lean_func_name(lean_check_request) };
            let response = lean_obj_p_to_rust_string(response);
            match serde_json::from_str(&response) {
                Ok(ResultDef::Ok(t)) => Ok(TimedResult::from_def(t)),
                Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
                Err(_) => Err(FfiError::LeanDeserializationError),
            }
        }
        pub fn $untimed_func_name(
            &self,
            policyset: &PolicySet,
            schema: &Schema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(policyset, schema, request_env)?
                .take_result())
        }
    };
}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! comparePolicySet_func {
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: &Schema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let lean_check_request = proto::ComparePolicySetsRequest::new(
                src_policyset,
                tgt_policyset,
                schema,
                request_env,
            )
            .encode_to_vec();
            let lean_check_request = buf_to_lean_obj(&lean_check_request);
            let response = unsafe { $lean_func_name(lean_check_request) };
            let response = lean_obj_p_to_rust_string(response);
            match serde_json::from_str(&response) {
                Ok(ResultDef::Ok(t)) => Ok(TimedResult::from_def(t)),
                Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
                Err(_) => Err(FfiError::LeanDeserializationError),
            }
        }
        pub fn $untimed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: &Schema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(src_policyset, tgt_policyset, schema, request_env)?
                .take_result())
        }
    };
}

impl CedarLeanFfi {
    /// WARNING: we can only have one Lean thread
    pub fn new() -> Self {
        START.call_once(|| {
            unsafe {
                // following: https://lean-lang.org/lean4/doc/dev/ffi.html
                lean_initialize_runtime_module_locked();
                let builtin: u8 = 1;
                let res = initialize_CedarFFI(builtin, lean_io_mk_world());
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

    // Adds each of the run_(symcc-command) to call the corresponding lean function
    // returns true if the check definitely holds and false if it definitely doesn't
    // returns an error if the lean could not successfully run the solver or if the solver returned unknown
    checkPolicy_func!(
        run_check_never_errors_timed,
        run_check_never_errors,
        runCheckNeverErrors,
        bool
    );

    checkPolicySet_func!(
        run_check_always_allows_timed,
        run_check_always_allows,
        runCheckAlwaysAllows,
        bool
    );

    checkPolicySet_func!(
        run_check_always_denies_timed,
        run_check_always_denies,
        runCheckAlwaysDenies,
        bool
    );

    comparePolicySet_func!(
        run_check_equivalent_timed,
        run_check_equivalent,
        runCheckEquivalent,
        bool
    );

    comparePolicySet_func!(
        run_check_implies_timed,
        run_check_implies,
        runCheckImplies,
        bool
    );

    comparePolicySet_func!(
        run_check_disjoint_timed,
        run_check_disjoint,
        runCheckDisjoint,
        bool
    );

    // Adds each of the print_(symcc-command) to call the corresponding lean function
    checkPolicy_func!(
        print_check_never_errors_timed,
        print_check_never_errors,
        printCheckNeverErrors,
        ()
    );

    checkPolicySet_func!(
        print_check_always_allows_timed,
        print_check_always_allows,
        printCheckAlwaysAllows,
        ()
    );

    checkPolicySet_func!(
        print_check_always_denies_timed,
        print_check_always_denies,
        printCheckAlwaysDenies,
        ()
    );

    comparePolicySet_func!(
        print_check_equivalent_timed,
        print_check_equivalent,
        printCheckEquivalent,
        ()
    );

    comparePolicySet_func!(
        print_check_implies_timed,
        print_check_implies,
        printCheckImplies,
        ()
    );

    comparePolicySet_func!(
        print_check_disjoint_timed,
        print_check_disjoint,
        printCheckDisjoint,
        ()
    );

    // Adds each of the smtlib_of_(symcc-command) to call the corresponding lean function
    checkPolicy_func!(
        smtlib_of_check_never_errors_timed,
        smtlib_of_check_never_errors,
        smtLibOfCheckNeverErrors,
        ()
    );

    checkPolicySet_func!(
        smtlib_of_check_always_allows_timed,
        smtlib_of_check_always_allows,
        smtLibOfCheckAlwaysAllows,
        ()
    );

    checkPolicySet_func!(
        smtlib_of_check_always_denies_timed,
        smtlib_of_check_always_denies,
        smtLibOfCheckAlwaysDenies,
        ()
    );

    comparePolicySet_func!(
        smtlib_of_check_equivalent_timed,
        smtlib_of_check_equivalent,
        smtLibOfCheckEquivalent,
        ()
    );

    comparePolicySet_func!(
        smtlib_of_check_implies_timed,
        smtlib_of_check_implies,
        smtLibOfCheckImplies,
        ()
    );

    comparePolicySet_func!(
        smtlib_of_check_disjoint_timed,
        smtlib_of_check_disjoint,
        smtLibOfCheckDisjoint,
        ()
    );

    /// Calls the lean backend to determine if the `Request` is allowed
    /// by the `PolicySet` given the provided set of `Entities`
    pub fn is_authorized_timed(
        &self,
        policyset: &PolicySet,
        entities: &Entities,
        request: &Request,
    ) -> Result<TimedResult<AuthorizationResponse>, FfiError> {
        let lean_auth_request =
            proto::AuthorizationRequest::new(policyset, entities, request).encode_to_vec();
        let lean_auth_request = buf_to_lean_obj(&lean_auth_request);
        let response = unsafe { isAuthorized(lean_auth_request) };
        let response = lean_obj_p_to_rust_string(response);
        let result: Result<ResultDef<TimedDef<AuthorizationResponseInner>>, _> =
            serde_json::from_str(&response);
        match result {
            Ok(ResultDef::Ok(resp)) => {
                let tdef = TimedDef {
                    data: AuthorizationResponse::from_inner(resp.data)?,
                    duration: resp.duration,
                };
                Ok(TimedResult::from_def(tdef))
            }
            Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
            Err(_) => Err(FfiError::LeanDeserializationError),
        }
    }
    pub fn is_authorized(
        &self,
        policyset: &PolicySet,
        entities: &Entities,
        request: &Request,
    ) -> Result<AuthorizationResponse, FfiError> {
        Ok(self
            .is_authorized_timed(policyset, entities, request)?
            .take_result())
    }

    /// Calls the lean backend to print the evaluation of the input Cedar `Expression`
    pub fn print_evaluation_timed(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
    ) -> Result<TimedResult<()>, FfiError> {
        let lean_eval_request =
            proto::EvaluationRequestChecked::new(input_expr, entities, request).encode_to_vec();
        let lean_eval_request = buf_to_lean_obj(&lean_eval_request);
        let ret = unsafe { printEvaluation(lean_eval_request) };
        let ret = lean_obj_p_to_rust_string(ret);
        match serde_json::from_str(&ret) {
            Ok(ResultDef::Ok(t)) => Ok(TimedResult::from_def(t)),
            Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
            Err(_) => Err(FfiError::LeanDeserializationError),
        }
    }
    pub fn print_evaluation(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
    ) -> Result<(), FfiError> {
        Ok(self
            .print_evaluation_timed(input_expr, entities, request)?
            .take_result())
    }

    /// Calls the lean backend and returns `true` if the input Cedar `Expression`
    /// evaluates to the output cedar `Expression`
    pub fn check_evaluate_timed(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
        output_expr: &Expression,
    ) -> Result<TimedResult<bool>, FfiError> {
        let lean_eval_request = proto::EvaluationRequestChecked::new_checked(
            input_expr,
            entities,
            request,
            output_expr,
        )
        .encode_to_vec();
        let lean_eval_request = buf_to_lean_obj(&lean_eval_request);
        let ret = unsafe { checkEvaluate(lean_eval_request) };
        let ret = lean_obj_p_to_rust_string(ret);
        match serde_json::from_str(&ret) {
            Ok(ResultDef::Ok(are_eq)) => Ok(TimedResult::from_def(are_eq)),
            Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
            Err(_) => Err(FfiError::LeanDeserializationError),
        }
    }
    pub fn check_evaluate(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
        output_expr: &Expression,
    ) -> Result<bool, FfiError> {
        Ok(self
            .check_evaluate_timed(input_expr, entities, request, output_expr)?
            .take_result())
    }

    /// Calls the lean backend to validate the `PolicySet` against the provided `Schema`
    pub fn validate_timed(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        mode: &ValidationMode,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let lean_validation_request =
            proto::ValidationRequest::new(policyset, schema, mode).encode_to_vec();
        let lean_validation_request = buf_to_lean_obj(&lean_validation_request);
        let ret = unsafe { validate(lean_validation_request) };
        let ret = lean_obj_p_to_rust_string(ret);
        match serde_json::from_str(&ret) {
            Ok(ResultDef::Ok(res)) => Ok(TimedResult::from_def(res)),
            Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
            Err(_) => Err(FfiError::LeanDeserializationError),
        }
    }
    pub fn validate(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        mode: &ValidationMode,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self.validate_timed(policyset, schema, mode)?.take_result())
    }

    /// Calls the lean backend to validate the `PolicySet` against the provided `Schema` at level `level`
    pub fn level_validate_timed(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        level: i32,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let lean_validation_request =
            proto::LevelValidationRequest::new(policyset, schema, level).encode_to_vec();
        let lean_validation_request = buf_to_lean_obj(&lean_validation_request);
        let ret = unsafe { levelValidate(lean_validation_request) };
        let ret = lean_obj_p_to_rust_string(ret);
        match serde_json::from_str(&ret) {
            Ok(ResultDef::Ok(res)) => Ok(TimedResult::from_def(res)),
            Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
            Err(_) => Err(FfiError::LeanDeserializationError),
        }
    }
    pub fn level_validate(
        &self,
        policyset: &PolicySet,
        schema: &Schema,
        level: i32,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self
            .level_validate_timed(policyset, schema, level)?
            .take_result())
    }

    /// Calls the lean backend to validate the `Entities` against the provided `Schema`
    pub fn validate_entities_timed(
        &self,
        schema: &Schema,
        entities: &Entities,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let lean_validation_request =
            proto::EntityValidationRequest::new(schema, entities).encode_to_vec();
        let lean_validation_request = buf_to_lean_obj(&lean_validation_request);
        let ret = unsafe { validateEntities(lean_validation_request) };
        let ret = lean_obj_p_to_rust_string(ret);
        match serde_json::from_str(&ret) {
            Ok(ResultDef::Ok(res)) => Ok(TimedResult::from_def(res)),
            Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
            Err(_) => Err(FfiError::LeanDeserializationError),
        }
    }
    pub fn validate_entities(
        &self,
        schema: &Schema,
        entities: &Entities,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self
            .validate_entities_timed(schema, entities)?
            .take_result())
    }

    /// Calls the lean backend to validate the `Request` against the provided `Schema`
    pub fn validate_request_timed(
        &self,
        schema: &Schema,
        request: &Request,
    ) -> Result<TimedResult<ValidationResponse>, FfiError> {
        let lean_validation_request =
            proto::RequestValidationRequest::new(schema, request).encode_to_vec();
        let lean_validation_request = buf_to_lean_obj(&lean_validation_request);
        let ret = unsafe { validateRequest(lean_validation_request) };
        let ret = lean_obj_p_to_rust_string(ret);
        match serde_json::from_str(&ret) {
            Ok(ResultDef::Ok(res)) => Ok(TimedResult::from_def(res)),
            Ok(ResultDef::Error(s)) => Err(FfiError::LeanBackendError(s)),
            Err(_) => Err(FfiError::LeanDeserializationError),
        }
    }
    pub fn validate_request(
        &self,
        schema: &Schema,
        request: &Request,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self.validate_request_timed(schema, request)?.take_result())
    }
}

/// uninitialize lean thread when done
impl Drop for CedarLeanFfi {
    fn drop(&mut self) {
        unsafe { lean_finalize_thread() }
    }
}
