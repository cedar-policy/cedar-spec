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
use crate::datatypes::{
    AuthorizationResponse, AuthorizationResponseInner, Env, ResultDef, Term, TimedDef, TimedResult,
    ValidationResponse,
};
use crate::err::FfiError;
use crate::lean_object::{
    call_lean_ffi_takes_obj_and_protobuf, call_lean_ffi_takes_protobuf, OwnedLeanObject,
};
use crate::messages::*;

use cedar_policy::{
    Decision, Effect, Entities, Expression, Policy, PolicySet, Request, RequestEnv, Schema,
    ValidationMode,
};
use lean_sys::{
    lean_dec, lean_dec_ref, lean_finalize_thread, lean_initialize_runtime_module_locked,
    lean_initialize_thread, lean_io_mark_end_initialization, lean_io_mk_world,
    lean_io_result_is_ok, lean_io_result_show_error, lean_object, lean_set_exit_on_panic,
};

use std::sync::Once;

mod test_implementation;

// Import and signal RUST to link the exported Lean FFI code (which are C functions at this point)
#[allow(clippy::duplicated_attributes)]
#[link(name = "Cedar", kind = "static")]
#[link(name = "Cedar_SymCC", kind = "static")]
#[link(name = "Protobuf", kind = "static")]
#[link(name = "CedarProto", kind = "static")]
#[link(name = "Batteries", kind = "static")]
#[link(name = "CedarFFI", kind = "static")]
extern "C" {
    fn runCheckNeverErrors(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckNeverErrorsWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysAllows(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckAlwaysAllowsWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckAlwaysDenies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckAlwaysDeniesWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckEquivalent(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckEquivalentWithCex(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn runCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckImpliesWithCex(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn runCheckDisjointWithCex(schema: *mut lean_object, req: *mut lean_object)
        -> *mut lean_object;

    fn printCheckNeverErrors(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckAlwaysAllows(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckAlwaysDenies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckEquivalent(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn printCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;

    fn smtLibOfCheckNeverErrors(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckAlwaysAllows(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckAlwaysDenies(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn smtLibOfCheckEquivalent(schema: *mut lean_object, req: *mut lean_object)
        -> *mut lean_object;
    fn smtLibOfCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;

    fn isAuthorized(req: *mut lean_object) -> *mut lean_object;
    fn validate(req: *mut lean_object) -> *mut lean_object;
    fn levelValidate(req: *mut lean_object) -> *mut lean_object;
    fn printEvaluation(req: *mut lean_object) -> *mut lean_object;
    fn checkEvaluate(req: *mut lean_object) -> *mut lean_object;
    fn validateEntities(req: *mut lean_object) -> *mut lean_object;
    fn validateRequest(req: *mut lean_object) -> *mut lean_object;

    fn runCheckAsserts(schema: *mut lean_object, asserts: *mut lean_object) -> *mut lean_object;
    fn printCheckAsserts(schema: *mut lean_object, asserts: *mut lean_object) -> *mut lean_object;
    fn smtLibOfCheckAsserts(
        schema: *mut lean_object,
        asserts: *mut lean_object,
    ) -> *mut lean_object;

    fn assertsOfCheckNeverErrors(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckNeverErrorsOnOriginal(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckAlwaysAllows(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckAlwaysAllowsOnOriginal(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckAlwaysDenies(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckAlwaysDeniesOnOriginal(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckEquivalent(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckEquivalentOnOriginal(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckImplies(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn assertsOfCheckImpliesOnOriginal(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;
    fn assertsOfCheckDisjoint(schema: *mut lean_object, req: *mut lean_object) -> *mut lean_object;
    fn assertsOfCheckDisjointOnOriginal(
        schema: *mut lean_object,
        req: *mut lean_object,
    ) -> *mut lean_object;

    fn batchedEvaluateFFI(req: *mut lean_object) -> *mut lean_object;

    fn initialize_CedarFFI(builtin: u8, ob: *mut lean_object) -> *mut lean_object;

    fn loadProtobufSchema(req: *mut lean_object) -> *mut lean_object;

    #[cfg(test)]
    static ffiTestString: *mut lean_object;
    #[cfg(test)]
    static ffiTestExceptOk: *mut lean_object;
    #[cfg(test)]
    static ffiTestExceptErr: *mut lean_object;
}

/// New type wrapper around a `OwnedLeanObject` containing a schema which has already been parsed into a Lean object.
#[derive(Clone, Debug)]
pub struct LeanSchema(OwnedLeanObject);

/// Lean can only be initialized once, use a static variable to know if lean backend needs
/// to be initialized
static START: Once = Once::new();

#[derive(Default)]
/// A struct which will initialize the lean backend (and initialize a thread running the lean runtime)
pub struct CedarLeanFfi {}

/// A macro which converts symcc-request to protobuf, calls the lean code, then deserializes the output
macro_rules! checkPolicy_func {
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        checkPolicy_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        checkPolicy_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            policy: &Policy,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::CheckPolicyRequest::new(policy, request_env),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            policy: &Policy,
            schema: LeanSchema,
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
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        checkPolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        checkPolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::CheckPolicySetRequest::new(policyset, request_env),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            policyset: &PolicySet,
            schema: LeanSchema,
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
    // Pattern for function identifier
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        comparePolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        comparePolicySet_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::ComparePolicySetsRequest::new(
                    src_policyset,
                    tgt_policyset,
                    request_env,
                ),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            src_policyset: &PolicySet,
            tgt_policyset: &PolicySet,
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self
                .$timed_func_name(src_policyset, tgt_policyset, schema, request_env)?
                .take_result())
        }
    };
}

macro_rules! checkAsserts_func {
    // Pattern for function identifier
    (&timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:ident, $ret_ty:ty) => {
        checkAsserts_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Pattern for closure expression
    ($timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        checkAsserts_func!(@internal $timed_func_name, $untimed_func_name, $lean_func_name, $transform, $ret_ty);
    };
    // Internal implementation
    (@internal $timed_func_name:ident, $untimed_func_name:ident, $lean_func_name:ident, $transform:expr, $ret_ty:ty) => {
        pub fn $timed_func_name(
            &self,
            asserts: &[Term],
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<TimedResult<$ret_ty>, FfiError> {
            let response = unsafe { call_lean_ffi_takes_obj_and_protobuf(
                $lean_func_name,
                schema.0,
                &proto::CheckAssertsRequest::new(asserts, request_env),
            )};
            match response.as_borrowed().deserialize_into()? {
                ResultDef::Ok(t) => Ok(TimedResult::from_def(t).transform($transform)),
                ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
            }
        }
        pub fn $untimed_func_name(
            &self,
            asserts: &[Term],
            schema: LeanSchema,
            request_env: &RequestEnv,
        ) -> Result<$ret_ty, FfiError> {
            Ok(self.$timed_func_name(asserts, schema, request_env)?.take_result())
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
        |x| x,
        bool
    );

    checkPolicy_func!(
        run_check_never_errors_with_cex_timed,
        run_check_never_errors_with_cex,
        runCheckNeverErrorsWithCex,
        |x| x,
        Option<Env>
    );

    checkPolicySet_func!(
        run_check_always_allows_timed,
        run_check_always_allows,
        runCheckAlwaysAllows,
        |x| x,
        bool
    );

    checkPolicySet_func!(
        run_check_always_allows_with_cex_timed,
        run_check_always_allows_with_cex,
        runCheckAlwaysAllowsWithCex,
        |x| x,
        Option<Env>
    );

    checkPolicySet_func!(
        run_check_always_denies_timed,
        run_check_always_denies,
        runCheckAlwaysDenies,
        |x| x,
        bool
    );

    checkPolicySet_func!(
        run_check_always_denies_with_cex_timed,
        run_check_always_denies_with_cex,
        runCheckAlwaysDeniesWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicySet_func!(
        run_check_equivalent_timed,
        run_check_equivalent,
        runCheckEquivalent,
        |x| x,
        bool
    );

    comparePolicySet_func!(
        run_check_equivalent_with_cex_timed,
        run_check_equivalent_with_cex,
        runCheckEquivalentWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicySet_func!(
        run_check_implies_timed,
        run_check_implies,
        runCheckImplies,
        |x| x,
        bool
    );

    comparePolicySet_func!(
        run_check_implies_with_cex_timed,
        run_check_implies_with_cex,
        runCheckImpliesWithCex,
        |x| x,
        Option<Env>
    );

    comparePolicySet_func!(
        run_check_disjoint_timed,
        run_check_disjoint,
        runCheckDisjoint,
        |x| x,
        bool
    );

    comparePolicySet_func!(
        run_check_disjoint_with_cex_timed,
        run_check_disjoint_with_cex,
        runCheckDisjointWithCex,
        |x| x,
        Option<Env>
    );

    // Adds each of the print_(symcc-command) to call the corresponding lean function
    checkPolicy_func!(
        print_check_never_errors_timed,
        print_check_never_errors,
        printCheckNeverErrors,
        |x| x,
        ()
    );

    checkPolicySet_func!(
        print_check_always_allows_timed,
        print_check_always_allows,
        printCheckAlwaysAllows,
        |x| x,
        ()
    );

    checkPolicySet_func!(
        print_check_always_denies_timed,
        print_check_always_denies,
        printCheckAlwaysDenies,
        |x| x,
        ()
    );

    comparePolicySet_func!(
        print_check_equivalent_timed,
        print_check_equivalent,
        printCheckEquivalent,
        |x| x,
        ()
    );

    comparePolicySet_func!(
        print_check_implies_timed,
        print_check_implies,
        printCheckImplies,
        |x| x,
        ()
    );

    comparePolicySet_func!(
        print_check_disjoint_timed,
        print_check_disjoint,
        printCheckDisjoint,
        |x| x,
        ()
    );

    checkAsserts_func!(
        run_check_asserts_timed,
        run_check_asserts,
        runCheckAsserts,
        |x| x,
        bool
    );

    checkAsserts_func!(
        print_check_asserts_timed,
        print_check_asserts,
        printCheckAsserts,
        |x| x,
        ()
    );

    checkAsserts_func!(
        smtlib_of_check_asserts_timed,
        smtlib_of_check_asserts,
        smtLibOfCheckAsserts,
        |x| x,
        String
    );

    checkPolicy_func!(
        asserts_of_check_never_errors_timed,
        asserts_of_check_never_errors,
        assertsOfCheckNeverErrors,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicy_func!(
        asserts_of_check_never_errors_on_original_timed,
        asserts_of_check_never_errors_on_original,
        assertsOfCheckNeverErrorsOnOriginal,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicySet_func!(
        asserts_of_check_always_allows_timed,
        asserts_of_check_always_allows,
        assertsOfCheckAlwaysAllows,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicySet_func!(
        asserts_of_check_always_allows_on_original_timed,
        asserts_of_check_always_allows_on_original,
        assertsOfCheckAlwaysAllowsOnOriginal,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicySet_func!(
        asserts_of_check_always_denies_timed,
        asserts_of_check_always_denies,
        assertsOfCheckAlwaysDenies,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    checkPolicySet_func!(
        asserts_of_check_always_denies_on_original_timed,
        asserts_of_check_always_denies_on_original,
        assertsOfCheckAlwaysDeniesOnOriginal,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_equivalent_timed,
        asserts_of_check_equivalent,
        assertsOfCheckEquivalent,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_equivalent_on_original_timed,
        asserts_of_check_equivalent_on_original,
        assertsOfCheckEquivalentOnOriginal,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_implies_timed,
        asserts_of_check_implies,
        assertsOfCheckImplies,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_implies_on_original_timed,
        asserts_of_check_implies_on_original,
        assertsOfCheckImpliesOnOriginal,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_disjoint_timed,
        asserts_of_check_disjoint,
        assertsOfCheckDisjoint,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    comparePolicySet_func!(
        asserts_of_check_disjoint_on_original_timed,
        asserts_of_check_disjoint_on_original,
        assertsOfCheckDisjointOnOriginal,
        ResultDef::to_result,
        Result<Vec<Term>, String>
    );

    // Adds each of the smtlib_of_(symcc-command) to call the corresponding lean function
    checkPolicy_func!(
        smtlib_of_check_never_errors_timed,
        smtlib_of_check_never_errors,
        smtLibOfCheckNeverErrors,
        |x| x,
        String
    );

    checkPolicySet_func!(
        smtlib_of_check_always_allows_timed,
        smtlib_of_check_always_allows,
        smtLibOfCheckAlwaysAllows,
        |x| x,
        String
    );

    checkPolicySet_func!(
        smtlib_of_check_always_denies_timed,
        smtlib_of_check_always_denies,
        smtLibOfCheckAlwaysDenies,
        |x| x,
        String
    );

    comparePolicySet_func!(
        smtlib_of_check_equivalent_timed,
        smtlib_of_check_equivalent,
        smtLibOfCheckEquivalent,
        |x| x,
        String
    );

    comparePolicySet_func!(
        smtlib_of_check_implies_timed,
        smtlib_of_check_implies,
        smtLibOfCheckImplies,
        |x| x,
        String
    );

    comparePolicySet_func!(
        smtlib_of_check_disjoint_timed,
        smtlib_of_check_disjoint,
        smtLibOfCheckDisjoint,
        |x| x,
        String
    );

    /// Calls the lean backend to determine if the `Request` is allowed
    /// by the `PolicySet` given the provided set of `Entities`
    pub fn is_authorized_timed(
        &self,
        policyset: &PolicySet,
        entities: &Entities,
        request: &Request,
    ) -> Result<TimedResult<AuthorizationResponse>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                isAuthorized,
                &proto::AuthorizationRequest::new(policyset, entities, request),
            )
        };
        match response
            .as_borrowed()
            .deserialize_into::<ResultDef<TimedDef<AuthorizationResponseInner>>>()?
        {
            ResultDef::Ok(resp) => {
                let tdef = TimedDef {
                    data: AuthorizationResponse::from_inner(resp.data)?,
                    duration: resp.duration,
                };
                Ok(TimedResult::from_def(tdef))
            }
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
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
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                printEvaluation,
                &proto::EvaluationRequestChecked::new(input_expr, entities, request),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(t) => Ok(TimedResult::from_def(t)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn print_evaluation(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
    ) -> Result<(), FfiError> {
        self.print_evaluation_timed(input_expr, entities, request)?;
        Ok(())
    }

    /// Calls the lean backend and returns `true` if the input Cedar `Expression`
    /// evaluates to the output cedar `Expression`
    pub fn check_evaluate_timed(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
        output_expr: Option<&Expression>,
    ) -> Result<TimedResult<bool>, FfiError> {
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                checkEvaluate,
                &proto::EvaluationRequestChecked::new_checked(
                    input_expr,
                    entities,
                    request,
                    output_expr,
                ),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(are_eq) => Ok(TimedResult::from_def(are_eq)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn check_evaluate(
        &self,
        input_expr: &Expression,
        entities: &Entities,
        request: &Request,
        output_expr: Option<&Expression>,
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
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                validate,
                &proto::ValidationRequest::new(policyset, schema, mode),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
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
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                levelValidate,
                &proto::LevelValidationRequest::new(policyset, schema, level),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
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
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                validateEntities,
                &proto::EntityValidationRequest::new(schema, entities),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
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
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                validateRequest,
                &proto::RequestValidationRequest::new(schema, request),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res)),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn validate_request(
        &self,
        schema: &Schema,
        request: &Request,
    ) -> Result<ValidationResponse, FfiError> {
        Ok(self.validate_request_timed(schema, request)?.take_result())
    }

    /// Calls the lean backend to perform batched evaluation on a single policy
    pub fn batched_evaluation_timed(
        &self,
        policy: &Policy,
        schema: &Schema,
        request: &Request,
        entities: &Entities,
        iteration: u32,
    ) -> Result<TimedResult<Option<Decision>>, FfiError> {
        // We have to construct a policy set because we don't have protobuf encoding of policy yet
        let policyset = PolicySet::from_policies(std::iter::once(policy.clone()))
            .expect("policy set construction should succeed");
        let response = unsafe {
            call_lean_ffi_takes_protobuf(
                batchedEvaluateFFI,
                &proto::BatchedEvaluationRequest::new(
                    &policyset, schema, request, entities, iteration,
                ),
            )
        };
        match response.as_borrowed().deserialize_into()? {
            ResultDef::Ok(res) => Ok(TimedResult::from_def(res).transform(|b: Option<bool>| {
                match (b, policy.effect()) {
                    (Some(true), Effect::Permit) => Some(Decision::Allow),
                    (Some(_), _) | (None, Effect::Forbid) => Some(Decision::Deny),
                    // We can't make any conclusions for this case
                    (None, Effect::Permit) => None,
                }
            })),
            ResultDef::Error(s) => Err(FfiError::LeanBackendError(s)),
        }
    }
    pub fn batched_evaluation(
        &self,
        policy: &Policy,
        schema: &Schema,
        request: &Request,
        entities: &Entities,
        iteration: u32,
    ) -> Result<Option<Decision>, FfiError> {
        Ok(self
            .batched_evaluation_timed(policy, schema, request, entities, iteration)?
            .take_result())
    }

    pub fn load_lean_schema_object(&self, schema: &Schema) -> Result<LeanSchema, FfiError> {
        let lean_schema_object = unsafe {
            call_lean_ffi_takes_protobuf(
                loadProtobufSchema,
                &cedar_policy::proto::models::Schema::from(schema),
            )
        };
        match lean_schema_object.as_borrowed().as_result()? {
            Ok(lean_ok_obj) => Ok(LeanSchema(lean_ok_obj.to_owned())),
            Err(lean_err_obj) => Err(FfiError::LeanBackendError(
                lean_err_obj.as_rust_str()?.to_string(),
            )),
        }
    }
}

/// uninitialize lean thread when done
impl Drop for CedarLeanFfi {
    fn drop(&mut self) {
        unsafe { lean_finalize_thread() }
    }
}

#[cfg(test)]
mod test {
    /***************** Copy Extern Block so that Tests are also linked with lean code *****************/
    #[allow(clippy::duplicated_attributes)]
    #[link(name = "Cedar", kind = "static")]
    #[link(name = "Cedar_SymCC", kind = "static")]
    #[link(name = "Protobuf", kind = "static")]
    #[link(name = "CedarProto", kind = "static")]
    #[link(name = "Batteries", kind = "static")]
    #[link(name = "CedarFFI", kind = "static")]
    extern "C" {}

    use cedar_policy::{
        Context, Entities, Entity, EntityTypeName, EntityUid, Expression, Policy, PolicyId,
        PolicySet, Request, RequestEnv, Schema, ValidationMode,
    };
    use cool_asserts::assert_matches;

    use std::collections::HashSet;
    use std::marker::PhantomData;
    use std::str::FromStr;

    use crate::{
        lean_ffi::{ffiTestExceptErr, ffiTestExceptOk, ffiTestString},
        lean_object::LeanObject,
        CedarLeanFfi, TimedResult, ValidationResponse,
    };

    impl CedarLeanFfi {
        fn ffi_test_string(&self) -> LeanObject<'static> {
            unsafe { LeanObject(ffiTestString, PhantomData) }
        }

        fn ffi_test_except_ok(&self) -> LeanObject<'static> {
            unsafe { LeanObject(ffiTestExceptOk, PhantomData) }
        }

        fn ffi_test_except_err(&self) -> LeanObject<'static> {
            unsafe { LeanObject(ffiTestExceptErr, PhantomData) }
        }
    }

    #[test]
    fn read_test_string() {
        let ffi = CedarLeanFfi::new();
        let rust_str = ffi.ffi_test_string().as_rust_str().unwrap();
        assert_eq!(rust_str, "ffiTestString");
    }

    #[test]
    fn read_test_except_ok() {
        let ffi = CedarLeanFfi::new();
        let ok_str = ffi
            .ffi_test_except_ok()
            .as_ctor()
            .unwrap()
            .as_result()
            .unwrap()
            .unwrap()
            .as_rust_str()
            .unwrap();
        assert_eq!(ok_str, "ok");
    }

    #[test]
    fn read_test_except_err() {
        let ffi = CedarLeanFfi::new();
        let err_str = ffi
            .ffi_test_except_err()
            .as_ctor()
            .unwrap()
            .as_result()
            .unwrap()
            .unwrap_err()
            .as_rust_str()
            .unwrap();
        assert_eq!(err_str, "error");
    }

    fn example_schema() -> Schema {
        Schema::from_cedarschema_str(
            r#"
            entity Account;
            entity Identity {
                account: Account
            };
            entity Thing in Account {
                owner: Identity,
                description: String,
                private: Bool
            };
            action view appliesTo {
            principal: [Identity],
            resource: [Thing],
            context: {
                n1: String
            }
            };
            "#,
        )
        .expect("Example schema failed to parse")
        .0
    }

    #[test]
    fn load_schema() {
        let ffi = CedarLeanFfi::new();
        let schema = example_schema();
        let t = ffi.load_lean_schema_object(&schema);
        t.unwrap();
    }

    fn request(principal: &str, action: &str, resource: &str) -> Request {
        let principal = EntityUid::from_str(principal).expect("Failed to parse principal");
        let action = EntityUid::from_str(action).expect("Failed to parse action");
        let resource = EntityUid::from_str(resource).expect("Failed to parse resource");
        let ctx = Context::from_pairs([(
            "n1".to_string(),
            cedar_policy::RestrictedExpression::new_string("Some value".to_string()),
        )])
        .expect("Failed to construct context");
        Request::new(principal, action, resource, ctx, None).expect("Failed to construct request")
    }

    fn request_env(principal_type: &str, action: &str, resource_type: &str) -> RequestEnv {
        let principal_type =
            EntityTypeName::from_str(principal_type).expect("Failed to parse principal type");
        let action = EntityUid::from_str(action).expect("Failed to parse action");
        let resource_type =
            EntityTypeName::from_str(resource_type).expect("Failed to parse resource type");
        RequestEnv::new(principal_type, action, resource_type)
    }

    #[test]
    fn test_check_never_errors() {
        let trivial_policy = Policy::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_never_errors(&trivial_policy, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_never_errors");
        assert!(
            res,
            "run_check_never_errors returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_never_errors(&trivial_policy, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_never_errors");

        ffi.asserts_of_check_never_errors(&trivial_policy, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_never_errors")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_never_errors",
            );
    }

    #[test]
    fn test_check_always_allows() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_always_allows(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_allows");
        assert!(
            res,
            "run_check_always_allows returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_always_allows(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_allows");

        ffi.asserts_of_check_always_allows(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_allows")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_allows",
            );

        let res = ffi
            .run_check_always_allows(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_allows");
        assert!(
            !res,
            "run_check_always_allows returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_always_allows(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_allows");

        ffi.asserts_of_check_always_allows(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_allows")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_allows",
            );
    }

    #[test]
    fn test_check_always_denies() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_always_denies(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_denies");
        assert!(
            !res,
            "run_check_always_denies returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_always_denies(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_denies");

        ffi.asserts_of_check_always_denies(&always_allows_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_denies")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_denies",
            );

        let res = ffi
            .run_check_always_denies(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for run_check_always_denies");
        assert!(
            res,
            "run_check_always_denies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_always_denies(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for smtlib_of_check_always_denies");

        ffi.asserts_of_check_always_denies(&always_denies_pset, schema.clone(), &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_always_denies")
            .expect(
                "Lean SymCC unexpectedly failed to encode term for asserts_of_check_always_denies",
            );
    }

    #[test]
    fn test_check_equivalent() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_equivalent(
                &always_allows_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_equivalent");
        assert!(
            res,
            "run_check_equivalent returned wrong result. Expected: true"
        );

        ffi.asserts_of_check_equivalent(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_equivalent")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_equivalent");

        ffi.smtlib_of_check_equivalent(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_equivalent");

        let res = ffi
            .run_check_equivalent(
                &always_denies_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_equivalent");
        assert!(
            res,
            "run_check_equivalent returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_equivalent(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_equivalent");

        ffi.asserts_of_check_equivalent(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_equivalent")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_equivalent");

        let res = ffi
            .run_check_equivalent(
                &always_allows_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_equivalent");
        assert!(
            !res,
            "run_check_equivalent returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_equivalent(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_equivalent");

        ffi.asserts_of_check_equivalent(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_equivalent")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_equivalent");
    }

    #[test]
    fn test_check_implies() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_implies(
                &always_allows_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            res,
            "run_check_implies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_implies(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_implies")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");

        let res = ffi
            .run_check_implies(
                &always_denies_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            res,
            "run_check_implies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_implies(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_implies")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");

        let res = ffi
            .run_check_implies(
                &always_allows_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            !res,
            "run_check_implies returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_implies(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_implies")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");

        let res = ffi
            .run_check_implies(
                &always_denies_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_implies");
        assert!(
            res,
            "run_check_implies returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_implies(
            &always_denies_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_implies");

        ffi.asserts_of_check_implies(&always_denies_pset, &always_allows_pset, schema, &req_env)
            .expect("Lean call unexpectedly failed for asserts_of_check_implies")
            .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_implies");
    }

    #[test]
    fn test_check_disjoint() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let ffi = CedarLeanFfi::new();
        let schema = ffi.load_lean_schema_object(&example_schema()).unwrap();
        let req_env = request_env("Identity", "Action::\"view\"", "Thing");

        let res = ffi
            .run_check_disjoint(
                &always_allows_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            !res,
            "run_check_disjoint returned wrong result. Expected: false"
        );

        ffi.smtlib_of_check_disjoint(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_allows_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");

        let res = ffi
            .run_check_disjoint(
                &always_denies_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            res,
            "run_check_disjoint returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_disjoint(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_denies_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");

        let res = ffi
            .run_check_disjoint(
                &always_allows_pset,
                &always_denies_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            res,
            "run_check_disjoint returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_disjoint(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_allows_pset,
            &always_denies_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");

        let res = ffi
            .run_check_disjoint(
                &always_denies_pset,
                &always_allows_pset,
                schema.clone(),
                &req_env,
            )
            .expect("Lean call unexpectedly failed for run_check_disjoint");
        assert!(
            res,
            "run_check_disjoint returned wrong result. Expected: true"
        );

        ffi.smtlib_of_check_disjoint(
            &always_denies_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for smtlib_of_check_disjoint");

        ffi.asserts_of_check_disjoint(
            &always_denies_pset,
            &always_allows_pset,
            schema.clone(),
            &req_env,
        )
        .expect("Lean call unexpectedly failed for asserts_of_check_disjoint")
        .expect("Lean SymCC unexpectedly failed to encode term for asserts_of_check_disjoint");
    }

    #[test]
    fn test_is_authorized() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let always_denies_pset = PolicySet::from_str("forbid(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"Thing1\"",
        );
        let principal = Entity::with_uid(req.principal().unwrap().clone());
        let action = Entity::with_uid(req.action().unwrap().clone());
        let resource = Entity::with_uid(req.resource().unwrap().clone());
        let entities = Entities::from_entities(vec![principal, action, resource], None)
            .expect("Failed to construct entities");

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .is_authorized(&always_allows_pset, &entities, &req)
            .expect("Lean call unexpectedly failed for is_authorized");

        assert_eq!(res.decision(), cedar_policy::Decision::Allow);
        let deciding_policies = HashSet::from_iter(vec![PolicyId::from_str("policy0").unwrap()]);
        assert_eq!(*res.determining_policies(), deciding_policies);
        assert!(
            res.erroring_policies().is_empty(),
            "Always allows policyset should have no erroring policies"
        );

        let res = ffi
            .is_authorized(&always_denies_pset, &entities, &req)
            .expect("Lean call unexpectedly failed for is_authorized");
        assert_eq!(res.decision(), cedar_policy::Decision::Deny);
        assert_eq!(*res.determining_policies(), deciding_policies);
        assert!(
            res.erroring_policies().is_empty(),
            "Always denies policyset should have no erroring policies"
        );
    }

    #[test]
    fn test_print_evaluate() {
        let input_expr = Expression::from_str("1 + 2").expect("Failed to parse expression");
        let err_expr = Expression::from_str("1 + true").expect("Failed to parse expression");
        let entities = Entities::empty();
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"Thing1\"",
        );

        let ffi = CedarLeanFfi::new();

        ffi.print_evaluation(&input_expr, &entities, &req)
            .expect("Lean call unexpectedly failed for check_evaluate");

        // Erroring expressions should print the evaluation error, not result in an FFI error.
        ffi.print_evaluation(&err_expr, &entities, &req)
            .expect("Lean call unexpectedly failed for check_evaluate");
    }

    #[test]
    fn test_check_evaluate() {
        let input_expr = Expression::from_str("1 + 2").expect("Failed to parse expression");
        let eval_expr = Expression::from_str("3").expect("Failed to parse expression");
        let wrong_expr = Expression::from_str("2").expect("Failed to parse expression");
        let entities = Entities::empty();
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"Thing1\"",
        );

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .check_evaluate(&input_expr, &entities, &req, Some(&eval_expr))
            .expect("Lean call unexpectedly failed for check_evaluate");
        assert!(res, "check_evaluate returned wrong result: Expected true");

        let res = ffi
            .check_evaluate(&input_expr, &entities, &req, Some(&wrong_expr))
            .expect("Lean call unexpectedly failed for check_evaluate");
        assert!(!res, "check_evaluate returned wrong result: Expected false");
    }

    #[test]
    fn test_validate() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let schema = example_schema();
        let mode = ValidationMode::Strict;

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .validate(&always_allows_pset, &schema, &mode)
            .expect("Lean call unexpectedly failed for validate");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_level_validate() {
        let always_allows_pset = PolicySet::from_str("permit(principal, action, resource);")
            .expect("Failed to parse trivial policy set");
        let schema = example_schema();

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .level_validate(&always_allows_pset, &schema, 0)
            .expect("Lean call unexpectedly failed for level_validate");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_validate_entities() {
        let schema = example_schema();
        let account = Entity::with_uid(EntityUid::from_str("Account::\"account\"").unwrap());
        let action = Entity::with_uid(EntityUid::from_str("Action::\"view\"").unwrap());
        let entities = Entities::from_entities(vec![account, action], None)
            .expect("Failed to construct entities");

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .validate_entities(&schema, &entities)
            .expect("Lean call unexpectedly failed for validate_entities");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_validate_request() {
        let schema = example_schema();
        let req = request(
            "Identity::\"Alice\"",
            "Action::\"view\"",
            "Thing::\"thing1\"",
        );

        let ffi = CedarLeanFfi::new();

        let res = ffi
            .validate_request(&schema, &req)
            .expect("Lean call unexpectedly failed for validate_request");
        assert_eq!(res, ValidationResponse::Ok(()));
    }

    #[test]
    fn test_cex() {
        let ffi = CedarLeanFfi::new();
        let schema = ffi
            .load_lean_schema_object(
                &Schema::from_str(
                    r#"
        entity a {
          r : Bool,
        };
        action "action" appliesTo {
          principal: a,
          resource: a,
        };
        "#,
                )
                .unwrap(),
            )
            .unwrap();
        let ps = PolicySet::from_str(
            r#"
        permit(
      principal,
      action in [Action::"action"],
      resource
    ) when {
      ((true && (a::"*"["r"])) && true) && true
    };"#,
        )
        .unwrap();
        let req_env = request_env("a", "Action::\"action\"", "a");

        assert_matches!(
            ffi.run_check_always_denies_with_cex_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_always_denies_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_always_allows_with_cex_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_always_allows_timed(&ps, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_never_errors_with_cex_timed(
                ps.policies().next().unwrap(),
                schema.clone(),
                &req_env,
            ),
            Ok(TimedResult { result: None, .. })
        );
        assert_matches!(
            ffi.run_check_never_errors_timed(
                ps.policies().next().unwrap(),
                schema.clone(),
                &req_env,
            ),
            Ok(TimedResult { result: true, .. })
        );

        let ps_new = PolicySet::from_str(
            r#"
        permit(
      principal,
      action in [Action::"action"],
      resource
    ) when {
      ((true && (a::"..."["r"])) && true) && true
    };"#,
        )
        .unwrap();

        assert_matches!(
            ffi.run_check_equivalent_with_cex_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_equivalent_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_implies_with_cex_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_implies_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult { result: false, .. })
        );

        assert_matches!(
            ffi.run_check_disjoint_with_cex_timed(&ps, &ps_new, schema.clone(), &req_env),
            Ok(TimedResult {
                result: Some(_),
                ..
            })
        );
        assert_matches!(
            ffi.run_check_disjoint_timed(&ps, &ps_new, schema, &req_env),
            Ok(TimedResult { result: false, .. })
        );
    }

    #[test]
    fn test_batched_evaluation() {
        let schema = Schema::from_str(
            r#"
            namespace Taxpreparer {
  type orgInfo = {
    organization: String,
    serviceline: String,
    location: String,
  };
  // A tax-preparing professional
  entity Professional = { 
    assigned_orgs: Set<orgInfo>,
    location: String,
  };
  // A client's tax document
  entity Document = {
    serviceline: String,
    location: String,
    owner: Client,
  };
  // A client 
  entity Client = {
    organization: String
  };

  action viewDocument appliesTo {
    principal: [Professional],
    resource: [Document],
  };
}
        "#,
        )
        .expect("valid schema");
        let policy = Policy::from_str(
            r#"
        // Rule 1a: organization-level access
permit (
  principal,
  action == Taxpreparer::Action::"viewDocument",
  resource
)
when
{
  principal.assigned_orgs
    .contains
    (
      {organization
       :resource.owner.organization,
       serviceline
       :resource.serviceline,
       location
       :resource.location}
    )
};
        "#,
        )
        .expect("valid policy");
        let entities = Entities::from_json_value(
            serde_json::json!([
                {
                    "uid": {
                        "type": "Taxpreparer::Professional",
                        "id": "Alice"
                    },
                    "attrs": {
                        "location": "IAD",
                        "assigned_orgs": [
                            {
                                "organization": "org-1",
                                "serviceline": "corporate",
                                "location": "IAD"
                            }
                        ]
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Professional",
                        "id": "Bob"
                    },
                    "attrs": {
                        "location": "JFK",
                        "assigned_orgs": [
                            {
                                "organization": "org-1",
                                "serviceline": "corporate",
                                "location": "JFK"
                            }
                        ]
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Client",
                        "id": "Ramon"
                    },
                    "attrs": {
                        "organization": "org-1"
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Document",
                        "id": "ABC"
                    },
                    "attrs": {
                        "serviceline": "corporate",
                        "location": "IAD",
                        "owner": {
                            "type": "Taxpreparer::Client",
                            "id": "Ramon"
                        }
                    },
                    "parents": []
                },
                {
                    "uid": {
                        "type": "Taxpreparer::Document",
                        "id": "DEF"
                    },
                    "attrs": {
                        "serviceline": "corporate",
                        "location": "JFK",
                        "owner": {
                            "type": "Taxpreparer::Client",
                            "id": "Ramon"
                        }
                    },
                    "parents": []
                }
            ]),
            Some(&schema),
        )
        .expect("valid entities");
        let request = Request::new(
            "Taxpreparer::Professional::\"Alice\"".parse().unwrap(),
            "Taxpreparer::Action::\"viewDocument\"".parse().unwrap(),
            "Taxpreparer::Document::\"ABC\"".parse().unwrap(),
            Context::empty(),
            None,
        )
        .expect("valid request");
        let ffi = CedarLeanFfi::new();
        assert_matches!(
            ffi.batched_evaluation(&policy, &schema, &request, &entities, 3),
            Ok(Some(cedar_policy::Decision::Allow))
        );
    }

    #[test]
    fn empty_record_encoding() {
        let schema = Schema::from_str(
            r#"
            entity V;
entity N;
entity V3 = {
  "x": {}
};
action "" appliesTo {
  principal: [N],
  resource: [V],
  context: {}
};
            "#,
        )
        .unwrap();
        let pset = PolicySet::from_str(
            r#"
            permit(
  principal,
  action in [Action::""],
  resource
) when {
  {} == (V3::"".x)
};
            "#,
        )
        .unwrap();
        let request_env = request_env("N", "Action::\"\"", "V");
        let ffi = CedarLeanFfi::new();
        assert!(!ffi
            .run_check_always_denies(
                &pset,
                ffi.load_lean_schema_object(&schema).unwrap(),
                &request_env
            )
            .unwrap());
    }
}
