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

//! Implementation of the [`CedarTestImplementation`] trait for the Cedar Java
//! implementation extracted from the Dafny specification.

use crate::cedar_test_impl::*;
use crate::logger::*;
use cedar_policy::frontend::is_authorized::InterfaceResponse;
use cedar_policy::integration_testing::{CustomCedarImpl, IntegrationTestValidationResult};
pub use cedar_policy::Response;
use cedar_policy_core::ast::{Expr, Value};
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidationResult, ValidatorSchema};
pub use entities::Entities;
use jni::objects::{JObject, JString, JValue};
use jni::{JNIVersion, JavaVM};
use lazy_static::lazy_static;
use log::info;
use serde::{Deserialize, Serialize};

/// Times to (de)serialize JSON content sent to / received from the Dafny-Java
/// implementation.
pub const RUST_SERIALIZATION_MSG: &str = "rust_serialization (ns) : ";
pub const RUST_DESERIALIZATION_MSG: &str = "rust_deserialization (ns) : ";

/// Times for cedar-policy authorization and validation.
pub const RUST_AUTH_MSG: &str = "rust_auth (ns) : ";
pub const RUST_VALIDATION_MSG: &str = "rust_validation (ns) : ";

/// Times for JSON (de)serialization, authorization, and validation as reported
/// by the Dafny-Java implementation.
pub const JAVA_SERIALIZATION_MSG: &str = "java_serialization (ns) : ";
pub const JAVA_DESERIALIZATION_MSG: &str = "java_deserialization (ns) : ";
pub const JAVA_AUTH_MSG: &str = "java_auth (ns) : ";
pub const JAVA_VALIDATION_MSG: &str = "java_validation (ns) : ";

lazy_static! {
    /// The JVM instance
    static ref JVM: JavaVM = {
        let classpath_opt = match std::env::var("CLASSPATH") {
            Ok(val) => format!("-Djava.class.path={val}"),
            Err(std::env::VarError::NotPresent) => String::new(),
            Err(std::env::VarError::NotUnicode(_)) => panic!("classpath not unicode"),
        };
        let jvm_args = jni::InitArgsBuilder::new()
            .version(JNIVersion::V8)
            .option("-Xcheck:jni")
            //.option("-verbose:class")
            .option(&classpath_opt)
            .build()
            .expect("failed to create JVM args");
        JavaVM::new(jvm_args).expect("failed to create JVM instance")
    };
}

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

/// The lifetime parameter 'j is the lifetime of the JVM instance
pub struct JavaDefinitionalEngine<'j> {
    /// Thread attached to the JVM
    thread: jni::AttachGuard<'j>,
    /// Definitional authorizer instance
    def_authorizer: JObject<'j>,
    /// Definitional validator instance
    def_validator: JObject<'j>,
}

impl<'j> JavaDefinitionalEngine<'j> {
    /// Create a new `JavaDefinitionalEngine` instance.
    ///
    /// This is a relatively expensive operation, so avoid calling it frequently.
    pub fn new() -> Result<Self, String> {
        let thread = JVM
            .attach_current_thread()
            .map_err(|e| format!("failed to attach current thread: {e}"))?;
        let def_authorizer_class = thread
            .find_class("com/CedarDefinitionalImplementation/DefinitionalEngine")
            .map_err(|e| format!("failed to find class: {e}"))?;
        let def_authorizer = thread
            .new_object(def_authorizer_class, "()V", &[])
            .map_err(|e| format!("failed to construct DefinitionalEngine instance: {e}"))?;
        let def_validator_class = thread
            .find_class("com/CedarDefinitionalImplementation/DefinitionalValidator")
            .map_err(|e| format!("failed to find class: {e}"))?;
        let def_validator = thread
            .new_object(def_validator_class, "()V", &[])
            .map_err(|e| format!("failed to construct DefinitionalValidator instance: {e}"))?;
        Ok(Self {
            thread,
            def_authorizer,
            def_validator,
        })
    }

    fn serialize_eval_request(
        &self,
        request: &ast::Request,
        entities: &Entities,
        expr: &Expr,
        expected: Option<&Expr>,
    ) -> JString {
        let request: String = serde_json::to_string(&EvalRequestForDefEngine {
            request,
            entities,
            expr,
            expected,
        })
        .expect("Failed to serialize request");
        self.thread
            .new_string(request)
            .expect("failed to create Java object for eval request string")
    }

    fn deserialize_eval_response(&self, response: JValue) -> bool {
        let jstr = response
            .l()
            .unwrap_or_else(|_| {
                panic!(
                    "expected eval_str to return an Object (String), but it returned {:?}",
                    response
                )
            })
            .into();
        let response: String = self
            .thread
            .get_string(jstr)
            .expect("Failed to get JavaStr")
            .into();
        self.thread
            .delete_local_ref(*jstr)
            .expect("Deletion failed");
        let r: DefinitionalEvalResponse = serde_json::from_str(&response).unwrap_or_else(|_| {
            panic!(
                "JSON response received from the definitional engine was malformed: \n{response}"
            )
        });
        r.matches
    }

    pub fn eval(
        &self,
        request: &ast::Request,
        entities: &Entities,
        expr: &Expr,
        expected: Option<Value>,
    ) -> bool {
        let expected_as_expr = expected.map(|v| v.into());
        let jstr = self.serialize_eval_request(request, entities, expr, expected_as_expr.as_ref());
        let response = self.thread.call_method(
            self.def_authorizer,
            "eval_str",
            "(Ljava/lang/String;)Ljava/lang/String;",
            &[jstr.into()],
        );
        match response {
            Ok(v) => self.deserialize_eval_response(v),
            Err(e) => {
                self.thread
                    .exception_describe()
                    .expect("Failed to print exception information");
                panic!("JVM Exception Occurred!: {:?}", e);
            }
        }
    }

    fn serialize_auth_request(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> JString {
        let request: String = serde_json::to_string(&RequestForDefEngine {
            request,
            policies,
            entities,
        })
        .expect("Failed to serialize request, policies, or entities");
        self.thread
            .new_string(request)
            .expect("failed to create Java object for authorization request string")
    }

    fn deserialize_auth_response(&self, response: JValue) -> InterfaceResponse {
        let jresponse: JString = response
            .l()
            .unwrap_or_else(|_| {
                panic!(
                    "expected isAuthorized_str to return an Object (String), but it returned {:?}",
                    response
                )
            })
            .into();
        let response: String = self
            .thread
            .get_string(jresponse)
            .expect("failed to get JavaStr")
            .into();
        self.thread
            .delete_local_ref(*jresponse)
            .expect("Deletion failed");
        let d_response: DefinitionalAuthResponse = serde_json::from_str(&response).unwrap_or_else(|_| {
            panic!(
                "JSON response received from the definitional engine was the wrong format:\n{response}",
            )
        });

        info!(
            "{}{}",
            JAVA_SERIALIZATION_MSG, d_response.serialization_nanos
        );
        info!(
            "{}{}",
            JAVA_DESERIALIZATION_MSG, d_response.deserialization_nanos
        );
        info!("{}{}", JAVA_AUTH_MSG, d_response.auth_nanos);

        d_response.response
    }

    /// Ask the definitional engine whether `isAuthorized` for the given `request`,
    /// `policies`, and `entities`
    pub fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> InterfaceResponse {
        let (jstring, dur) =
            time_function(|| self.serialize_auth_request(request, policies, entities));
        info!("{}{}", RUST_SERIALIZATION_MSG, dur.as_nanos());
        let response = self.thread.call_method(
            self.def_authorizer,
            "isAuthorized_str",
            // https://stackoverflow.com/questions/8066253/compute-a-java-functions-signature
            "(Ljava/lang/String;)Ljava/lang/String;",
            &[jstring.into()],
        );
        if response.is_err() {
            self.thread
                .exception_describe()
                .expect("Failed to print exception information");
            panic!("JVM Exception Occurred!");
        }
        let response: JValue = response.expect("failed to call Java isAuthorized_str");
        let (response, dur) = time_function(|| self.deserialize_auth_response(response));
        info!("{}{}", RUST_DESERIALIZATION_MSG, dur.as_nanos());
        self.thread
            .delete_local_ref(*jstring)
            .expect("Deletion failed");
        response
    }

    fn serialize_val_request(
        &self,
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
        mode: ValidationMode,
    ) -> JString {
        let request: String = serde_json::to_string(&RequestForDefValidator {
            schema,
            policies,
            mode,
        })
        .expect("Failed to serialize schema or policies");
        self.thread
            .new_string(request)
            .expect("failed to create Java object for validation request string")
    }

    fn deserialize_val_response(&self, response: JValue) -> ValidationInterfaceResponse {
        let jresponse: JString = response
            .l()
            .unwrap_or_else(|_| {
                panic!(
                    "expected validate_str to return an Object (String), but it returned {:?}",
                    response
                )
            })
            .into();
        let response: String = self
            .thread
            .get_string(jresponse)
            .expect("failed to get JavaStr")
            .into();
        self.thread
            .delete_local_ref(*jresponse)
            .expect("Deletion failed");
        let d_response: DefinitionalValResponse =
            serde_json::from_str(&response).unwrap_or_else(|_| {
                panic!(
                "JSON response received from the definitional validator was the wrong format:\n{response}",
            )
            });

        info!(
            "{}{}",
            JAVA_SERIALIZATION_MSG, d_response.serialization_nanos
        );
        info!(
            "{}{}",
            JAVA_DESERIALIZATION_MSG, d_response.deserialization_nanos
        );
        info!("{}{}", JAVA_VALIDATION_MSG, d_response.validation_nanos);

        d_response.response
    }

    /// Use the definitional validator to validate the given `policies` given a `schema`
    pub fn validate(
        &self,
        schema: &ValidatorSchema,
        policies: &ast::PolicySet,
        mode: ValidationMode,
    ) -> ValidationInterfaceResponse {
        let (jstring, dur) = time_function(|| self.serialize_val_request(schema, policies, mode));
        info!("{}{}", RUST_SERIALIZATION_MSG, dur.as_nanos());
        let response = self.thread.call_method(
            self.def_validator,
            "validate_str",
            // https://stackoverflow.com/questions/8066253/compute-a-java-functions-signature
            "(Ljava/lang/String;)Ljava/lang/String;",
            &[jstring.into()],
        );
        if response.is_err() {
            self.thread
                .exception_describe()
                .expect("Failed to print exception information");
            panic!("JVM Exception Occurred!");
        }
        let response: JValue = response.expect("failed to call Java validate_str");
        let (response, dur) = time_function(|| self.deserialize_val_response(response));
        info!("{}{}", RUST_DESERIALIZATION_MSG, dur.as_nanos());
        self.thread
            .delete_local_ref(*jstring)
            .expect("Deletion failed");
        response
    }
}

impl<'j> CedarTestImplementation for JavaDefinitionalEngine<'j> {
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
        request: &ast::Request,
        entities: &Entities,
        expr: &Expr,
        expected: Option<Value>,
    ) -> bool {
        self.eval(request, entities, expr, expected)
    }

    fn validate(
        &self,
        schema: &cedar_policy_validator::ValidatorSchema,
        policies: &ast::PolicySet,
        mode: ValidationMode,
    ) -> ValidationInterfaceResponse {
        self.validate(schema, policies, mode)
    }
}

/// Implementation of the trait used for integration testing.
impl<'j> CustomCedarImpl for JavaDefinitionalEngine<'j> {
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
    ) -> cedar_policy::integration_testing::IntegrationTestValidationResult {
        let definitional_res = self.validate(
            &schema,
            policies,
            cedar_policy_validator::ValidationMode::default(),
        );
        assert!(
            definitional_res.parsing_succeeded(),
            "Dafny json parsing failed for:\nPolicies:\n{}\nSchema:\n{:?}Errors:\n{:?}",
            &policies,
            schema,
            definitional_res.parse_errors
        );
        IntegrationTestValidationResult {
            validation_passed: definitional_res.validation_passed(),
            validation_errors_debug: format!("{:?}", definitional_res.validation_errors),
        }
    }
}
