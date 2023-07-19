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

#![forbid(unsafe_code)]
pub use cedar_policy::Response;
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationMode, ValidationResult, ValidatorSchema};
pub use entities::Entities;
use jni::objects::{JObject, JString, JValue};
use jni::{JNIVersion, JavaVM};
use lazy_static::lazy_static;
use serde::{Deserialize, Serialize};
mod logger;
use log::{info, warn};
pub use logger::*;

pub fn initialize_log() {
    match env_logger::try_init() {
        Ok(()) => (),
        Err(e) => warn!("SetLogError : {}", e),
    };
}

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
struct RequestForDefEngine<'a> {
    request: &'a ast::Request,
    policies: &'a ast::PolicySet,
    entities: &'a Entities,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct DefinitionalAuthResponse {
    serialization_nanos: i64,
    deserialization_nanos: i64,
    auth_nanos: i64,
    response: Response,
}

/// The lifetime parameter 'j is the lifetime of the JVM instance
pub struct DefinitionalEngine<'j> {
    /// Thread attached to the JVM
    thread: jni::AttachGuard<'j>,
    /// Java `DefinitionalEngine` instance
    java_def_engine: JObject<'j>,
}

impl<'j> DefinitionalEngine<'j> {
    /// Create a new `DefinitionalEngine` instance
    pub fn new() -> Result<Self, String> {
        let thread = JVM
            .attach_current_thread()
            .map_err(|e| format!("failed to attach current thread: {e}"))?;
        let def_engine_class = thread
            .find_class("com/CedarDefinitionalImplementation/DefinitionalEngine")
            .map_err(|e| format!("failed to find class: {e}"))?;
        let java_def_engine = thread
            .new_object(def_engine_class, "()V", &[])
            .map_err(|e| format!("failed to construct DefinitionalEngine instance: {e}"))?;
        Ok(Self {
            thread,
            java_def_engine,
        })
    }

    fn serialize_request(
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

    fn deserialize_response(&self, response: JValue) -> Response {
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
            logger::JAVA_SERIALIZATION_MSG,
            d_response.serialization_nanos
        );
        info!(
            "{}{}",
            logger::JAVA_DESERIALIZATION_MSG,
            d_response.deserialization_nanos
        );
        info!("{}{}", logger::JAVA_AUTH_MSG, d_response.auth_nanos);

        d_response.response
    }

    /// Ask the definitional engine whether `isAuthorized` for the given `request`,
    /// `policies`, and `entities`
    pub fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> Response {
        let (jstring, dur) = time_function(|| self.serialize_request(request, policies, entities));
        info!("{}{}", logger::RUST_SERIALIZATION_MSG, dur.as_nanos());
        let response = self.thread.call_method(
            self.java_def_engine,
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
        let (response, dur) = time_function(|| self.deserialize_response(response));
        info!("{}{}", logger::RUST_DESERIALIZATION_MSG, dur.as_nanos());
        self.thread
            .delete_local_ref(*jstring)
            .expect("Deletion failed");
        response
    }
}

#[derive(Debug, Serialize)]
struct RequestForDefValidator<'a> {
    schema: ValidatorSchema,
    policies: &'a ast::PolicySet,
    mode: ValidationMode,
}

#[derive(Deserialize, Debug)]
pub struct ValidationResponse {
    #[serde(rename = "validationErrors")]
    pub validation_errors: Vec<String>,
    #[serde(rename = "parseErrors")]
    pub parse_errors: Vec<String>,
}

impl ValidationResponse {
    pub fn validation_passed(&self) -> bool {
        self.validation_errors.is_empty()
    }

    pub fn parsing_succeeded(&self) -> bool {
        self.parse_errors.is_empty()
    }

    pub fn contains_error(&self, s: String) -> bool {
        self.validation_errors.contains(&s)
    }
}

#[derive(Debug, Deserialize)]
pub struct DefinitionalValResponse {
    serialization_nanos: i64,
    deserialization_nanos: i64,
    validation_nanos: i64,
    response: ValidationResponse,
}

/// The lifetime parameter 'j is the lifetime of the JVM instance
pub struct DefinitionalValidator<'j> {
    /// Thread attached to the JVM
    thread: jni::AttachGuard<'j>,
    /// Java `DefinitionalEngine` instance
    java_def_validator: JObject<'j>,
}

impl<'j> DefinitionalValidator<'j> {
    /// Create a new `DefinitionalValidator` instance
    pub fn new() -> Result<Self, String> {
        let thread = JVM
            .attach_current_thread()
            .map_err(|e| format!("failed to attach current thread: {e}"))?;
        let def_engine_class = thread
            .find_class("com/CedarDefinitionalImplementation/DefinitionalValidator")
            .map_err(|e| format!("failed to find class: {e}"))?;
        let java_def_validator = thread
            .new_object(def_engine_class, "()V", &[])
            .map_err(|e| format!("failed to construct DefinitionalValidator instance: {e}"))?;
        Ok(Self {
            thread,
            java_def_validator,
        })
    }

    fn serialize_request(
        &self,
        schema: ValidatorSchema,
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

    fn deserialize_response(&self, response: JValue) -> ValidationResponse {
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
            logger::JAVA_SERIALIZATION_MSG,
            d_response.serialization_nanos
        );
        info!(
            "{}{}",
            logger::JAVA_DESERIALIZATION_MSG,
            d_response.deserialization_nanos
        );
        info!(
            "{}{}",
            logger::JAVA_VALIDATION_MSG,
            d_response.validation_nanos
        );

        d_response.response
    }

    /// Use the definitional validator to validate the given `policies` given a `schema`
    pub fn validate(
        &self,
        schema: ValidatorSchema,
        policies: &ast::PolicySet,
        mode: ValidationMode,
    ) -> ValidationResponse {
        let (jstring, dur) = time_function(|| self.serialize_request(schema, policies, mode));
        info!("{}{}", logger::RUST_SERIALIZATION_MSG, dur.as_nanos());
        let response = self.thread.call_method(
            self.java_def_validator,
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
        let (response, dur) = time_function(|| self.deserialize_response(response));
        info!("{}{}", logger::RUST_DESERIALIZATION_MSG, dur.as_nanos());
        self.thread
            .delete_local_ref(*jstring)
            .expect("Deletion failed");
        response
    }
}
