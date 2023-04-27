#![forbid(unsafe_code)]
pub use authorizer::Answer;
pub use cedar_policy_core::*;
pub use cedar_policy_validator::{ValidationResult, ValidatorSchema};
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
pub struct DefinitionalAuthAnswer {
    serialization_nanos: i64,
    deserialization_nanos: i64,
    auth_nanos: i64,
    answer: Answer,
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

    fn deserialize_answer(&self, answer: JValue) -> Answer {
        let janswer: JString = answer
            .l()
            .unwrap_or_else(|_| {
                panic!(
                    "expected isAuthorized_str to return an Object (String), but it returned {:?}",
                    answer
                )
            })
            .into();
        let answer: String = self
            .thread
            .get_string(janswer)
            .expect("failed to get JavaStr")
            .into();
        self.thread
            .delete_local_ref(*janswer)
            .expect("Deletion failed");
        let d_answer: DefinitionalAuthAnswer = serde_json::from_str(&answer).unwrap_or_else(|_| {
            panic!(
                "JSON answer received from the definitional engine was the wrong format:\n{answer}",
            )
        });

        info!(
            "{}{}",
            logger::JAVA_SERIALIZATION_MSG,
            d_answer.serialization_nanos
        );
        info!(
            "{}{}",
            logger::JAVA_DESERIALIZATION_MSG,
            d_answer.deserialization_nanos
        );
        info!("{}{}", logger::JAVA_AUTH_MSG, d_answer.auth_nanos);

        d_answer.answer
    }

    /// Ask the definitional engine whether `isAuthorized` for the given `request`,
    /// `policies`, and `entities`
    pub fn is_authorized(
        &self,
        request: &ast::Request,
        policies: &ast::PolicySet,
        entities: &Entities,
    ) -> Answer {
        let (jstring, dur) = time_function(|| self.serialize_request(request, policies, entities));
        info!("{}{}", logger::RUST_SERIALIZATION_MSG, dur.as_nanos());
        let answer = self.thread.call_method(
            self.java_def_engine,
            "isAuthorized_str",
            // https://stackoverflow.com/questions/8066253/compute-a-java-functions-signature
            "(Ljava/lang/String;)Ljava/lang/String;",
            &[jstring.into()],
        );
        if answer.is_err() {
            self.thread
                .exception_describe()
                .expect("Failed to print exception information");
            panic!("JVM Exception Occurred!");
        }
        let answer: JValue = answer.expect("failed to call Java isAuthorized_str");
        let (answer, dur) = time_function(|| self.deserialize_answer(answer));
        info!("{}{}", logger::RUST_DESERIALIZATION_MSG, dur.as_nanos());
        self.thread
            .delete_local_ref(*jstring)
            .expect("Deletion failed");
        answer
    }
}

#[derive(Debug, Serialize)]
struct QueryForDefValidator<'a> {
    schema: ValidatorSchema,
    policies: &'a ast::PolicySet,
}

#[derive(Deserialize, Debug)]
pub struct ValidationAnswer {
    #[serde(rename = "validationErrors")]
    pub validation_errors: Vec<String>,
    #[serde(rename = "parseErrors")]
    pub parse_errors: Vec<String>,
}

impl ValidationAnswer {
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
pub struct DefinitionalValAnswer {
    serialization_nanos: i64,
    deserialization_nanos: i64,
    validation_nanos: i64,
    answer: ValidationAnswer,
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

    fn serialize_query(&self, schema: ValidatorSchema, policies: &ast::PolicySet) -> JString {
        let query: String = serde_json::to_string(&QueryForDefValidator { schema, policies })
            .expect("Failed to serialize schema or policies");
        self.thread
            .new_string(query)
            .expect("failed to create Java object for validation query string")
    }

    fn deserialize_answer(&self, answer: JValue) -> ValidationAnswer {
        let janswer: JString = answer
            .l()
            .unwrap_or_else(|_| {
                panic!(
                    "expected validate_str to return an Object (String), but it returned {:?}",
                    answer
                )
            })
            .into();
        let answer: String = self
            .thread
            .get_string(janswer)
            .expect("failed to get JavaStr")
            .into();
        self.thread
            .delete_local_ref(*janswer)
            .expect("Deletion failed");
        let d_answer: DefinitionalValAnswer =
            serde_json::from_str(&answer).unwrap_or_else(|_| {
                panic!(
                "JSON answer received from the definitional validator was the wrong format:\n{answer}",
            )
            });

        info!(
            "{}{}",
            logger::JAVA_SERIALIZATION_MSG,
            d_answer.serialization_nanos
        );
        info!(
            "{}{}",
            logger::JAVA_DESERIALIZATION_MSG,
            d_answer.deserialization_nanos
        );
        info!(
            "{}{}",
            logger::JAVA_VALIDATION_MSG,
            d_answer.validation_nanos
        );

        d_answer.answer
    }

    /// Use the definitional validator to validate the given `policies` given a `schema`
    pub fn validate(&self, schema: ValidatorSchema, policies: &ast::PolicySet) -> ValidationAnswer {
        let (jstring, dur) = time_function(|| self.serialize_query(schema, policies));
        info!("{}{}", logger::RUST_SERIALIZATION_MSG, dur.as_nanos());
        let answer = self.thread.call_method(
            self.java_def_validator,
            "validate_str",
            // https://stackoverflow.com/questions/8066253/compute-a-java-functions-signature
            "(Ljava/lang/String;)Ljava/lang/String;",
            &[jstring.into()],
        );
        if answer.is_err() {
            self.thread
                .exception_describe()
                .expect("Failed to print exception information");
            panic!("JVM Exception Occurred!");
        }
        let answer: JValue = answer.expect("failed to call Java validate_str");
        let (answer, dur) = time_function(|| self.deserialize_answer(answer));
        info!("{}{}", logger::RUST_DESERIALIZATION_MSG, dur.as_nanos());
        self.thread
            .delete_local_ref(*jstring)
            .expect("Deletion failed");
        answer
    }
}
