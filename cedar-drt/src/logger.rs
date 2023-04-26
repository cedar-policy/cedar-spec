use std::time::{Duration, Instant};

pub const RUST_SERIALIZATION_MSG: &str = "rust_serialization (ns) : ";
pub const RUST_DESERIALIZATION_MSG: &str = "rust_deserialization (ns) : ";
pub const RUST_AUTH_MSG: &str = "rust_auth (ns) : ";
pub const RUST_VALIDATION_MSG: &str = "rust_validation (ns) : ";
pub const JAVA_SERIALIZATION_MSG: &str = "java_serialization (ns) : ";
pub const JAVA_DESERIALIZATION_MSG: &str = "java_deserialization (ns) : ";
pub const JAVA_AUTH_MSG: &str = "java_auth (ns) : ";
pub const JAVA_VALIDATION_MSG: &str = "java_validation (ns) : ";
pub const TOTAL_MSG: &str = "total (ns) : ";

pub fn time_function<X, F>(f: F) -> (X, Duration)
where
    F: FnOnce() -> X,
{
    let start = Instant::now();
    let result = f();
    (result, start.elapsed())
}
