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
use log::warn;
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

pub fn initialize_log() {
    match env_logger::try_init() {
        Ok(()) => (),
        Err(e) => {
            let msg = e.to_string();
            if &msg == "attempted to set a logger after the logging system was already initialized"
            {
                // don't log that error, it's expected
            } else {
                warn!("SetLogError : {msg}");
            }
        }
    };
}

pub fn time_function<X, F>(f: F) -> (X, Duration)
where
    F: FnOnce() -> X,
{
    let start = Instant::now();
    let result = f();
    (result, start.elapsed())
}
