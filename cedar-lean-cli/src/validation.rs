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
use crate::err::ExecError;
use cedar_lean_ffi::{CedarLeanFfi, ValidationResponse};
use cedar_policy::{Entities, PolicySet, Request, Schema, ValidationMode};

/// Validate (using the lean_ffi backend) that the input `PolicySet` matches the provided
/// `Schema` for the given `ValidationMode` (Strict or Permissive)
pub fn validate(
    policyset: &PolicySet,
    schema: &Schema,
    mode: &ValidationMode,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    match lean_context.validate(policyset, schema, mode)? {
        ValidationResponse::Ok(()) => {
            println!("Policyset successfully validated");
            Ok(())
        }
        ValidationResponse::Error(s) => {
            println!("Policyset failed to validate: {s}");
            Ok(())
        }
    }
}

/// Validates (using the lean_ffi backend) that the input `PolicySet` matches the provided
/// `Schema` at level `level`. Level 0 means no entity or context record fields are accessed.
/// Level `i` means that record fields are accessed upto depth `i`.
pub fn level_validate(policyset: &PolicySet, schema: &Schema, level: i32) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    match lean_context.level_validate(policyset, schema, level)? {
        ValidationResponse::Ok(()) => {
            println!("Policyset successfully validated at level {level}");
            Ok(())
        }
        ValidationResponse::Error(s) => {
            println!("Policyset failed to validate at level {level}: {s}");
            Ok(())
        }
    }
}

/// Validates (using the lean_ffi backend) that the input `Entities` matches the provided `Schema`
pub fn validate_entities(schema: &Schema, entities: &Entities) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    match lean_context.validate_entities(schema, entities)? {
        ValidationResponse::Ok(()) => {
            println!("Entities successfully validated");
            Ok(())
        }
        ValidationResponse::Error(s) => {
            println!("Entities failed to validate: {s}");
            Ok(())
        }
    }
}

/// Validates (using the lean_ffi backend) that the input `Request` matches the provided `Schema`
pub fn validate_request(schema: &Schema, request: &Request) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    match lean_context.validate_request(schema, request)? {
        ValidationResponse::Ok(()) => {
            println!("Request successfully validated");
            Ok(())
        }
        ValidationResponse::Error(s) => {
            println!("Request failed to validate: {s}");
            Ok(())
        }
    }
}
