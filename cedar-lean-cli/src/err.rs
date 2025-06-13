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
use cedar_policy::entities_errors::EntitiesError;
use std::path::PathBuf;
use thiserror::Error;

/// The type of struct was expected to be contained within the file
#[derive(Clone, Debug)]
pub enum ContentType {
    Context,
    Entities,
    Expression,
    Policy,
    PolicySet,
    Request,
    Schema,
    SchemaJSON,
}

/// The element of a RequestEnvironment that was involved in the error
#[allow(clippy::enum_variant_names)]
#[derive(Clone, Debug)]
pub enum EntityType {
    PrincipalTypeName,
    ActionName,
    ResourceTypeName,
}

/// The element of a Request that was involved in the error
#[derive(Clone, Debug)]
pub enum RequestElement {
    Principal,
    Action,
    Resource,
    Context,
}

#[derive(Error, Debug)]
pub enum ExecError {
    #[error("Error reading {content_type:?} from {file_name} : {error}")]
    FileReadError {
        content_type: ContentType,
        file_name: PathBuf,
        error: Box<dyn std::error::Error>,
    },
    #[error("Error parsing {content_type:?} from {file_name} : {error}")]
    ParseError {
        content_type: ContentType,
        file_name: PathBuf,
        error: Box<dyn std::error::Error>,
    },
    #[error("Error while attempting to use id annotations as policy ids in while parsing {content_type:?} from {file_name}: {error}")]
    RenameIdError {
        content_type: ContentType,
        file_name: PathBuf,
        error: miette::ErrReport,
    },
    #[error("Error parsing {content_type:?} from {file_name} : invalid JSON format")]
    ParseJsonError {
        content_type: ContentType,
        file_name: PathBuf,
    },
    #[error("Error creating {entity_type:?} from {input_str} : {error}")]
    EntityTypeError {
        entity_type: EntityType,
        input_str: String,
        error: Box<dyn std::error::Error>,
    },
    #[error("Error Creating {element:?} from {input_str} : {error}")]
    RequestError {
        element: RequestElement,
        input_str: String,
        error: Box<dyn std::error::Error>,
    },
    #[error("Error converting Policy to a PolicySet : {error}")]
    PolicyIntoPolicySetError { error: Box<dyn std::error::Error> },
    #[error("Error during analysis : {error}")]
    InternalAnalysisError { error: Box<dyn std::error::Error> },
    #[error("Error Creating Request : {error}")]
    RequestValidationError { error: Box<dyn std::error::Error> },
    #[error("Could not fetch actions from Schema")]
    ActionsFromSchemaError(#[from] EntitiesError),
    #[error("{principal_type} cannot {action_name} on {resource_type} in the provided Schema")]
    RequestEnvArgsIncompatible {
        principal_type: String,
        action_name: String,
        resource_type: String,
    },
    #[error(transparent)]
    LeanFFIError(#[from] cedar_lean_ffi::FfiError),
}
