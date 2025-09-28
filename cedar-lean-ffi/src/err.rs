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
use thiserror::Error;

use crate::lean_object::LeanObjectError;

#[derive(Error, Debug)]
pub enum FfiError {
    #[error("Error deserializing Lean backend output : {0}")]
    LeanDeserializationError(String),
    #[error("Error occurred in Lean backend : {0}")]
    LeanBackendError(String),
    #[error(transparent)]
    LeanObjectError(#[from] LeanObjectError),
}
