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

//! Pseudorandom generation of Cedar policies, hierarchies, and requests

#![warn(missing_docs, missing_debug_implementations, rust_2018_idioms)]
#![forbid(unsafe_code)]

/// This module contains code for generating ABAC policies, hierarchies, and
/// requests -- that is, fully general, containing attributes
pub mod abac;

/// This module contains deterministic versions of `HashMap` and `HashSet`
pub mod collections;

/// This module contains error types used by the crate
pub mod err;

/// This module contains functionality for generating `Expr`s
pub mod expr;

/// This module contains helper macros for generators
#[macro_use]
pub mod gen;

/// This module contains the `Hierarchy` data structure
pub mod hierarchy;

/// This module contains the `GeneratedPolicy` and `GeneratedLinkedPolicy` data
/// structures
pub mod policy;

/// This module contains code for generating RBAC policies, hierarchies, and
/// requests -- that is, without attributes
pub mod rbac;

/// This module contains the `Request` data structure
pub mod request;

/// This module contains the `Schema` data structure and methods for generating
/// both schemas and hierarchies/policies that conform to a schema
pub mod schema;

/// This module contains helper functions for calculating size_hint()
pub mod size_hint_utils;

/// This module contains various generator settings
pub mod settings;

/// This module contains generator functions for sampling Cedar schema grammars
pub mod schema_grammar;

/// This module contains generator functions for sampling Cedar policy grammars
pub mod policy_grammar;
