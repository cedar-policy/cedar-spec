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
