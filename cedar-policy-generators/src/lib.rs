//! Pseudorandom generation of Cedar policies, hierarchies, and requests

#![warn(missing_docs, missing_debug_implementations, rust_2018_idioms)]
#![forbid(unsafe_code)]

/// This module contains deterministic versions of `HashMap` and `HashSet`
pub mod collections;

/// This module contains error types used by the crate
pub mod err;

/// This module contains code for generating a Hierarchy
pub mod hierarchy;

/// This module contains helper functions for calculating size_hint()
pub mod size_hint_utils;
