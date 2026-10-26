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

//! A simplified, executable model of Cedar linking production to the Lean spec.
//! Verus (`dual_spec`) turns each function into a spec function that production
//! is proved against; Aeneas translates it to Lean, where it is proved equal to
//! `Cedar/Spec`. So it uses only Rust both tools support: cons-lists, `Box`,
//! structural recursion. Production includes it as `verification::model`.

#![allow(clippy::all)]

#[cfg(feature = "verus")]
#[allow(unused_imports)]
use vstd::prelude::*;

/// Termination measure, stated in the body because `dual_spec` copies the body
/// (but not `verus_spec`) into the spec function. Expands to nothing outside Verus.
macro_rules! decreases {
    ($($e:expr),+ $(,)?) => {
        #[cfg(verus_keep_ghost)]
        vstd::prelude::decreases(($($e,)+));
    };
}

pub mod authorizer;
pub mod entities;
pub mod evaluator;
pub mod expr;
pub mod ext;
pub mod policy;
pub mod request;
pub mod value;
