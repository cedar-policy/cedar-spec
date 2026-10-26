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

//! Requests (`Cedar/Spec/Request.lean`).

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::value::*;

#[cfg_attr(feature = "verus", verus_verify)]
pub struct Request {
    pub principal: EntityUID,
    pub action: EntityUID,
    pub resource: EntityUID,
    pub context: Attrs,
}
