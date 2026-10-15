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

//! Tests schema-link order independence on schemas parsed from arbitrary JSON.

#![no_main]
use cedar_drt_inner::{
    arbitrary_json::ArbitraryJson, fuzz_target, props::schema_link_is_order_independent,
};

fuzz_target!(|input: Vec<ArbitraryJson>| {
    schema_link_is_order_independent(input.into_iter().map(Into::into).collect());
});
