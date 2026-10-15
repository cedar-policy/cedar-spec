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

//! Differential testing of entity and request validation against partial
//! schemas ([RFC 116](https://github.com/cedar-policy/rfcs/pull/116)).

#![no_main]
use cedar_drt::logger::{TOTAL_MSG, initialize_log};
use cedar_drt_inner::{
    fuzz_target,
    partial_schema::{PartialSchemaInput, check_agreement},
};

use cedar_lean_ffi::CedarLeanFfi;
use cedar_testing::cedar_test_impl::time_function;
use log::info;

fuzz_target!(|input: PartialSchemaInput| {
    initialize_log();
    let ffi = CedarLeanFfi::new();
    let (_, total_dur) = time_function(|| check_agreement(&ffi, &input));
    info!("{}{}", TOTAL_MSG, total_dur.as_nanos());
});
