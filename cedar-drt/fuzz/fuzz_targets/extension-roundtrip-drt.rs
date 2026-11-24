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

#![no_main]
use cedar_drt::logger::initialize_log;
use cedar_drt_inner::{
    extensions::{ExtensionRoundtripInput, run_ext_roundtrip_test},
    fuzz_target,
};
use cedar_lean_ffi::CedarLeanFfi;
use log::debug;

// Check that extension constructors recover generated values from their
// string renderings, and diff test the results
fuzz_target!(|input: ExtensionRoundtripInput| {
    initialize_log();
    let def_impl = CedarLeanFfi::new();
    debug!("Input: {input:?}");
    run_ext_roundtrip_test(&def_impl, &input);
});
