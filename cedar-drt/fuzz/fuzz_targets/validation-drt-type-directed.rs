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
use cedar_drt_inner::{fuzz_target, validation_drt};
#[cfg(feature = "prt")]
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};

// Type-directed fuzzing of (strict) validation.
fuzz_target!(|input: validation_drt::FuzzTargetInput<true>| validation_drt::fuzz_target(input));
