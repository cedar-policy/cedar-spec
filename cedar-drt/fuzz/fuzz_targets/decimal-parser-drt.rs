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

use cedar_drt::LeanDefinitionalEngine;
use cedar_drt_inner::{fuzz_target, run_ext_constructor_test};

// Type-directed fuzzing of expression evaluation.
fuzz_target!(|datetime: String| {
    let def_impl = LeanDefinitionalEngine::new();
    run_ext_constructor_test(&def_impl, "decimal".parse().unwrap(), datetime);
});
