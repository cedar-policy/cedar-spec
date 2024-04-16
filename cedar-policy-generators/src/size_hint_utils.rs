/*
 * Copyright Cedar Contributors
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

/// get a size hint for a call to ratio::<T>() with these parameters
pub fn size_hint_for_ratio<T: arbitrary::unstructured::Int>(
    _a: T,
    _b: T,
) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for ratio()
    size_hint_for_nonzero_range::<T>()
}

/// get a size hint for a call to int_in_range::<T>() with the parameter a..=b
pub fn size_hint_for_range<T: arbitrary::unstructured::Int>(a: T, b: T) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for int_in_range()
    if a >= b {
        (0, Some(0))
    } else {
        size_hint_for_nonzero_range::<T>()
    }
}

/// get a size hint for a call to int_in_range::<T>(a..=b) where we assume a < b
/// given this assumption, a and b don't matter for the calculation
pub fn size_hint_for_nonzero_range<T: arbitrary::unstructured::Int>() -> (usize, Option<usize>) {
    (1, Some(std::mem::size_of::<T>()))
}

/// get a size hint for a call to choose(). More precise estimate available if
/// you have an upper bound on how many things you're choosing from
pub fn size_hint_for_choose(max_num_choices: Option<usize>) -> (usize, Option<usize>) {
    // the following hint is based on looking at the source for choose()
    match max_num_choices {
        Some(max_num_choices) => size_hint_for_range::<usize>(0, max_num_choices - 1),
        None => (1, None), // hard to know upper bound here
    }
}
