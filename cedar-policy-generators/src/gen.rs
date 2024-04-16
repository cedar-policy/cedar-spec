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

/// Helper macro used by other macros here
#[macro_export]
// the inner language [weight => value]+
// desugar it into a series of if else statements
macro_rules! gen_inner {
    ($i:ident, [$w:expr => $v:expr]) => {
        $v
    };
    ($i:ident, [$w1:expr => $v1:expr] [$w2:expr => $v2:expr] $([$ws:expr => $vs:expr])*) => {
        if $i < $w1 {
            $v1
        } else {
            gen_inner!($i, [$w1+$w2 => $v2] $([$ws => $vs])*)
        }
    };
}

/// Helper macro used by other macros here
#[macro_export]
// accumulate the weight of the inner language
macro_rules! accum {
    () => {
        0
    };
    ([$w1:expr => $v1:expr] $([$ws:expr => $vs:expr])*) => {
        $w1 + accum!($([$ws => $vs])*)
    }
}

/// the top level language `u, w => v,+` where `u` is a `Unstructured`, `w` is the weight, and `v` is the value to generate
/// it desugars into something like
/// ```ignore
///      let x = u.int_in_range::<u8>(0..(w1+w2+...+wn-1))?;
///      if x < w1 { v1 } else {
///          if x < w1 + w2 { v2 } else {
///              if x < w1 + w2 + w3 { v3 } else {
///                  ... else { vn }
///              }
///          }
///      }
/// ```
#[macro_export]
macro_rules! gen {
    ($u:expr, $($ws:expr => $vs:expr),+) => {
        {
            let x = $u.int_in_range::<u8>(0..=(($crate::accum!($([$ws => $vs])+)-1)))?;
            $crate::gen_inner!(x, $([$ws => $vs])+)
        }
    };
}

/// a short circuit to uniformly generate values
/// it desugars to the language above where all weights are 1
#[macro_export]
macro_rules! uniform {
    ($u:expr, $($es:expr),+) => {
        {
            let x = $u.int_in_range::<u8>(0..=(($crate::accum!($([1 => $es])+)-1)))?;
            $crate::gen_inner!(x, $([1 => $es])+)
        }
    };
}
