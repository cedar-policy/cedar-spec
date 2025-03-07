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

use cedar_drt_inner::fuzz_target;
use cedar_policy_core::ast::{Pattern, PatternElem};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Result, Unstructured};
use regex::{escape, Regex};
use serde::{Serialize, Serializer};
use serde::ser::SerializeStruct;

/// Input expected by this fuzz target:
/// A pattern and a string that matches it
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated pattern
    pub pattern: Vec<PatternElem>,
    /// generated string
    pub string: String,
}

impl Serialize for FuzzTargetInput {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut state = serializer.serialize_struct("FuzzTargetInput", 2)?;

        let pattern: Vec<String> = self.pattern.iter().map(|e| match e {
            PatternElem::Char(c) => c.to_string(),
            PatternElem::Wildcard => "*".to_string(),
        }).collect();

        state.serialize_field("pattern", &pattern)?;
        state.serialize_field("string", &self.string)?;
        state.end()
    }
}

/// A wrapper struct for valid characters:
/// A character `c` is valid if it satisfies two criteria:
/// 1. c as u32 <= 0xffff (i.e., c is in the Basic Multilingual Plane.)
/// 2. char::from_u32(c as u32).is_some() (i.e., c is not a surrogate code point.)
#[derive(Debug, Clone)]
struct ValidChar(char);

impl From<ValidChar> for char {
    fn from(vc: ValidChar) -> Self {
        vc.0
    }
}

impl Arbitrary<'_> for ValidChar {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        // High Surrogate: U+D800–U+DBFF
        // Low Surrogate: U+DC00–U+DFFF
        // Pick a value beween 0 and 0x10000 minus the number of surrogate values
        let mut v: u32 = u.int_in_range(0..=(0x10000 - 8 * 0x100))?;
        if (0xD800..=0xDFFF).contains(&v) {
            // shift v to range 0xE000 to 0xFFFF
            v = 0xE000 + v - 0xD800;
        }
        Ok(Self(std::char::from_u32(v).expect("valid char!")))
    }

    // Had to comment it out because this function seems not accessible to this module
    //fn size_hint(depth: usize) -> (usize, Option<usize>) {
    //    super::size_hint_for_nonzero_range(depth)
    //}
}

// Like `PatternElem` but the character contained in it is valid.
// We use this struct to produce an arbitrary `PatternElem`.
#[derive(arbitrary::Arbitrary, Debug, Clone)]
enum PatternElemWithValidChar {
    Char(ValidChar),
    Wildcard,
}

impl From<PatternElemWithValidChar> for PatternElem {
    fn from(pevc: PatternElemWithValidChar) -> Self {
        match pevc {
            PatternElemWithValidChar::Char(vc) => Self::Char(vc.0),
            PatternElemWithValidChar::Wildcard => Self::Wildcard,
        }
    }
}

/// Naively generate a string that matches a pattern by expanding the wildcard star into a sequence of chars.
fn expand_pattern<'a, 'b>(
    pattern: impl IntoIterator<Item = &'b PatternElem>,
    u: &mut Unstructured<'a>,
) -> Result<String> {
    let mut s = String::new();
    for pe in pattern {
        match pe {
            PatternElem::Char(c) => {
                // Keep the char for a 3/4 chance, otherwise either drop it or replace with an arbitrary char.
                if u.ratio(3, 4)? {
                    s.push(*c);
                } else if u.ratio(1, 2)? {
                    s.push(<ValidChar as Arbitrary>::arbitrary(u)?.into())
                }
            }
            PatternElem::Wildcard => {
                let sz = u.arbitrary_len::<ValidChar>()?;
                for _i in 0..sz {
                    s.push(<ValidChar as Arbitrary>::arbitrary(u)?.0);
                }
            }
        }
    }
    Ok(s)
}

impl Arbitrary<'_> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'_>) -> Result<Self> {
        let pattern = <Vec<PatternElemWithValidChar> as Arbitrary>::arbitrary(u)?
            .into_iter()
            .map(|pe| pe.into())
            .collect();
        let s = expand_pattern(&pattern, u)?;
        Ok(Self { pattern, string: s })
    }
    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        // A real best-effort estimate
        <Vec<PatternElemWithValidChar> as Arbitrary>::size_hint(depth)
    }
}

fn wildcard_match_regex<'a>(
    text: &str,
    pattern: impl IntoIterator<Item = &'a PatternElem>,
) -> bool {
    let mut regex_pat_inner = String::new();
    for pe in pattern {
        match pe {
            PatternElem::Char(c) => {
                regex_pat_inner.push_str(&escape(&c.to_string()));
            }
            PatternElem::Wildcard => {
                // Use flag `s` because there could be newlines in the text.
                regex_pat_inner.push_str("(?s:.)*");
            }
        }
    }
    let regex_pat = format!("^{}$", regex_pat_inner);
    Regex::new(&regex_pat)
        .expect("Should be a correct regex pattern!")
        .is_match(text)
}

fuzz_target!(|input: FuzzTargetInput| {
    // Ensure wildcard matching is equivalent to the regex version
    let regex_result = wildcard_match_regex(&input.string, &input.pattern);
    let rust_result = Pattern::from(input.pattern).wildcard_match(&input.string);
    assert_eq!(
        regex_result, rust_result,
        "\nregex result: {};rust result:{}.\n",
        regex_result, rust_result
    );
});
