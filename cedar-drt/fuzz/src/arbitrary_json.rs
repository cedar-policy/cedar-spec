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

use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use serde_json::{Map, Number, Value};

const MAX_DEPTH: usize = 16;
const MAX_WIDTH: u32 = 8;

#[derive(Debug, Clone)]
pub struct ArbitraryJson(Value);

impl<'a> Arbitrary<'a> for ArbitraryJson {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        Self::arbitrary_with_depth(u, 0)
    }
}

impl ArbitraryJson {
    fn arbitrary_with_depth(u: &mut Unstructured<'_>, depth: usize) -> arbitrary::Result<Self> {
        let max_variant = if depth < MAX_DEPTH { 5 } else { 3 };
        let value = match u.int_in_range(0..=max_variant)? {
            0 => Value::Null,
            1 => Value::Bool(u.arbitrary()?),
            2 => Value::Number(match u.int_in_range(0..=2)? {
                0 => Number::from(u.arbitrary::<i64>()?),
                1 => Number::from(u.arbitrary::<u64>()?),
                _ => Number::from_f64(u.arbitrary()?).unwrap_or_else(|| Number::from(0)),
            }),
            3 => Value::String(u.arbitrary()?),
            4 => {
                let mut values = Vec::new();
                u.arbitrary_loop(Some(0), Some(MAX_WIDTH), |u| {
                    values.push(Self::arbitrary_with_depth(u, depth + 1)?.into());
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Value::Array(values)
            }
            _ => {
                let mut entries = Map::new();
                u.arbitrary_loop(Some(0), Some(MAX_WIDTH), |u| {
                    entries.insert(
                        u.arbitrary()?,
                        Self::arbitrary_with_depth(u, depth + 1)?.into(),
                    );
                    Ok(std::ops::ControlFlow::Continue(()))
                })?;
                Value::Object(entries)
            }
        };
        Ok(Self(value))
    }
}

impl From<ArbitraryJson> for Value {
    fn from(value: ArbitraryJson) -> Self {
        value.0
    }
}
