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

//! Entity stores (`Cedar/Spec/Entities.lean`).

#![allow(clippy::all)]

#[cfg(feature = "verus")]
use vstd::prelude::*;

use super::value::*;

#[cfg_attr(feature = "verus", verus_verify)]
pub struct EntityData {
    pub attrs: Attrs,
    pub ancestors: List<EntityUID>,
    pub tags: Attrs,
}

/// Well-formed entity stores are in canonical form.
pub type Entities = List<(EntityUID, EntityData)>;

#[cfg_attr(feature = "verus", verus_verify(dual_spec, open))]
#[cfg_attr(feature = "verus", verus_spec(returns entities_find(es, u)))]
pub fn entities_find<'a>(es: &'a Entities, u: &EntityUID) -> Option<&'a EntityData> {
    decreases!(es);
    match es {
        List::Nil => None,
        List::Cons((v, d), rest) => {
            if uid_eq(v, u) {
                Some(d)
            } else {
                entities_find(rest, u)
            }
        }
    }
}
