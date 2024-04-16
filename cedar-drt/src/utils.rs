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

use cedar_policy_core::ast::Expr;
use cedar_policy_core::est;
use serde::Serialize;
use serde::Serializer;

pub fn expr_to_est<S: Serializer>(e: &Expr, s: S) -> Result<S::Ok, S::Error> {
    let est: est::Expr = e.clone().into();
    est.serialize(s)
}
