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

//! Return types for the `typecheckPolicyTyped` Lean entry point (issue #840).
//!
//! The Lean `TypedExpr` is carried as an uninterpreted `serde_json::Value`.
//! That is deliberate: the Rust side renders its own typed AST into the same
//! tagged shape independently, and the two trees are then compared. Decoding
//! the Lean tree into a Rust mirror of the Rust AST would let the decoder
//! silently absorb differences that the comparison exists to surface.

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// One (policy, environment) typechecking outcome from the Lean validator.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct LeanTypedExprEnvResult {
    /// Principal entity type, as rendered by Lean's `ToString`
    pub principal: String,
    /// Action EUID, as rendered by Lean's `ToString`
    pub action: String,
    /// Resource entity type, as rendered by Lean's `ToString`
    pub resource: String,
    /// Whether `typecheckPolicy` returned `.ok`
    pub ok: bool,
    /// The `TypedExpr`, present exactly when `ok` is true
    #[serde(rename = "typedExpr", default)]
    pub typed_expr: Option<Value>,
}

impl LeanTypedExprEnvResult {
    /// Key identifying the request environment. Both implementations produce
    /// this independently, so results are matched by key rather than by
    /// position in a list.
    pub fn env_key(&self) -> (String, String, String) {
        (
            self.principal.clone(),
            self.action.clone(),
            self.resource.clone(),
        )
    }
}

/// All per-environment outcomes for one policy.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct LeanTypedExprPolicyResult {
    /// Policy id, as rendered by Lean's `ToString`
    #[serde(rename = "policyId")]
    pub policy_id: String,
    /// One entry per schema-defined environment
    pub envs: Vec<LeanTypedExprEnvResult>,
}
