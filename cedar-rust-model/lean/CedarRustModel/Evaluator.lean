/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

module

public import CedarRustModel.Convert
public import Cedar.Spec
import CedarRustModel.Lemmas.Evaluate

/-!
The model's evaluator (`cedar-rust-model/src/evaluator.rs`, extracted to Lean
by Aeneas) agrees with `Cedar.Spec.evaluate`.
-/

namespace CedarRustModel

open Aeneas.Std Cedar.Data Cedar.Spec
open cedar_rust_model

/-- The model's evaluator does not panic and agrees with `Cedar.Spec.evaluate`. -/
public theorem evaluate_correct
    (x : expr.Expr) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.evaluate x req es = .ok r ∧
      Result.toSpec Value.toSpec r =
        Cedar.Spec.evaluate (Expr.toSpec x) (Request.toSpec req) (Entities.toSpec es) :=
  evaluate_ok x req es

end CedarRustModel
