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

import Cedar.Partial.Evaluator
import Cedar.Thm.Partial.Evaluation.EvaluateHasAttr
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.ReevaluateHasAttr

open Cedar.Partial (Subsmap)
open Cedar.Spec (Attr)

/--
  If `Partial.evaluateHasAttr` returns a residual, re-evaluating that residual with a
  substitution is equivalent to substituting first, evaluating the arg, and calling
  `Partial.evaluateHasAttr` on the substituted/evaluated arg
-/
theorem reeval_eqv_substituting_first (pval₁ : Partial.Value) (attr : Attr) {entities : Partial.Entities} (subsmap : Subsmap)
  (wf_e : entities.WellFormed)
  (wf₁ : pval₁.WellFormed) :
  (Partial.evaluateHasAttr pval₁ attr entities >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)) =
  (Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap) >>= λ pval' => Partial.evaluateHasAttr pval' attr (entities.subst subsmap))
:= by
  unfold Partial.evaluateHasAttr
  cases pval₁ <;> simp [Partial.Value.WellFormed] at wf₁
  case value v₁ =>
    simp [Subst.subst_concrete_value, Partial.evaluateValue]
    rw [← EvaluateHasAttr.hasAttr_subst_const subsmap wf_e]
  case residual r₁ =>
    simp [Partial.Value.subst, Partial.ResidualExpr.subst]
    simp [Partial.evaluateValue, Partial.evaluateResidual]
    cases Partial.evaluateValue (r₁.subst subsmap) (entities.subst subsmap)
    case error e => simp only [Except.bind_err, implies_true]
    case ok r₁' => simp only [Partial.evaluateHasAttr, Except.bind_ok, implies_true]
