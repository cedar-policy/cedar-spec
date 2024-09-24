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
import Cedar.Spec.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.LT
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation.EvaluateValue
import Cedar.Thm.Partial.Evaluation.Props
import Cedar.Thm.Partial.Evaluation.ReevaluatePartialGetAttr
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

namespace Cedar.Thm.Partial.Evaluation.ReevaluateGetAttr

open Cedar.Data
open Cedar.Partial (Subsmap)
open Cedar.Spec (Attr EntityUID Error Expr Prim Result)

/--
  If `Partial.evaluateGetAttr` returns a residual, re-evaluating that residual with a
  substitution is equivalent to substituting first, evaluating the arg, and calling
  `Partial.evaluateGetAttr` on the substituted/evaluated arg

  As an inductive hypothesis, this takes a proof of
  `ReevaluateValue.reeval_eqv_substituting_first` for any `pval` contained in `entities`.
-/
theorem reeval_eqv_substituting_first (pval₁ : Partial.Value) (attr : Attr) {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed)
  (wf₁ : pval₁.WellFormed)
  (ih : ∀ v pv pv',
    v.WellFormed →
    Partial.getAttr v attr entities = .ok pv →
    Partial.evaluateValue pv entities = .ok pv' →
    Partial.evaluateValue (pv'.subst subsmap) (entities.subst subsmap) =
    Partial.evaluateValue (pv.subst subsmap) (entities.subst subsmap)
  ) :
  let re_evaluated := (Partial.evaluateGetAttr pval₁ attr entities >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap))
  let subst_first := (Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap) >>= λ pval₁' => Partial.evaluateGetAttr pval₁' attr (entities.subst subsmap))
  match (re_evaluated, subst_first) with
  | (Except.error _, Except.error _) => true -- don't require that the errors are equal
  | (_, _) => re_evaluated = subst_first
:= by
  unfold Partial.evaluateGetAttr
  cases pval₁ <;> simp [Partial.Value.WellFormed] at wf₁
  case value v₁ =>
    simp [Subst.subst_concrete_value, Partial.evaluateValue]
    rw [← reeval_eqv_substituting_first_partialGetAttr v₁ attr wf₁ wf_e wf_s]
    cases h₁ : Partial.getAttr v₁ attr entities <;> simp
    case ok pval =>
      have wf_pv : pval.WellFormed := EvaluateGetAttr.getAttr_wf wf₁ wf_e _ h₁
      specialize ih v₁ pval
      cases h₂ : Partial.evaluateValue pval entities
      <;> simp only [Except.bind_ok, Except.bind_err]
      case error e =>
        have ⟨e', h₃⟩ := EvaluateValue.subst_preserves_errors wf_pv wf_e wf_s h₂
        simp only [h₃]
      case ok pval' =>
        specialize ih pval' wf₁ h₁ h₂
        simp [ih]
        split <;> trivial
  case residual r₁ =>
    simp only [Except.bind_ok, Partial.evaluateValue, Partial.evaluateResidual, bind_assoc,
      Partial.Value.subst]
    cases h₁ : Partial.evaluateValue (r₁.subst subsmap) (entities.subst subsmap)
    <;> simp only [Partial.ResidualExpr.subst, Partial.Value.subst, Partial.evaluateValue,
      Partial.evaluateResidual, h₁, Except.bind_ok, Except.bind_err]
    case ok pv₂ =>
      cases pv₂ <;> simp [Partial.evaluateGetAttr]
      case value => split <;> trivial


end Cedar.Thm.Partial.Evaluation.ReevaluateGetAttr
