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
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Subst
import Cedar.Thm.Partial.WellFormed

/-! Theorems about reevaluation of `Partial.evaluateUnaryApp` -/

namespace Cedar.Thm.Partial.Evaluation.ReevaluateUnaryApp

open Cedar.Partial (Subsmap)
open Cedar.Spec (UnaryOp)

/--
  If `Partial.evaluateUnaryApp` returns a residual, re-evaluating that residual
  with a substitution is equivalent to substituting first, evaluating the arg,
  and calling `Partial.evaluateUnaryApp` on the substituted/evaluated arg
-/
theorem reeval_eqv_substituting_first (op : UnaryOp) (pval₁ : Partial.Value) (entities : Partial.Entities) (subsmap : Subsmap)
  (wf₁ : pval₁.WellFormed) :
  let re_evaluated := Partial.evaluateUnaryApp op pval₁ >>= λ residual => Partial.evaluateValue (residual.subst subsmap) (entities.subst subsmap)
  let subst_first := Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap) >>= λ pval₁' => Partial.evaluateUnaryApp op pval₁'
  match (re_evaluated, subst_first) with
  | (Except.error _, Except.error _) => true -- don't require that the errors are equal
  | (_, _) => re_evaluated = subst_first
:= by
  simp only [Partial.evaluateUnaryApp]
  split <;> try { trivial } <;> rename_i hₑ h₁
  simp only [Prod.mk.injEq] at h₁ ; replace ⟨h₁, h₁'⟩ := h₁ ; subst h₁ h₁'
  cases h₁ : Partial.evaluateValue (pval₁.subst subsmap) (entities.subst subsmap)
  case error e =>
    exfalso
    simp only [h₁, Except.bind_err, Except.error.injEq, imp_false, forall_apply_eq_imp_iff] at hₑ
    cases pval₁ <;> simp only [bind_assoc, Except.bind_ok] at hₑ
    case value v₁ =>
      simp [Subst.subst_concrete_value, Partial.evaluateValue] at h₁
    case residual r₁ =>
      simp only [Partial.Value.subst, Partial.ResidualExpr.subst] at h₁ hₑ
      simp only [Partial.evaluateValue, Partial.evaluateResidual] at h₁ hₑ
      simp only [h₁, Except.bind_err, Except.error.injEq, forall_eq'] at hₑ
  case ok pval₁' =>
    cases pval₁
    case value v₁ =>
      simp only [Subst.subst_concrete_value, Partial.evaluateValue,
        bind_assoc, Except.bind_ok, Except.ok.injEq, imp_false] at *
      subst pval₁'
      simp only
    case residual r₁ =>
      simp [Partial.Value.subst, Partial.ResidualExpr.subst, Partial.evaluateValue, Partial.evaluateResidual] at *
      cases hr₁' : Partial.evaluateValue (r₁.subst subsmap) (entities.subst subsmap)
      case error e =>
        simp only [hr₁', Except.bind_err, Except.error.injEq, forall_apply_eq_imp_iff, imp_false,
          forall_eq'] at hₑ
      case ok r₁' =>
        simp only [hr₁', Except.ok.injEq] at h₁ ; subst r₁'
        simp only [Except.bind_ok, Partial.evaluateUnaryApp]
