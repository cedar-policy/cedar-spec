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

import Cedar.Partial.Authorizer
import Cedar.Thm.Partial.Evaluation

/-!
  This file contains lemmas about `Partial.evaluatePolicy`.
-/

namespace Cedar.Thm.Partial.EvaluatePolicy

open Cedar.Data
open Cedar.Partial (Residual Subsmap Unknown)
open Cedar.Spec (Effect Policies Policy PolicyID)

/--
  if `Partial.evaluatePolicy` produces `some residual` after substitution, it
  must have produced `some` with a residual with the same id and effect before
  substitution

  (or, if the residual after substitution is an evaluation error, then it must
  have produced `some` with a residual with the same id before substitution)
-/
theorem subst_doesn't_increase_residuals {p : Policy} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluatePolicy p req' (entities.subst subsmap) = some r' →
  ∃ r, Partial.evaluatePolicy p req entities = some r ∧ r.id = r'.id ∧ (r.effect = r'.effect ∨ r'.effect = none)
:= by
  unfold Partial.evaluatePolicy
  intro h_req h₁
  split at h₁ <;> simp only [Option.some.injEq] at h₁ <;> subst h₁
  case h_2 v' h₁ h₂ =>
    -- after subst, partial eval of the policy produced a .value other than False
    have h₃ := Partial.Evaluation.Evaluate.subst_preserves_errors_mt (expr := p.toExpr) (entities := entities) wf_r wf_e wf_s h_req (by
      simp only [Except.isOk, Except.toBool]
      split <;> simp only [Bool.false_eq_true]
      · rename_i h₃ ; simp only [h₃] at h₂
    )
    simp [Except.isOk, Except.toBool] at h₃
    split at h₃ <;> simp at h₃
    clear h₃ <;> rename_i pval h₃
    · exists (Residual.residual p.id p.effect pval)
      constructor
      · simp only [h₃]
        split <;> rename_i h <;> simp only [Option.some.injEq, Residual.residual.injEq, true_and]
        <;> simp only [Except.ok.injEq] at h <;> subst h
        case h_1 h₃ _ =>
          -- before subst, partial eval of the policy produced False
          have h₅ := Partial.Evaluation.Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₃
          simp only [h₅, Except.ok.injEq, Partial.Value.value.injEq] at h₂
          exact h₁ h₂.symm
        case h_2 h₃ _ v _ =>
          -- before subst, partial eval of the policy produced a .value other than False
          simp only
      · simp only [Residual.id, Residual.effect, or_false, and_self]
  case h_3 e' h₁ =>
    -- after subst, partial eval of the policy produced an error
    cases h₂ : Partial.evaluate p.toExpr req entities
    case error e =>
      exists (Residual.error p.id)
      constructor
      · split <;> simp at *
      · exact And.intro (rfl) (by left ; rfl)
    case ok pval =>
      exists (Residual.residual p.id p.effect pval)
      constructor
      · split <;> rename_i h₃ <;> simp only [Option.some.injEq, Residual.residual.injEq, true_and]
        <;> simp at h₃ <;> subst h₃
        · -- before subst, partial eval of the policy produced False
          have h₃ := Partial.Evaluation.Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₂
          simp only [h₃] at h₁
        · rfl
      · simp only [Residual.id, Residual.effect, or_true, and_self]

/--
  if `Partial.evaluatePolicy` produces `none` before substitution, then it also
  does after any substitution
-/
theorem subst_preserves_none {p : Policy} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluatePolicy p req entities = none →
  Partial.evaluatePolicy p req' (entities.subst subsmap) = none
:= by
  unfold Partial.evaluatePolicy
  intro h_req h₁
  split at h₁ <;> simp at h₁
  · rename_i h₂
    simp only [Partial.Evaluation.Evaluate.subst_preserves_evaluation_to_value wf_r wf_e wf_s h_req h₂]

/--
  if `Partial.evaluatePolicy` produces an error-residual before substitution,
  then it also does after any substitution
-/
theorem subst_preserves_err {p : Policy} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Subsmap}
  (wf_r : req.WellFormed)
  (wf_e : entities.WellFormed)
  (wf_s : subsmap.WellFormed) :
  req.subst subsmap = some req' →
  Partial.evaluatePolicy p req entities = some (Residual.error pid) →
  Partial.evaluatePolicy p req' (entities.subst subsmap) = some (Residual.error pid)
:= by
  unfold Partial.evaluatePolicy
  intro h_req h₁
  split at h₁ <;> simp at h₁
  subst pid
  rename_i e h₂
  have ⟨e', h₃⟩ := Partial.Evaluation.Evaluate.subst_preserves_errors wf_r wf_e wf_s h_req h₂
  simp only [h₃]
