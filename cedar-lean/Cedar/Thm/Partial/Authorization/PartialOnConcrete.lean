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

import Cedar.Spec.Authorizer
import Cedar.Spec.Entities
import Cedar.Spec.Request
import Cedar.Partial.Authorizer
import Cedar.Partial.Response
import Cedar.Thm.Authorization.Evaluator
import Cedar.Thm.Partial.Evaluation
import Cedar.Thm.Partial.Evaluation.Basic

/-!
  This file contains lemmas about the behavior of partial authorization on
  concrete inputs.

  The toplevel theorems (proved using these lemmas) are in
  Thm/Partial/Authorization.lean, not this file.
-/

namespace Cedar.Thm.Partial.Authorization.PartialOnConcrete

open Cedar.Data
open Cedar.Partial (Residual)
open Cedar.Spec (Effect Policies PolicyID)

/--
  on concrete inputs, Partial.Response.mayBeSatisfied is empty iff
  Spec.satisfiedPolicies is empty
-/
theorem mayBeSatisfied_empty_iff_no_satisfied {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect}
  (wf : req.WellFormed) :
  ((Partial.isAuthorized req entities policies).mayBeSatisfied eff).isEmpty ↔
  (Spec.satisfiedPolicies eff policies req entities).isEmpty
:= by
  unfold Partial.Response.mayBeSatisfied Spec.satisfiedPolicies
  repeat rw [← Set.make_empty]
  repeat rw [List.filterMap_empty_iff_all_none]
  simp only [Spec.satisfiedWithEffect, Spec.satisfied, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, ite_eq_right_iff, and_imp]
  constructor
  case mp =>
    intro h₁ policy h₂ h₃ h₄
    subst h₃
    simp only [Partial.isAuthorized, List.mem_filterMap, forall_exists_index, and_imp] at h₁
    simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf, Except.map] at h₁
    rw [forall_comm] at h₁
    specialize h₁ policy
    simp only [Residual.mayBeSatisfied] at h₁
    cases h₃ : Spec.evaluate policy.toExpr req entities <;> simp only [h₃, Except.ok.injEq] at *
    case ok v =>
      subst h₄
      simp only [Option.some.injEq, forall_apply_eq_imp_iff] at h₁
      specialize h₁ h₂
      split at h₁ <;> simp only [Spec.Value.asPartialExpr, Residual.residual.injEq,
        Partial.Expr.lit.injEq, Spec.Prim.bool.injEq, and_false, imp_self, forall_const, and_imp,
        forall_apply_eq_imp_iff₂, forall_apply_eq_imp_iff, forall_eq'] at *
      case h_2 pid eff cond h₄ h₅ =>
        replace ⟨h₅, h₅', h₅''⟩ := h₅
        subst pid eff cond
        simp only [↓reduceIte] at h₁
  case mpr =>
    intro h₁ r h₂
    simp [Partial.isAuthorized, List.mem_filterMap] at h₂
    replace ⟨policy, h₂, h₃⟩ := h₂
    simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf, Except.map] at h₃
    simp only [Residual.mayBeSatisfied]
    split <;> simp only [ite_eq_right_iff]
    case h_2 r pid eff' cond h₄ =>
      intro h₅ ; subst h₅
      split at h₃
      <;> simp only [Option.some.injEq, Residual.residual.injEq] at h₃
      <;> replace ⟨h₃, h₅, h₆⟩ := h₃
      <;> subst h₃ h₆
      <;> specialize h₁ policy h₂ h₅
      <;> apply h₁ <;> clear h₁
      case h_3 x h₁ => split at h₁ <;> simp at h₁
      case h_2 v h₁ h₃ =>
        split at h₃ <;> simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₃
        case h_2 v' h₅ =>
          subst h₃
          simp only [h₅, Except.ok.injEq]
          have h₃ := policy_produces_bool_or_error policy req entities
          simp only [h₅] at h₃
          split at h₃ <;> rename_i h₆
          · rename_i b
            cases b
            case true => simp at h₆ ; assumption
            case false => simp at h₆ ; exfalso ; apply h₁ ; assumption
          · simp at h₆
          · contradiction

/--
  corollary of the above
-/
theorem permits_empty_iff_no_satisfied_permits {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).permits.isEmpty ↔
  (Spec.satisfiedPolicies .permit policies req entities).isEmpty
:= by
  unfold Partial.Response.permits
  apply mayBeSatisfied_empty_iff_no_satisfied (eff := .permit) wf

/--
  corollary of the above
-/
theorem forbids_empty_iff_no_satisfied_forbids {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).forbids.isEmpty ↔
  (Spec.satisfiedPolicies .forbid policies req entities).isEmpty
:= by
  unfold Partial.Response.forbids
  apply mayBeSatisfied_empty_iff_no_satisfied (eff := .forbid) wf

/--
  another corollary, for the nonempty case
-/
theorem mayBeSatisfied_nonempty_iff_satisfied_nonempty {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect}
  (wf : req.WellFormed) :
  ((Partial.isAuthorized req entities policies).mayBeSatisfied eff).isEmpty = false ↔
  (Spec.satisfiedPolicies eff policies req entities).isEmpty = false
:= by
  constructor
  case mp =>
    intro h₁
    apply eq_false_of_ne_true
    replace h₁ := ne_true_of_eq_false h₁
    rw [mayBeSatisfied_empty_iff_no_satisfied wf] at h₁
    exact h₁
  case mpr =>
    intro h₁
    apply eq_false_of_ne_true
    replace h₁ := ne_true_of_eq_false h₁
    rw [← mayBeSatisfied_empty_iff_no_satisfied wf] at h₁
    exact h₁

/--
  corollary of the above
-/
theorem permits_nonempty_iff_satisfied_permits_nonempty {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).permits.isEmpty = false ↔
  (Spec.satisfiedPolicies .permit policies req entities).isEmpty = false
:= by
  unfold Partial.Response.permits
  apply mayBeSatisfied_nonempty_iff_satisfied_nonempty (eff := .permit) wf

/--
  corollary of the above
-/
theorem forbids_nonempty_iff_satisfied_forbids_nonempty {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).forbids.isEmpty = false ↔
  (Spec.satisfiedPolicies .forbid policies req entities).isEmpty = false
:= by
  unfold Partial.Response.forbids
  apply mayBeSatisfied_nonempty_iff_satisfied_nonempty (eff := .forbid) wf

/--
  on concrete inputs, the `cond` of all residuals is literal `true`
-/
theorem all_residuals_are_true_residuals {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {id : PolicyID} {eff : Effect} {cond : Partial.Expr}
  (wf : req.WellFormed) :
  (Residual.residual id eff cond) ∈ (Partial.isAuthorized req entities policies).residuals →
  cond = .lit (.bool true)
:= by
  intro h₁
  unfold Partial.isAuthorized at h₁
  simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf, Except.map,
    List.mem_filterMap] at h₁
  replace ⟨policy, _, h₁⟩ := h₁
  have h₂ := policy_produces_bool_or_error (p := policy) (request := req) (entities := entities)
  split at h₂ <;> simp only at h₂
  · rename_i b h₃
    simp only [h₃] at h₁
    split at h₁ <;> simp only [Option.some.injEq, Residual.residual.injEq] at h₁
    case h_2 v h₄ h₅ =>
      replace ⟨h₁, _, h₆⟩ := h₁
      subst h₁ h₆
      simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₅
      subst h₅
      simp only [Spec.Value.asPartialExpr, Partial.Expr.lit.injEq, Spec.Prim.bool.injEq]
      match b with
      | true => rfl
      | false => simp only [forall_const] at h₄
    case h_3 cond' h₄ =>
      replace ⟨h₁, _, h₅⟩ := h₁
      subst h₁ h₅
      simp only [Except.ok.injEq] at h₄
  · rename_i e h₃ ; simp [h₃] at h₁

/--
  on concrete inputs, `mustBeSatisfied` and `mayBeSatisfied` are the same
-/
theorem mustBeSatisfied_eq_mayBeSatisfied {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).mustBeSatisfied eff =
  (Partial.isAuthorized req entities policies).mayBeSatisfied eff
:= by
  simp only [Partial.Response.mustBeSatisfied, Partial.Response.mayBeSatisfied]
  rw [Set.make_make_eqv]
  unfold List.Equiv
  simp only [Residual.mustBeSatisfied, Residual.mayBeSatisfied, List.subset_def,
    List.mem_filterMap, forall_exists_index, and_imp]
  constructor <;> intro pid r h₁ h₂
  case left =>
    exists r
    apply And.intro h₁
    split at h₂ <;> simp only [ite_some_none_eq_some] at h₂
    case h_1 r pid' eff' =>
      replace ⟨h₂, h₂'⟩ := h₂
      subst pid' eff'
      simp only [reduceIte]
  case right =>
    exists r
    apply And.intro h₁
    split at h₂ <;> simp only [ite_some_none_eq_some] at h₂
    case h_2 r pid' eff' cond h₃ =>
      replace ⟨h₂, h₂'⟩ := h₂
      subst pid' eff'
      split <;> simp only [ite_some_none_eq_some] <;> rename_i h₄
      · simp at h₄
        exact And.intro h₄.right.left h₄.left.symm
      · apply h₄ pid eff ; clear h₄
        have h₂ := all_residuals_are_true_residuals wf h₁
        subst h₂
        rfl

/--
  corollary of the above
-/
theorem knownPermits_eq_permits {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).knownPermits = (Partial.isAuthorized req entities policies).permits
:= by
  unfold Partial.Response.knownPermits Partial.Response.permits
  apply mustBeSatisfied_eq_mayBeSatisfied (eff := .permit) wf

/--
  corollary of the above
-/
theorem knownForbids_eq_forbids {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.WellFormed) :
  (Partial.isAuthorized req entities policies).knownForbids = (Partial.isAuthorized req entities policies).forbids
:= by
  unfold Partial.Response.knownForbids Partial.Response.forbids
  apply mustBeSatisfied_eq_mayBeSatisfied (eff := .forbid) wf

/--
  on concrete inputs, `Partial.Response.errors` and `Spec.errorPolicies` are equal
-/
theorem errors_eq_errorPolicies {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.WellFormed) :
  Set.make ((Partial.isAuthorized req entities policies).errors.map Prod.fst) =
  Spec.errorPolicies policies req entities
:= by
  unfold Spec.errorPolicies Partial.Response.errors
  rw [Set.make_make_eqv]
  simp only [List.Equiv, List.map_filterMap, List.subset_def, List.mem_filterMap,
    Option.map_eq_some', forall_exists_index, and_imp]
  constructor
  case left =>
    intro pid r h₁ pair h₂ h₃
    split at h₂ <;> simp only [Option.some.injEq] at h₂
    case h_1 r pid' e =>
      subst pair
      simp only at h₃
      subst pid'
      simp only [Partial.isAuthorized, List.mem_filterMap, Spec.errored, Spec.hasError,
        ite_some_none_eq_some] at *
      replace ⟨policy, h₁, h₂⟩ := h₁
      exists policy
      apply And.intro h₁
      simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf] at h₂
      split <;> split at h₂
      <;> simp only [Option.some.injEq, Residual.error.injEq] at h₂
      <;> try simp only [h₂, and_true, and_self]
      case h_1.h_4 h₃ _ e' h₄ => simp [h₃, Except.map] at h₄
  case right =>
    intro pid policy h₁ h₂
    unfold Spec.errored Spec.hasError at h₂
    simp only [ite_some_none_eq_some] at h₂
    replace ⟨h₂, h₂'⟩ := h₂
    subst h₂'
    split at h₂ <;> simp only at h₂
    case h_2 e h₃ =>
      exists (.error policy.id e)
      apply And.intro _ (by exists (policy.id, e))
      unfold Partial.isAuthorized
      simp [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf]
      exists policy
      apply And.intro h₁
      split <;> simp only [Option.some.injEq, Residual.error.injEq, true_and]
      <;> rename_i h₄
      <;> simp only [Except.map, h₃, Except.error.injEq] at h₄
      exact h₄.symm

end Cedar.Thm.Partial.Authorization.PartialOnConcrete
