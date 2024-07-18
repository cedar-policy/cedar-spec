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
import Cedar.Thm.Partial.WellFormed

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
  on concrete inputs, `Partial.Response.mayBeSatisfied` is equal to
  `Spec.satisfiedPolicies`
-/
theorem mayBeSatisfied_eq_satisfiedPolicies {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect}
  (wf : req.context.WellFormed) :
  (Partial.isAuthorized req entities policies).mayBeSatisfied eff = Spec.satisfiedPolicies eff policies req entities
:= by
  unfold Partial.Response.mayBeSatisfied Spec.satisfiedPolicies Spec.satisfiedWithEffect Spec.satisfied Partial.isAuthorized
  simp only [List.filterMap_filterMap, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf, Except.map]
  simp only [Set.make_make_eqv, List.Equiv, List.subset_def]
  simp only [List.mem_filterMap, Option.bind_eq_some, ite_some_none_eq_some, forall_exists_index, and_imp]
  constructor <;> intro pid policy h₁
  case left =>
    intro r h₂ h₃
    exists policy
    apply And.intro h₁
    split at h₂ <;> simp only [Option.some.injEq] at h₂
    <;> subst h₂
    <;> simp only [Residual.mayBeSatisfied] at h₃
    <;> split at h₃ <;> simp only [Option.some.injEq] at h₃
    <;> rename_i h₂ h₄
    <;> subst eff pid
    <;> split at h₂ <;> simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₂
    subst h₂
    rename_i v h₂ h₃
    simp only [h₂, Except.ok.injEq, true_and, and_true]
    simp only [Partial.Value.value.injEq, imp_false] at h₃
    have h₄ := policy_produces_bool_or_error policy req entities
    simp only [h₂, Bool.false_eq_true] at h₄
    split at h₄ <;> rename_i h₅ <;> simp only [Except.ok.injEq, imp_self, implies_true] at h₅
    <;> try contradiction
    subst h₅ ; simp only [Spec.Value.prim.injEq, Spec.Prim.bool.injEq]
    simp only [Spec.Value.prim.injEq, Spec.Prim.bool.injEq] at h₃
    simp only [h₃]
  case right =>
    intro h₂ h₃ h₄
    subst h₂ h₄
    exists policy
    apply And.intro h₁
    simp only [h₃, Residual.mayBeSatisfied, Option.some.injEq, exists_eq_left', reduceIte]

/--
  corollary of the above
-/
theorem permits_eq_satisfied_permits {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.context.WellFormed) :
  (Partial.isAuthorized req entities policies).permits = Spec.satisfiedPolicies .permit policies req entities
:= by
  unfold Partial.Response.permits
  simp [mayBeSatisfied_eq_satisfiedPolicies (eff := .permit) wf]

/--
  corollary of the above
-/
theorem forbids_eq_satisfied_forbids {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.context.WellFormed) :
  (Partial.isAuthorized req entities policies).forbids = Spec.satisfiedPolicies .forbid policies req entities
:= by
  unfold Partial.Response.forbids
  simp [mayBeSatisfied_eq_satisfiedPolicies (eff := .forbid) wf]

/--
  on concrete inputs, the `cond` of all residuals is literal `true`
-/
theorem all_residuals_are_true_residuals {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {id : PolicyID} {eff : Effect} {cond : Partial.Value}
  (wf : req.context.WellFormed) :
  (Residual.residual id eff cond) ∈ (Partial.isAuthorized req entities policies).residuals →
  cond = .value true
:= by
  unfold Partial.isAuthorized
  simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf, Except.map,
    List.mem_filterMap, forall_exists_index, and_imp]
  intro policy _
  have h₂ := policy_produces_bool_or_error (p := policy) (request := req) (entities := entities)
  split at h₂ <;> simp only at h₂
  · rename_i b h₃
    simp only [h₃]
    split <;> simp only [Option.some.injEq, Residual.residual.injEq, and_imp, false_implies]
    · rename_i pv h₄ h₅
      intro h₁ h₆ h₇ ; subst h₁ h₆ h₇
      simp only [Except.ok.injEq, Partial.Value.value.injEq] at h₅
      subst h₅
      match b with
      | true => rfl
      | false => simp only [forall_const] at h₄
  · rename_i e h₃ ; simp only [h₃, Option.some.injEq, false_implies]

/--
  on concrete inputs, `mustBeSatisfied` and `mayBeSatisfied` are the same
-/
theorem mustBeSatisfied_eq_mayBeSatisfied {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect}
  (wf : req.context.WellFormed) :
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
      · simp only [Residual.residual.injEq] at h₄
        exact And.intro h₄.right.left h₄.left.symm
      · apply h₄ pid eff ; clear h₄
        have h₂ := all_residuals_are_true_residuals wf h₁
        subst h₂
        rfl

/--
  corollary of the above
-/
theorem knownPermits_eq_permits {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.context.WellFormed) :
  (Partial.isAuthorized req entities policies).knownPermits = (Partial.isAuthorized req entities policies).permits
:= by
  unfold Partial.Response.knownPermits Partial.Response.permits
  apply mustBeSatisfied_eq_mayBeSatisfied (eff := .permit) wf

/--
  corollary of the above
-/
theorem knownForbids_eq_forbids {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.context.WellFormed) :
  (Partial.isAuthorized req entities policies).knownForbids = (Partial.isAuthorized req entities policies).forbids
:= by
  unfold Partial.Response.knownForbids Partial.Response.forbids
  apply mustBeSatisfied_eq_mayBeSatisfied (eff := .forbid) wf

/--
  on concrete inputs, `Partial.Response.errorPolicies` and `Spec.errorPolicies` are equal
-/
theorem errorPolicies_eq_errorPolicies {policies : Policies} {req : Spec.Request} {entities : Spec.Entities}
  (wf : req.context.WellFormed) :
  (Partial.isAuthorized req entities policies).errorPolicies =
  Spec.errorPolicies policies req entities
:= by
  unfold Spec.errorPolicies Partial.Response.errorPolicies
  rw [Set.make_make_eqv]
  simp only [List.Equiv, List.map_filterMap, List.subset_def, List.mem_filterMap,
    Option.map_eq_some', forall_exists_index, and_imp]
  constructor
  case left =>
    intro pid r h₁ h₂
    cases r <;> simp only [Option.some.injEq] at h₂
    case error pid' e =>
      subst pid'
      simp only [Partial.isAuthorized, Spec.errored, Spec.hasError,
        List.mem_filterMap, ite_some_none_eq_some] at *
      replace ⟨policy, h₁, h₂⟩ := h₁
      exists policy
      apply And.intro h₁
      simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf] at h₂
      split <;> split at h₂
      <;> simp only [Option.some.injEq, Residual.error.injEq] at h₂
      <;> try simp only [h₂, and_true, and_self]
      case h_1.h_3 h₃ _ e h₄ => simp only [h₃, Except.map] at h₄
  case right =>
    intro pid policy h₁ h₂
    unfold Spec.errored Spec.hasError at h₂
    simp only [ite_some_none_eq_some] at h₂
    replace ⟨h₂, h₂'⟩ := h₂
    subst pid
    split at h₂ <;> simp only at h₂
    case h_2 e h₃ =>
      exists (.error policy.id e)
      simp only [and_true]
      unfold Partial.isAuthorized
      simp only [Partial.Evaluation.on_concrete_eqv_concrete_eval _ req entities wf,
        List.mem_filterMap]
      exists policy
      apply And.intro h₁
      split <;> simp only [Option.some.injEq, Residual.error.injEq, true_and]
      <;> rename_i h₄
      <;> simp only [Except.map, h₃, Except.error.injEq] at h₄
      exact h₄.symm

end Cedar.Thm.Partial.Authorization.PartialOnConcrete
