/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Partial.Response
import Cedar.Partial.Value
import Cedar.Spec.Response
import Cedar.Spec.Value
import Cedar.Thm.Authorization.Evaluator
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.Partial.Evaluation
import Cedar.Thm.Partial.Evaluation.And
import Cedar.Thm.Partial.Authorization.PartialResponse
import Cedar.Thm.Utils

/-!
  This file contains lemmas about Cedar's partial authorizer.

  The toplevel theorems (proved using these lemmas) are in
  Thm/Partial/Authorization.lean, not this file.
-/

namespace Cedar.Thm.Partial.Authorization

open Cedar.Data
open Cedar.Partial (Residual Unknown)
open Cedar.Spec (Effect Policies PolicyID)

namespace PartialOnConcrete -- lemmas about the behavior of partial authorization on concrete inputs

/--
  on concrete inputs, Partial.Response.mayBeSatisfied is empty iff
  satisfiedPolicies (computed with the concrete evaluator) is empty
-/
theorem mayBeSatisfied_empty_iff_no_satisfied {policies : Spec.Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect} :
  ((Partial.isAuthorized req entities policies).mayBeSatisfied eff).isEmpty ↔
  (Spec.satisfiedPolicies eff policies req entities).isEmpty
:= by
  unfold Partial.Response.mayBeSatisfied Spec.satisfiedPolicies
  repeat rw [← Set.make_empty]
  repeat rw [List.filterMap_empty_iff_f_returns_none]
  simp [Spec.satisfiedWithEffect, Spec.satisfied]
  constructor
  case mp =>
    intro h₁ policy h₂ h₃ h₄
    simp [Partial.isAuthorized] at h₁
    simp [Partial.Evaluation.partial_eval_on_concrete_eqv_concrete_eval, Except.map] at h₁
    rw [forall_comm] at h₁
    specialize h₁ policy
    simp [h₃, Residual.mayBeSatisfied] at h₁
    split at h₁ <;> simp at h₁
    case h_1 h₅ | h_4 h₅ => simp [h₄] at h₅
    case h_2 | h_3 => apply h₁ ; assumption
  case mpr =>
    intro h₁ r h₂
    simp [Partial.isAuthorized] at h₂
    replace ⟨policy, h₂, h₃⟩ := h₂
    simp [Partial.Evaluation.partial_eval_on_concrete_eqv_concrete_eval, Except.map] at h₃
    simp [Residual.mayBeSatisfied]
    split <;> simp
    case h_1 r pid eff' cond =>
      intro h₄ ; subst h₄
      split at h₃
      <;> simp at h₃
      <;> replace ⟨h₃, h₄, h₅⟩ := h₃
      <;> subst h₃ h₅
      <;> specialize h₁ policy h₂ h₄
      <;> apply h₁ <;> clear h₁
      case h_3 x h₁ => split at h₁ <;> simp at h₁
      case h_2 v h₁ h₃ =>
        split at h₃ <;> simp at h₃
        case h_2 v' h₅ =>
          subst h₃
          simp [h₅]
          have h₃ := @policy_produces_bool_or_error policy req entities
          simp [h₅] at h₃
          split at h₃
          case h_1 b h₆ =>
            cases b
            case true => simp at h₆ ; assumption
            case false => simp at h₆ ; exfalso ; apply h₁ ; assumption
          case h_2 h₆ => simp at h₆
          case h_3 => contradiction

/--
  corollary of the above
-/
theorem permits_empty_iff_no_satisfied_permits {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} :
  (Partial.isAuthorized req entities policies).permits.isEmpty ↔
  (Spec.satisfiedPolicies .permit policies req entities).isEmpty
:= by
  unfold Partial.Response.permits
  apply mayBeSatisfied_empty_iff_no_satisfied (eff := .permit)

/--
  corollary of the above
-/
theorem forbids_empty_iff_no_satisfied_forbids {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} :
  (Partial.isAuthorized req entities policies).forbids.isEmpty ↔
  (Spec.satisfiedPolicies .forbid policies req entities).isEmpty
:= by
  unfold Partial.Response.forbids
  apply mayBeSatisfied_empty_iff_no_satisfied (eff := .forbid)

/--
  another corollary, for the nonempty case
-/
theorem mayBeSatisfied_nonempty_iff_satisfied_nonempty {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect} :
  ((Partial.isAuthorized req entities policies).mayBeSatisfied eff).isEmpty = false ↔
  (Spec.satisfiedPolicies eff policies req entities).isEmpty = false
:= by
  constructor
  case mp =>
    intro h₁
    apply eq_false_of_ne_true
    replace h₁ := ne_true_of_eq_false h₁
    rw [mayBeSatisfied_empty_iff_no_satisfied] at h₁
    assumption
  case mpr =>
    intro h₁
    apply eq_false_of_ne_true
    replace h₁ := ne_true_of_eq_false h₁
    rw [← mayBeSatisfied_empty_iff_no_satisfied] at h₁
    assumption

/--
  corollary of the above
-/
theorem permits_nonempty_iff_satisfied_permits_nonempty {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} :
  (Partial.isAuthorized req entities policies).permits.isEmpty = false ↔
  (Spec.satisfiedPolicies .permit policies req entities).isEmpty = false
:= by
  unfold Partial.Response.permits
  apply mayBeSatisfied_nonempty_iff_satisfied_nonempty (eff := .permit)

/--
  corollary of the above
-/
theorem forbids_nonempty_iff_satisfied_forbids_nonempty {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} :
  (Partial.isAuthorized req entities policies).forbids.isEmpty = false ↔
  (Spec.satisfiedPolicies .forbid policies req entities).isEmpty = false
:= by
  unfold Partial.Response.forbids
  apply mayBeSatisfied_nonempty_iff_satisfied_nonempty (eff := .forbid)

/--
  on concrete inputs, the `cond` of all residuals is literal `true`
-/
theorem all_residuals_are_true_residuals {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {id : PolicyID} {eff : Effect} {cond : Partial.Expr} :
  (Residual.residual id eff cond) ∈ (Partial.isAuthorized req entities policies).residuals →
  cond = .lit (.bool true)
:= by
  intro h₁
  unfold Partial.isAuthorized at h₁
  simp [Partial.Evaluation.partial_eval_on_concrete_eqv_concrete_eval, Except.map] at h₁
  replace ⟨policy, _, h₁⟩ := h₁
  have h₂ := policy_produces_bool_or_error (p := policy) (request := req) (entities := entities)
  split at h₂ <;> simp at h₂
  case h_1 b h₃ =>
    simp [h₃] at h₁
    split at h₁ <;> simp at h₁
    case h_2 v h₄ h₅ =>
      replace ⟨h₁, _, h₆⟩ := h₁
      subst h₁ h₆
      simp at h₅
      subst h₅
      simp [Spec.Value.asPartialExpr]
      cases b
      case true => rfl
      case false => simp at h₄
    case h_3 cond' h₄ =>
      replace ⟨h₁, _, h₅⟩ := h₁
      subst h₁ h₅
      simp at h₄
  case h_2 e h₃ => simp [h₃] at h₁

/--
  on concrete inputs, `mustBeSatisfied` and `mayBeSatisfied` are the same
-/
theorem mustBeSatisfied_eq_mayBeSatisfied {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} {eff : Effect} :
  (Partial.isAuthorized req entities policies).mustBeSatisfied eff = (Partial.isAuthorized req entities policies).mayBeSatisfied eff
:= by
  simp only [Partial.Response.mustBeSatisfied, Partial.Response.mayBeSatisfied]
  rw [Set.make_make_eqv]
  unfold List.Equiv
  simp [List.subset_def, Residual.mustBeSatisfied, Residual.mayBeSatisfied]
  constructor <;> intro pid r h₁ h₂
  case left =>
    exists r
    apply And.intro h₁
    split at h₂ <;> simp at h₂
    case h_1 r pid' eff' =>
      replace ⟨h₂, h₃⟩ := h₂
      subst eff' pid'
      simp
  case right =>
    exists r
    apply And.intro h₁
    split at h₂ <;> simp at h₂
    case h_1 r pid' eff' cond =>
      replace ⟨h₂, h₃⟩ := h₂
      subst eff' pid'
      split <;> simp
      case h_1 pid' eff' h₃ =>
        simp at h₃
        exact And.intro h₃.right.left h₃.left.symm
      case h_2 r' h₃ =>
        specialize h₃ pid eff
        apply h₃ ; clear h₃
        have h₂ := all_residuals_are_true_residuals h₁
        subst h₂
        rfl

/--
  corollary of the above
-/
theorem knownPermits_eq_permits {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} :
  (Partial.isAuthorized req entities policies).knownPermits = (Partial.isAuthorized req entities policies).permits
:= by
  unfold Partial.Response.knownPermits Partial.Response.permits
  apply mustBeSatisfied_eq_mayBeSatisfied (eff := .permit)

/--
  corollary of the above
-/
theorem knownForbids_eq_forbids {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} :
  (Partial.isAuthorized req entities policies).knownForbids = (Partial.isAuthorized req entities policies).forbids
:= by
  unfold Partial.Response.knownForbids Partial.Response.forbids
  apply mustBeSatisfied_eq_mayBeSatisfied (eff := .forbid)

/--
  on concrete inputs, `Partial.Response.errors` and `errorPolicies` are equal
-/
theorem errors_eq_errorPolicies {policies : Policies} {req : Spec.Request} {entities : Spec.Entities} :
  Set.make ((Partial.isAuthorized req entities policies).errors.map Prod.fst) = Spec.errorPolicies policies req entities
:= by
  unfold Spec.errorPolicies Partial.Response.errors
  simp [Set.make_make_eqv]
  simp [List.map_filterMap, List.Equiv, List.subset_def]
  constructor
  case left =>
    intro pid r h₁ pair h₂ h₃
    split at h₂ <;> simp at h₂
    case h_1 r pid' e =>
      subst pair
      simp at h₃
      subst pid'
      simp [Partial.isAuthorized, Spec.errored, Spec.hasError] at *
      replace ⟨policy, h₁, h₂⟩ := h₁
      exists policy
      apply And.intro h₁
      simp [Partial.Evaluation.partial_eval_on_concrete_eqv_concrete_eval] at h₂
      split <;> split at h₂ <;> simp at h₂ <;> try simp [h₂]
      case h_1.h_4 h₃ _ e' h₄ => simp [h₃, Except.map] at h₄
  case right =>
    intro pid policy h₁ h₂
    unfold Spec.errored Spec.hasError at h₂
    simp at h₂
    replace ⟨h₂, h₃⟩ := h₂
    subst h₃
    split at h₂ <;> simp at h₂
    case h_2 e h₃ =>
      exists (.error policy.id e)
      constructor
      case left =>
        unfold Partial.isAuthorized
        simp [Partial.Evaluation.partial_eval_on_concrete_eqv_concrete_eval]
        exists policy
        apply And.intro h₁
        split <;> simp
        case h_1 h₄ | h_2 h₄ | h_3 h₄ => simp [Except.map, h₃] at h₄
        case h_4 h₄ => simp [Except.map, h₃] at h₄ ; simp [h₄]
      case right => exists (policy.id, e)

end PartialOnConcrete

/--
  for every residual that exists after substitution,
  a residual with the same id and effect must have existed before substitution

  (or, if the residual after substitution is an evaluation error, then a
  residual with the same id must have existed before substitution)
-/
theorem subst_doesn't_increase_residuals {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} {r' : Residual} :
  req.subst subsmap = some req' →
  r' ∈ (Partial.isAuthorized req' (entities.subst subsmap) policies).residuals →
  ∃ r ∈ (Partial.isAuthorized req entities policies).residuals, r.id = r'.id ∧ (r.effect = r'.effect ∨ r'.effect = none)
:= by
  unfold Partial.isAuthorized
  intro h₁ h₂
  simp at *
  replace ⟨p, ⟨h₂, h₃⟩⟩ := h₂
  split at h₃ <;> simp at h₃ <;> subst h₃
  case h_2 v h₃ h₄ =>
    -- after subst, partial eval of the policy produced a .value other than False
    have h₅ := Partial.Evaluation.subst_preserves_errors_mt (expr := p.toExpr.asPartialExpr) (entities := entities) h₁ (by
      simp [Except.isOk, Except.toBool]
      split <;> simp
      case _ e h₅ =>
        simp [Partial.subs_expr_id] at h₅
        simp [h₅] at h₄
    )
    simp [Except.isOk, Except.toBool] at h₅
    split at h₅ <;> simp at h₅
    clear h₅
    case _ pval h₅ =>
      exists (Residual.residual p.id p.effect pval.asPartialExpr)
      constructor
      case left =>
        exists p
        apply And.intro h₂
        split <;> simp
        case h_1 h₅ _ h₆ =>
          -- before subst, partial eval of the policy produced False
          have h₇ := Partial.Evaluation.subst_preserves_evaluation_to_literal h₆ h₁
          rw [Partial.subs_expr_id] at h₇
          simp [h₇] at h₄
          exact h₃ h₄.symm
        case h_2 h₅ _ v h₆ h₇ =>
          -- before subst, partial eval of the policy produced a .value other than False
          simp [h₇] at h₅
          subst h₅
          simp [Partial.Value.asPartialExpr]
        case h_3 h₅ _ x h₆ =>
          -- before subst, partial eval of the policy produced a .residual
          simp [h₆] at h₅
          subst h₅
          simp [Partial.Value.asPartialExpr]
        case h_4 h₅ _ e h₆ =>
          -- before subst, partial eval of the policy produced an error
          simp [h₆] at h₅
      case right =>
        constructor
        case left => simp [Residual.id]
        case right => simp [Residual.effect]
  case h_3 x h₃ =>
    -- after subst, partial eval of the policy produced a .residual
    have h₄ := Partial.Evaluation.subst_preserves_errors_mt (expr := p.toExpr.asPartialExpr) (entities := entities) h₁ (by
      simp [Except.isOk, Except.toBool]
      split <;> simp
      case _ e h₄ =>
        simp [Partial.subs_expr_id] at h₄
        simp [h₄] at h₃
    )
    simp [Except.isOk, Except.toBool] at h₄
    split at h₄ <;> simp at h₄
    clear h₄
    case _ pval h₄ =>
      exists (Residual.residual p.id p.effect pval.asPartialExpr)
      constructor
      case left =>
        exists p
        apply And.intro h₂
        split <;> simp
        case h_1 h₅ _ h₆ =>
          -- before subst, partial eval of the policy produced False
          have h₇ := Partial.Evaluation.subst_preserves_evaluation_to_literal h₆ h₁
          rw [Partial.subs_expr_id] at h₇
          simp [h₇] at h₃
        case h_2 h₅ _ v h₆ h₇ =>
          -- before subst, partial eval of the policy produced a .value other than False
          simp [h₇] at h₄
          subst h₄
          simp [Partial.Value.asPartialExpr]
        case h_3 h₅ _ x h₆ =>
          -- before subst, partial eval of the policy produced a .residual
          simp [h₆] at h₄
          subst h₄
          simp [Partial.Value.asPartialExpr]
        case h_4 h₅ _ e h₅ =>
          -- before subst, partial eval of the policy produced an error
          simp [h₅] at h₄
      case right =>
        constructor
        case left => simp [Residual.id]
        case right => simp [Residual.effect]
  case h_4 e' h₃ =>
    -- after subst, partial eval of the policy produced an error
    cases h₄ : Partial.evaluate p.toExpr req entities
    case error e =>
      exists (Residual.error p.id e)
      constructor
      case left =>
        exists p
        apply And.intro h₂
        split <;> simp
        case h_1 h₅ | h_2 h₅ | h_3 h₅ =>
          -- before subst, partial eval of the policy produced ok
          simp [h₅] at h₄
        case h_4 e'' h₅ =>
          -- before subst, partial eval of the policy produced an error
          simp [h₅] at h₄ ; assumption
      case right =>
        constructor
        case left => simp [Residual.id]
        case right => simp [Residual.effect]
    case ok pval =>
      exists (Residual.residual p.id p.effect pval.asPartialExpr)
      constructor
      case left =>
        exists p
        apply And.intro h₂
        split <;> simp
        case h_1 h₅ =>
          -- before subst, partial eval of the policy produced False
          have h₆ := Partial.Evaluation.subst_preserves_evaluation_to_literal h₅ h₁
          rw [Partial.subs_expr_id] at h₆
          simp [h₆] at h₃
        case h_2 h₅ =>
          -- before subst, partial eval of the policy produced a .value other than False
          simp [h₅] at h₄
          subst h₄
          simp [Partial.Value.asPartialExpr]
        case h_3 x h₅ =>
          -- before subst, partial eval of the policy produced a .residual
          simp [h₅] at h₄
          subst h₄
          simp [Partial.Value.asPartialExpr]
        case h_4 e h₅ =>
          -- before subst, partial eval of the policy produced an error
          simp [h₅] at h₄
      case right =>
        constructor
        case left => simp [Residual.id]
        case right => simp [Residual.effect]

/--
  if a residual was `true` before substitution, it's still `true` after any
  substitution
-/
theorem subst_preserves_true_residuals {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} {pid : PolicyID} {effect : Effect} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  req.subst subsmap = some req' →
  Residual.residual pid effect (.lit (.bool true)) ∈ (Partial.isAuthorized req entities policies).residuals →
  Residual.residual pid effect (.lit (.bool true)) ∈ (Partial.isAuthorized req' (entities.subst subsmap) policies).residuals
:= by
  unfold Partial.isAuthorized
  intro wf rcu_e rcu_r h₁ h₂
  simp at *
  replace ⟨p, h₂⟩ := h₂
  exists p
  apply And.intro h₂.left
  replace h₂ := h₂.right
  split <;> simp
  case h_1 h₃ =>
    -- after subst, partial eval of the policy produced False
    split at h₂ <;> simp at h₂
    case _ h₄ h₅ =>
      replace ⟨_, _, h₂⟩ := h₂
      rw [Spec.Value.prim_prim] at h₂
      subst h₂
      have h₆ := Partial.Evaluation.subst_preserves_evaluation_to_literal h₅ h₁
      rw [Partial.subs_expr_id] at h₆
      simp [h₆] at h₃
    case _ h₄ =>
      replace ⟨_, _, h₂⟩ := h₂
      subst h₂
      have h₅ := Partial.Evaluation.residuals_contain_unknowns wf rcu_e rcu_r _ h₄
      unfold Partial.Expr.containsUnknown at h₅
      rw [List.any_eq_true] at h₅
      replace ⟨x, h₅⟩ := h₅
      unfold Partial.Expr.subexpressions at h₅
      rw [List.mem_cons] at h₅
      simp only [List.not_mem_nil, or_false] at h₅
      replace ⟨h₅, h₆⟩ := h₅
      subst h₅
      simp [Partial.Expr.isUnknown] at h₆
  case h_2 h₃ | h_3 h₃ =>
    -- after subst, partial eval of the policy produced a .value (other than False) or .residual
    split at h₂ <;> simp at h₂
    case h_2 v' h₄ _ v h₅ h₆ =>
      apply And.intro h₂.left
      replace h₂ := h₂.right
      apply And.intro h₂.left
      replace h₂ := h₂.right
      rw [Spec.Value.prim_prim] at *
      subst h₂
      have h₇ := Partial.Evaluation.subst_preserves_evaluation_to_literal h₆ h₁
      rw [Partial.subs_expr_id] at h₇
      simp [h₃] at h₇
      try assumption
    case h_3 v' h₄ _ x h₅ =>
      apply And.intro h₂.left
      replace h₂ := h₂.right
      apply And.intro h₂.left
      replace h₂ := h₂.right
      subst h₂
      have h₆ := Partial.Evaluation.residuals_contain_unknowns wf rcu_e rcu_r _ h₅
      simp [Partial.Expr.containsUnknown, Partial.Expr.subexpressions, Partial.Expr.isUnknown] at h₆
  case h_4 h₃ =>
    -- after subst, partial eval of the policy produced an error
    split at h₂ <;> simp at h₂
    case _ v h₅ h₆ =>
      replace ⟨_, _, h₂⟩ := h₂
      rw [Spec.Value.prim_prim] at h₂
      subst h₂
      have h₇ := Partial.Evaluation.subst_preserves_evaluation_to_literal h₆ h₁
      rw [Partial.subs_expr_id] at h₇
      simp [h₃] at h₇
    case _ x h₄ =>
      replace ⟨_, _, h₂⟩ := h₂
      subst h₂
      have h₅ := Partial.Evaluation.residuals_contain_unknowns wf rcu_e rcu_r _ h₄
      simp [Partial.Expr.containsUnknown, Partial.Expr.subexpressions, Partial.Expr.isUnknown] at h₅

/--
  if a policy mustBeSatisfied before substitution, it still mustBeSatisfied
  after substitution
-/
theorem subst_preserves_mustBeSatisfied {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} {pid : PolicyID} {eff : Effect} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  req.subst subsmap = some req' →
  pid ∈ (Partial.isAuthorized req entities policies).mustBeSatisfied eff →
  pid ∈ (Partial.isAuthorized req' (entities.subst subsmap) policies).mustBeSatisfied eff
:= by
  unfold Partial.Response.mustBeSatisfied Residual.mustBeSatisfied
  intro wf rcu_e rcu_r h₁ h₂
  rw [← Set.make_mem] at *
  simp [List.filterMap_nonempty_iff_exists_f_returns_some] at *
  replace ⟨r, ⟨h₂, h₃⟩⟩ := h₂
  exists r
  apply And.intro _ h₃
  split at h₃ <;> simp at h₃
  replace ⟨h₃, h₄⟩ := h₃
  subst h₃ h₄
  apply subst_preserves_true_residuals wf rcu_e rcu_r h₁ h₂

/--
  corollary of the above
-/
theorem subst_preserves_knownPermits {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} {pid : PolicyID} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  req.subst subsmap = some req' →
  pid ∈ (Partial.isAuthorized req entities policies).knownPermits →
  pid ∈ (Partial.isAuthorized req' (entities.subst subsmap) policies).knownPermits
:= by
  unfold Partial.Response.knownPermits
  apply subst_preserves_mustBeSatisfied (eff := .permit)

/--
  corollary of the above
-/
theorem subst_preserves_knownForbids {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} {pid : PolicyID} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  req.subst subsmap = some req' →
  pid ∈ (Partial.isAuthorized req entities policies).knownForbids →
  pid ∈ (Partial.isAuthorized req' (entities.subst subsmap) policies).knownForbids
:= by
  unfold Partial.Response.knownForbids
  apply subst_preserves_mustBeSatisfied (eff := .forbid)

/--
  helper lemma

  not currently used; we might or might not need this in this formulation
-/
theorem fullSubst_preserves_mustBeSatisfied {policies : Policies} {req : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Spec.Value} {req' : Spec.Request} {entities' : Spec.Entities} {pid : PolicyID} {eff : Effect} :
  req.fullSubst subsmap = some req' →
  entities.fullSubst subsmap = some entities' →
  pid ∈ (Partial.isAuthorized req entities policies).mustBeSatisfied eff →
  pid ∈ (Partial.isAuthorized req' entities' policies).mustBeSatisfied eff
:= by
  intro h₁ h₂ h₃
  -- can we make this a corollary of `subst_preserves_mustBeSatisfied` somehow?
  -- even better, can we have some general result that allows us to say that
  -- anything that `subst` preserves, `fullSubst` must also preserve?
  sorry

/--
  if there are no `mayBeSatisfied` policies with a particular effect before
  substitution, there won't be after substitution either
-/
theorem subst_preserves_empty_mayBeSatisfied {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} {eff : Effect} :
  req.subst subsmap = some req' →
  ((Partial.isAuthorized req entities policies).mayBeSatisfied eff).isEmpty →
  ((Partial.isAuthorized req' (entities.subst subsmap) policies).mayBeSatisfied eff).isEmpty
:= by
  intro h₁ h₂
  unfold Partial.Response.mayBeSatisfied Residual.mayBeSatisfied at *
  rw [← Set.make_empty] at *
  simp [List.filterMap_empty_iff_f_returns_none] at *
  intro r' h₃
  rcases subst_doesn't_increase_residuals h₁ h₃ with ⟨r, ⟨h₄, h₅, h₆ | h₆⟩⟩
  case _ =>
    split <;> simp
    case _ r' pid eff' cond =>
      intro h₇ ; subst h₇
      specialize h₂ r h₄
      simp [Residual.id] at h₅
      simp [Residual.effect] at h₆
      split at h₆ <;> simp at h₆
      subst h₆
      simp [h₅] at h₂
  case _ =>
    split <;> simp
    simp [Residual.effect] at h₆

/--
  corollary of the above
-/
theorem subst_preserves_empty_permits {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} :
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).permits.isEmpty →
  (Partial.isAuthorized req' (entities.subst subsmap) policies).permits.isEmpty
:= by
  unfold Partial.Response.permits
  apply subst_preserves_empty_mayBeSatisfied (eff := .permit)

/--
  corollary of the above
-/
theorem subst_preserves_empty_forbids {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} :
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).forbids.isEmpty →
  (Partial.isAuthorized req' (entities.subst subsmap) policies).forbids.isEmpty
:= by
  unfold Partial.Response.forbids
  apply subst_preserves_empty_mayBeSatisfied (eff := .forbid)

/--
  if there are any `mustBeSatisfied` policies with a particular effect before
  substitution, there will be after substitution too
-/
theorem subst_preserves_nonempty_mustBeSatisfied {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} {eff : Effect} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  req.subst subsmap = some req' →
  ¬ ((Partial.isAuthorized req entities policies).mustBeSatisfied eff).isEmpty →
  ¬ ((Partial.isAuthorized req' (entities.subst subsmap) policies).mustBeSatisfied eff).isEmpty
:= by
  repeat rw [Set.non_empty_iff_exists]
  intro wf rcu_e rcu_r h₁ h₂
  replace ⟨pid, h₂⟩ := h₂
  exists pid
  exact subst_preserves_mustBeSatisfied wf rcu_e rcu_r h₁ h₂

/--
  corollary of the above
-/
theorem subst_preserves_nonempty_knownForbids {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  req.subst subsmap = some req' →
  ¬ (Partial.isAuthorized req entities policies).knownForbids.isEmpty →
  ¬ (Partial.isAuthorized req' (entities.subst subsmap) policies).knownForbids.isEmpty
:= by
  unfold Partial.Response.knownForbids
  apply subst_preserves_nonempty_mustBeSatisfied (eff := .forbid)

/--
  if partial authorization returns a concrete decision, and there are no knownForbids,
  then knownPermits is either empty both before and after any substitution, or
  nonempty both before and after any substitution
-/
theorem partial_authz_decision_concrete_no_knownForbids_then_knownPermits_unknown_agnostic {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map String Partial.RestrictedValue} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  (Partial.isAuthorized req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).knownForbids.isEmpty →
  (Partial.isAuthorized req entities policies).knownPermits.isEmpty = (Partial.isAuthorized req' (entities.subst subsmap) policies).knownPermits.isEmpty
:= by
  intro wf rcu_e rcu_r h₁ h₂ h₃
  cases h₄ : (Partial.isAuthorized req entities policies).knownPermits.isEmpty
  case true =>
    rcases Partial.Response.decision_concrete_then_kf_or_kp h₁ with h₅ | ⟨h₅, _⟩ | h₅
    case _ => contradiction
    case _ => contradiction
    case _ =>
      have h₆ := subst_preserves_empty_permits h₂ h₅
      apply Eq.symm
      by_contra h₇
      replace ⟨pid, h₇⟩ := (Set.non_empty_iff_exists _).mp h₇
      replace h₇ := Partial.Response.in_knownPermits_in_permits h₇
      rw [Set.empty_iff_not_exists] at h₆
      apply h₆ ; clear h₆
      exists pid
  case false =>
    unfold Partial.Response.knownPermits Partial.Response.mustBeSatisfied at *
    apply Eq.symm
    rw [← Set.make_non_empty] at *
    intro h₅
    simp [List.filterMap_empty_iff_f_returns_none] at h₅
    simp [List.filterMap_nonempty_iff_exists_f_returns_some] at h₄
    replace ⟨r, ⟨h₄, h₆⟩⟩ := h₄
    specialize h₅ r
    simp [Option.isSome] at h₆
    split at h₆ <;> simp at h₆
    clear h₆
    rename_i optid pid h₆
    unfold Residual.mustBeSatisfied at h₅ h₆
    split at h₆ <;> simp at h₆
    replace ⟨h₆, h₇⟩ := h₆
    subst h₆ h₇
    rename_i r pid
    simp at h₅
    apply h₅ ; clear h₅
    exact subst_preserves_true_residuals wf rcu_e rcu_r h₂ h₄

/--
  if there are any knownForbids before substitution, you always get Deny after
  any substitution
-/
theorem if_knownForbids_then_deny_after_any_sub {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map String Partial.RestrictedValue} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  ¬ (Partial.isAuthorized req entities policies).knownForbids.isEmpty →
  req.subst subsmap = some req' →
  (Partial.isAuthorized req' (entities.subst subsmap) policies).decision = .deny
:= by
  intro wf rcu_e rcu_r h₁ h₂
  unfold Partial.Response.decision
  simp
  intro h₃
  replace h₁ := subst_preserves_nonempty_knownForbids wf rcu_e rcu_r h₂ h₁
  contradiction

/--
  helper lemma
-/
theorem partial_authz_decision_concrete_no_knownForbids_some_permits_then_must_be_permits_after_any_sub {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map String Partial.RestrictedValue} :
  entities.AllWellFormed →
  Partial.Entities.ResidualsContainUnknowns entities →
  Partial.Request.ResidualsContainUnknowns req →
  (Partial.isAuthorized req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).knownForbids.isEmpty →
  ¬ (Partial.isAuthorized req entities policies).permits.isEmpty →
  ¬ (Partial.isAuthorized req' (entities.subst subsmap) policies).permits.isEmpty
:= by
  intro wf rcu_e rcu_r h₁ h₂ h₃ h₄
  rcases Partial.Response.decision_concrete_then_kf_or_kp h₁ with h₅ | ⟨h₅, _⟩ | h₅
  case _ => contradiction
  case _ =>
    replace ⟨kp, h₅⟩ := (Set.non_empty_iff_exists _).mp h₅
    rw [Set.non_empty_iff_exists]
    exists kp
    apply Partial.Response.in_knownPermits_in_permits
    apply subst_preserves_knownPermits wf rcu_e rcu_r h₂
    assumption
  case _ => contradiction

/--
  helper lemma
-/
theorem partial_authz_decision_concrete_no_knownForbids_some_permits_then_no_knownForbids_after_any_sub {policies : Policies} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map String Partial.RestrictedValue} :
  (Partial.isAuthorized req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (Partial.isAuthorized req entities policies).knownForbids.isEmpty →
  ¬ (Partial.isAuthorized req entities policies).permits.isEmpty →
  (Partial.isAuthorized req' (entities.subst subsmap) policies).knownForbids.isEmpty
:= by
  intro h₁ h₂ h₃ h₄
  rcases Partial.Response.decision_concrete_then_kf_or_kp h₁ with h₅ | ⟨_, h₆⟩ | h₅
  case _ => contradiction
  case _ =>
    apply Partial.Response.empty_forbids_empty_knownForbids
    apply subst_preserves_empty_forbids h₂ h₆
  case _ => contradiction
