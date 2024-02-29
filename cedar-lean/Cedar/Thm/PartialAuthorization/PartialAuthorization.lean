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

import Cedar.Spec.Response
import Cedar.Spec.Value
import Cedar.Spec.PartialAuthorizer
import Cedar.Spec.PartialResponse
import Cedar.Spec.PartialValue
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.Set
import Cedar.Thm.PartialEval
import Cedar.Thm.PartialEval.And
import Cedar.Thm.PartialAuthorization.PartialResponse
import Cedar.Thm.Utils

/-!
  This file contains lemmas about Cedar's partial authorizer.

  The toplevel theorems (proved using these lemmas) are in
  Thm/PartialAuthorization.lean, not this file.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Except

/--
  helper lemma
-/
theorem subs_doesn't_increase_residuals {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {r' : Residual} :
  req.subst subsmap = some req' →
  r' ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).residuals →
  ∃ r ∈ (isAuthorizedPartial req entities policies).residuals, r.id = r'.id ∧ (r.effect = r'.effect ∨ r'.effect = none)
:= by
  unfold isAuthorizedPartial
  intro h₁ h₂
  simp at *
  replace ⟨p, ⟨h₂, h₃⟩⟩ := h₂
  split at h₃ <;> simp at h₃ <;> subst h₃
  case h_2 v h₃ h₄ =>
    -- after subst, partial eval of the policy produced a .value other than False
    have h₅ := subs_preserves_errors_mt (expr := p.toExpr.asPartialExpr) (entities := entities) h₁ (by
      simp [Except.isOk, Except.toBool]
      split <;> simp
      case _ e h₅ =>
        simp [subs_expr_id] at h₅
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
          have h₇ := subs_preserves_evaluation_to_literal h₆ h₁
          rw [subs_expr_id] at h₇
          simp [h₇] at h₄
          exact h₃ h₄.symm
        case h_2 h₅ _ v h₆ h₇ =>
          -- before subst, partial eval of the policy produced a .value other than False
          simp [h₇] at h₅
          subst h₅
          simp [PartialValue.asPartialExpr]
        case h_3 h₅ _ x h₆ =>
          -- before subst, partial eval of the policy produced a .residual
          simp [h₆] at h₅
          subst h₅
          simp [PartialValue.asPartialExpr]
        case h_4 h₅ _ e h₆ =>
          -- before subst, partial eval of the policy produced an error
          simp [h₆] at h₅
      case right =>
        constructor
        case left => simp [Residual.id]
        case right => simp [Residual.effect]
  case h_3 x h₃ =>
    -- after subst, partial eval of the policy produced a .residual
    have h₄ := subs_preserves_errors_mt (expr := p.toExpr.asPartialExpr) (entities := entities) h₁ (by
      simp [Except.isOk, Except.toBool]
      split <;> simp
      case _ e h₄ =>
        simp [subs_expr_id] at h₄
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
          have h₇ := subs_preserves_evaluation_to_literal h₆ h₁
          rw [subs_expr_id] at h₇
          simp [h₇] at h₃
        case h_2 h₅ _ v h₆ h₇ =>
          -- before subst, partial eval of the policy produced a .value other than False
          simp [h₇] at h₄
          subst h₄
          simp [PartialValue.asPartialExpr]
        case h_3 h₅ _ x h₆ =>
          -- before subst, partial eval of the policy produced a .residual
          simp [h₆] at h₄
          subst h₄
          simp [PartialValue.asPartialExpr]
        case h_4 h₅ _ e h₅ =>
          -- before subst, partial eval of the policy produced an error
          simp [h₅] at h₄
      case right =>
        constructor
        case left => simp [Residual.id]
        case right => simp [Residual.effect]
  case h_4 e' h₃ =>
    -- after subst, partial eval of the policy produced an error
    cases h₄ : partialEvaluate p.toExpr req entities
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
          have h₆ := subs_preserves_evaluation_to_literal h₅ h₁
          rw [subs_expr_id] at h₆
          simp [h₆] at h₃
        case h_2 h₅ =>
          -- before subst, partial eval of the policy produced a .value other than False
          simp [h₅] at h₄
          subst h₄
          simp [PartialValue.asPartialExpr]
        case h_3 x h₅ =>
          -- before subst, partial eval of the policy produced a .residual
          simp [h₅] at h₄
          subst h₄
          simp [PartialValue.asPartialExpr]
        case h_4 e h₅ =>
          -- before subst, partial eval of the policy produced an error
          simp [h₅] at h₄
      case right =>
        constructor
        case left => simp [Residual.id]
        case right => simp [Residual.effect]

/--
  helper lemma
-/
theorem subs_preserves_true_residuals {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {pid : PolicyID} {effect : Effect} :
  req.subst subsmap = some req' →
  Residual.residual pid effect (.lit (.bool true)) ∈ (isAuthorizedPartial req entities policies).residuals →
  Residual.residual pid effect (.lit (.bool true)) ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).residuals
:= by
  unfold isAuthorizedPartial
  intro h₁ h₂
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
      rw [Value.prim_prim] at h₂
      subst h₂
      -- h₃ and h₅ are contradictory, need to show it
      sorry
    case _ h₄ =>
      replace ⟨_, _, h₂⟩ := h₂
      subst h₂
      -- h₃ and h₄ are contradictory, need to show it
      sorry
  case h_2 h₃ | h_3 h₃ =>
    -- after subst, partial eval of the policy produced a .value (other than False) or .residual
    split at h₂ <;> simp at h₂
    case h_2 v' h₄ _ v h₅ h₆ =>
      apply And.intro h₂.left
      replace h₂ := h₂.right
      apply And.intro h₂.left
      replace h₂ := h₂.right
      rw [Value.prim_prim] at *
      subst h₂
      have h₇ := subs_preserves_evaluation_to_literal h₆ h₁
      rw [subs_expr_id] at h₇
      simp [h₃] at h₇
      try assumption
    case h_3 v' h₄ _ x h₅ =>
      apply And.intro h₂.left
      replace h₂ := h₂.right
      apply And.intro h₂.left
      replace h₂ := h₂.right
      subst h₂
      have h₆ := residuals_contain_unknowns h₅
      simp [PartialExpr.containsUnknown, PartialExpr.subexpressions, PartialExpr.isUnknown] at h₆
  case h_4 h₃ =>
    -- after subst, partial eval of the policy produced an error
    split at h₂ <;> simp at h₂
    case _ v h₅ h₆ =>
      replace ⟨_, _, h₂⟩ := h₂
      rw [Value.prim_prim] at h₂
      subst h₂
      have h₇ := subs_preserves_evaluation_to_literal h₆ h₁
      rw [subs_expr_id] at h₇
      simp [h₃] at h₇
    case _ x h₄ =>
      replace ⟨_, _, h₂⟩ := h₂
      subst h₂
      have h₅ := residuals_contain_unknowns h₄
      simp [PartialExpr.containsUnknown, PartialExpr.subexpressions, PartialExpr.isUnknown] at h₅

/--
  helper lemma
-/
theorem subs_preserves_knownPermits {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {pid : PolicyID} :
  req.subst subsmap = some req' →
  pid ∈ (isAuthorizedPartial req entities policies).knownPermits →
  pid ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).knownPermits
:= by
  intro h₁ h₂
  unfold PartialResponse.knownPermits at *
  simp at *
  rw [← Set.make_mem] at *
  simp [List.filterMap_nonempty_iff_exists_f_returns_some] at *
  replace ⟨r, ⟨h₂, h₃⟩⟩ := h₂
  exists r
  apply And.intro _ h₃
  split at h₃ <;> simp at h₃
  subst h₃
  apply subs_preserves_true_residuals h₁ h₂

/--
  helper lemma
-/
theorem subs_preserves_knownForbids {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} {pid : PolicyID} :
  req.subst subsmap = some req' →
  pid ∈ (isAuthorizedPartial req entities policies).knownForbids →
  pid ∈ (isAuthorizedPartial req' (entities.subst subsmap) policies).knownForbids
:= by
  intro h₁ h₂
  unfold PartialResponse.knownForbids at *
  simp at *
  rw [← Set.make_mem] at *
  simp [List.filterMap_nonempty_iff_exists_f_returns_some] at *
  replace ⟨r, ⟨h₂, h₃⟩⟩ := h₂
  exists r
  apply And.intro _ h₃
  split at h₃ <;> simp at h₃
  subst h₃
  apply subs_preserves_true_residuals h₁ h₂

/--
  helper lemma
-/
theorem subs_preserves_empty_permits {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).permits.isEmpty →
  (isAuthorizedPartial req' (entities.subst subsmap) policies).permits.isEmpty
:= by
  intro h₁ h₂
  unfold PartialResponse.permits at *
  simp at *
  rw [← Set.make_empty] at *
  simp [List.filterMap_empty_iff_f_returns_none] at *
  intro r h₃
  rcases subs_doesn't_increase_residuals h₁ h₃ with ⟨r', ⟨h₄, h₅, h₆ | h₆⟩⟩
  case _ =>
    split <;> simp
    case _ pid cond =>
      specialize h₂ r' h₄
      simp [Residual.id] at h₅
      simp [Residual.effect] at h₆
      split at h₆ <;> simp at h₆
      subst h₆
      simp [h₅] at h₂
  case _ =>
    split <;> simp
    simp [Residual.effect] at h₆

/--
  helper lemma
-/
theorem subs_preserves_empty_forbids {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).forbids.isEmpty →
  (isAuthorizedPartial req' (entities.subst subsmap) policies).forbids.isEmpty
:= by
  intro h₁ h₂
  unfold PartialResponse.forbids at *
  simp at *
  rw [← Set.make_empty] at *
  simp [List.filterMap_empty_iff_f_returns_none] at *
  intro r h₃
  rcases subs_doesn't_increase_residuals h₁ h₃ with ⟨r', ⟨h₄, h₅, h₆ | h₆⟩⟩
  case _ =>
    split <;> simp
    case _ pid cond =>
      specialize h₂ r' h₄
      simp [Residual.id] at h₅
      simp [Residual.effect] at h₆
      split at h₆ <;> simp at h₆
      subst h₆
      simp [h₅] at h₂
  case _ =>
    split <;> simp
    simp [Residual.effect] at h₆

/--
  helper lemma
-/
theorem subs_preserves_nonempty_knownForbids {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  req.subst subsmap = some req' →
  ¬ (isAuthorizedPartial req entities policies).knownForbids.isEmpty →
  ¬ (isAuthorizedPartial req' (entities.subst subsmap) policies).knownForbids.isEmpty
:= by
  repeat rw [Set.non_empty_iff_exists]
  intro h₁ h₂
  replace ⟨pid, h₂⟩ := h₂
  exists pid
  exact subs_preserves_knownForbids h₁ h₂

/--
  helper lemma
-/
theorem partial_authz_decision_concrete_no_knownForbids_then_knownPermits_unknown_agnostic {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).knownForbids.isEmpty →
  (isAuthorizedPartial req entities policies).knownPermits.isEmpty = (isAuthorizedPartial req' (entities.subst subsmap) policies).knownPermits.isEmpty
:= by
  intro h₁ h₂ h₃
  cases h₄ : (isAuthorizedPartial req entities policies).knownPermits.isEmpty
  case true =>
    rcases PartialResponse.decision_concrete_then_kf_or_kp h₁ with h₅ | ⟨h₅, _⟩ | h₅
    case _ => contradiction
    case _ => contradiction
    case _ =>
      have h₆ := subs_preserves_empty_permits h₂ h₅
      apply Eq.symm
      by_contra h₇
      replace ⟨pid, h₇⟩ := (Set.non_empty_iff_exists _).mp h₇
      replace h₇ := PartialResponse.in_knownPermits_in_permits h₇
      rw [Set.empty_iff_not_exists] at h₆
      apply h₆ ; clear h₆
      exists pid
  case false =>
    unfold PartialResponse.knownPermits at *
    simp at *
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
    split at h₆ <;> simp at h₆
    subst h₆
    rename_i r pid
    simp at h₅
    apply h₅ ; clear h₅
    apply subs_preserves_true_residuals h₂ h₄

/--
  helper lemma
-/
theorem if_knownForbids_then_deny_after_any_sub {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  ¬ (isAuthorizedPartial req entities policies).knownForbids.isEmpty →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req' (entities.subst subsmap) policies).decision = .deny
:= by
  intro h₁ h₂
  unfold PartialResponse.decision
  simp
  intro h₃
  replace h₁ := subs_preserves_nonempty_knownForbids h₂ h₁
  contradiction

/--
  helper lemma
-/
theorem partial_authz_decision_concrete_no_knownForbids_some_permits_then_must_be_permits_after_any_sub {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).knownForbids.isEmpty →
  ¬ (isAuthorizedPartial req entities policies).permits.isEmpty →
  ¬ (isAuthorizedPartial req' (entities.subst subsmap) policies).permits.isEmpty
:= by
  intro h₁ h₂ h₃ h₄
  rcases PartialResponse.decision_concrete_then_kf_or_kp h₁ with h₅ | ⟨h₅, _⟩ | h₅
  case _ => contradiction
  case _ =>
    replace ⟨kp, h₅⟩ := (Set.non_empty_iff_exists _).mp h₅
    rw [Set.non_empty_iff_exists]
    exists kp
    apply PartialResponse.in_knownPermits_in_permits
    apply subs_preserves_knownPermits h₂
    assumption
  case _ => contradiction

/--
  helper lemma
-/
theorem partial_authz_decision_concrete_no_knownForbids_some_permits_then_no_knownForbids_after_any_sub {policies : Policies} {req req' : PartialRequest} {entities : PartialEntities} {subsmap : Map String PartialValue} :
  (isAuthorizedPartial req entities policies).decision ≠ .unknown →
  req.subst subsmap = some req' →
  (isAuthorizedPartial req entities policies).knownForbids.isEmpty →
  ¬ (isAuthorizedPartial req entities policies).permits.isEmpty →
  (isAuthorizedPartial req' (entities.subst subsmap) policies).knownForbids.isEmpty
:= by
  intro h₁ h₂ h₃ h₄
  rcases PartialResponse.decision_concrete_then_kf_or_kp h₁ with h₅ | ⟨_, h₆⟩ | h₅
  case _ => contradiction
  case _ =>
    apply PartialResponse.empty_forbids_empty_knownForbids
    apply subs_preserves_empty_forbids h₂ h₆
  case _ => contradiction
