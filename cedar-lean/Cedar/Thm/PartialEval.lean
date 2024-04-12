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

import Cedar.Partial.Evaluator
import Cedar.Partial.Expr
import Cedar.Spec.Evaluator
import Cedar.Thm.PartialEval.And
import Cedar.Thm.PartialEval.Basic
import Cedar.Thm.PartialEval.Binary
import Cedar.Thm.PartialEval.Call
import Cedar.Thm.PartialEval.GetAttr
import Cedar.Thm.PartialEval.HasAttr
import Cedar.Thm.PartialEval.Ite
import Cedar.Thm.PartialEval.Or
import Cedar.Thm.PartialEval.Set
import Cedar.Thm.PartialEval.Unary
import Cedar.Thm.Data.Control
import Cedar.Thm.Utils

/-! This file contains theorems about Cedar's partial evaluator. -/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Partial (Unknown)
open Cedar.Spec (Error Result)
open Except

/--
  Partial evaluation with concrete inputs gives the same output as
  concrete evaluation with those inputs
-/
theorem partial_eval_on_concrete_eqv_concrete_eval {expr : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} :
  Partial.evaluate expr request entities = (Spec.evaluate expr request entities).map Partial.Value.value
:= by
  cases expr <;> simp only [Spec.Expr.asPartialExpr]
  case lit p => simp [Partial.evaluate, Spec.evaluate, Except.map]
  case var v =>
    unfold Partial.evaluate Spec.evaluate
    cases v <;> simp only [Spec.Request.asPartialRequest, Except.map]
    case context =>
      split
      case h_1 kvs h₁ =>
        simp
        rw [Map.mapOnValues_eq_make_map] at h₁
        rw [Map.eq_iff_kvs_equiv (wf₁ := by simp [Map.make_wf])]
        simp [List.Equiv, List.subset_def]
        have h₂ := mapM_some_iff_f_some_on_all_elements.mp (Option.isSome_iff_exists.mpr (Exists.intro kvs h₁))
        simp at h₂
        -- h₂ says, approximately, that context after wrapping in
        -- Partial.RestrictedValue.value doesn't have any residuals.
        -- We may not need it stated in that form.
        constructor
        case left =>
          intro kv h₃
          sorry
        case right =>
          intro kv h₃
          sorry
        all_goals sorry
      case h_2 =>
        sorry
  case and x₁ x₂ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    exact PartialEval.And.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂
  case or x₁ x₂ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    exact PartialEval.Or.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂
  case ite x₁ x₂ x₃ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    have ih₃ := @partial_eval_on_concrete_eqv_concrete_eval x₃ request entities
    exact PartialEval.Ite.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂ ih₃
  case unaryApp op x₁ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    exact PartialEval.Unary.partial_eval_on_concrete_eqv_concrete_eval ih₁
  case binaryApp op x₁ x₂ =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    have ih₂ := @partial_eval_on_concrete_eqv_concrete_eval x₂ request entities
    exact PartialEval.Binary.partial_eval_on_concrete_eqv_concrete_eval ih₁ ih₂
  case getAttr x₁ attr =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    exact PartialEval.GetAttr.partial_eval_on_concrete_eqv_concrete_eval ih₁
  case hasAttr x₁ attr =>
    have ih₁ := @partial_eval_on_concrete_eqv_concrete_eval x₁ request entities
    exact PartialEval.HasAttr.partial_eval_on_concrete_eqv_concrete_eval ih₁
  case set xs =>
    have ih : ∀ x ∈ xs, Partial.evaluate x request entities = (Spec.evaluate x request entities).map Partial.Value.value := by
      intro x h₁
      apply @partial_eval_on_concrete_eqv_concrete_eval x request entities
    exact PartialEval.Set.partial_eval_on_concrete_eqv_concrete_eval ih
  case record attrs =>
    sorry
  case call xfn args =>
    have ih : ∀ arg ∈ args, Partial.evaluate arg request entities = (Spec.evaluate arg request entities).map Partial.Value.value := by
      intro arg h₁
      apply @partial_eval_on_concrete_eqv_concrete_eval arg request entities
    exact PartialEval.Call.partial_eval_on_concrete_eqv_concrete_eval ih

/--
  Corollary to the above: partial evaluation with concrete inputs gives a
  concrete value (or an error)
-/
theorem partial_eval_on_concrete_gives_concrete {expr : Spec.Expr} {request : Spec.Request} {entities : Spec.Entities} :
  match Partial.evaluate expr request entities with
  | .ok (.value _) => true
  | .ok (.residual _) => false
  | .error _ => true
:= by
  simp [partial_eval_on_concrete_eqv_concrete_eval, Except.map]
  split <;> rename_i h <;> split at h <;> simp at h <;> trivial

/--
  If partial evaluation returns a residual, then that residual expression
  contains an unknown
-/
theorem residuals_contain_unknowns {expr : Partial.Expr} {request : Partial.Request} {entities : Partial.Entities}
  (wf_e : entities.AllWellFormed)
  (ih_e : Partial.Entities.ResidualsContainUnknowns entities)
  (ih_r : Partial.Request.ResidualsContainUnknowns request) :
  ∀ r,
  Partial.evaluate expr request entities = ok (.residual r) →
  r.containsUnknown
:= by
  cases expr
  case lit p =>
    unfold Partial.evaluate
    intro r h₁
    simp at h₁
  case unknown u =>
    unfold Partial.evaluate
    intro r h₁
    simp at h₁
    subst h₁
    unfold Partial.Expr.containsUnknown Partial.Expr.subexpressions
    simp [List.any_eq_true, Partial.Expr.isUnknown]
  case var v =>
    unfold Partial.evaluate
    intro r h₁
    cases v <;> simp at h₁
    case principal =>
      cases h₂ : request.principal <;> simp [h₂] at h₁
      case unknown u =>
        subst h₁
        simp [Partial.Expr.containsUnknown, Partial.Expr.subexpressions, Partial.Expr.isUnknown]
    case action =>
      cases h₂ : request.action <;> simp [h₂] at h₁
      case unknown u =>
        subst h₁
        simp [Partial.Expr.containsUnknown, Partial.Expr.subexpressions, Partial.Expr.isUnknown]
    case resource =>
      cases h₂ : request.resource <;> simp [h₂] at h₁
      case unknown u =>
        subst h₁
        simp [Partial.Expr.containsUnknown, Partial.Expr.subexpressions, Partial.Expr.isUnknown]
    case context =>
      unfold Partial.Request.ResidualsContainUnknowns at ih_r
      split at h₁ <;> simp at h₁
      case h_2 h₂ =>
        subst h₁
        simp [mapM_none_iff_f_none_on_some_element] at h₂
        replace ⟨kv, h₂, h₃⟩ := h₂
        split at h₃ <;> simp at h₃
        case h_2 r h₄ =>
          specialize ih_r kv.snd (Map.in_kvs_snd_in_values h₂)
          unfold Partial.Expr.containsUnknown Partial.Expr.subexpressions
          unfold Partial.RestrictedValue.ResidualsContainUnknowns at ih_r
          simp [h₄] at ih_r
          simp
          right
          simp [Partial.RestrictedExpr.containsUnknown] at ih_r
          have ⟨subx, h₅, h₆⟩ := ih_r ; clear ih_r
          exists subx.asPartialExpr
          constructor
          case right =>
            rw [← Partial.isUnknown_asPartialExpr]
            assumption
          case left =>
            rw [List.mem_join]
            exists kv.snd.asPartialExpr.subexpressions
            constructor
            case left =>
              simp [List.mem_map]
              exists kv
            case right =>
              simp [h₄, Partial.RestrictedValue.asPartialExpr]
              exact Partial.subexpressions_asPartialExpr h₅
  case and x₁ x₂ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf_e ih_e ih_r
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf_e ih_e ih_r
    rw [← Partial.Expr.ResidualsContainUnknowns] at *
    exact PartialEval.And.residuals_contain_unknowns ih₁ ih₂
  case or x₁ x₂ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf_e ih_e ih_r
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf_e ih_e ih_r
    rw [← Partial.Expr.ResidualsContainUnknowns] at *
    exact PartialEval.Or.residuals_contain_unknowns ih₁ ih₂
  case ite x₁ x₂ x₃ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf_e ih_e ih_r
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf_e ih_e ih_r
    have ih₃ := @residuals_contain_unknowns x₃ request entities wf_e ih_e ih_r
    rw [← Partial.Expr.ResidualsContainUnknowns] at *
    exact PartialEval.Ite.residuals_contain_unknowns ih₁ ih₂ ih₃
  case unaryApp op x₁ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf_e ih_e ih_r
    exact PartialEval.Unary.residuals_contain_unknowns ih₁
  case binaryApp op x₁ x₂ =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf_e ih_e ih_r
    have ih₂ := @residuals_contain_unknowns x₂ request entities wf_e ih_e ih_r
    rw [← Partial.Expr.ResidualsContainUnknowns] at *
    exact PartialEval.Binary.residuals_contain_unknowns ih₁ ih₂
  case getAttr x₁ attr =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf_e ih_e ih_r
    exact PartialEval.GetAttr.residuals_contain_unknowns wf_e ih₁ ih_e
  case hasAttr x₁ attr =>
    have ih₁ := @residuals_contain_unknowns x₁ request entities wf_e ih_e ih_r
    exact PartialEval.HasAttr.residuals_contain_unknowns ih₁
  case set xs =>
    have ih : ∀ x ∈ xs, @Partial.Expr.ResidualsContainUnknowns x request entities := by
      intro x h₁
      unfold Partial.Expr.ResidualsContainUnknowns
      apply @residuals_contain_unknowns x request entities wf_e ih_e ih_r
    exact PartialEval.Set.residuals_contain_unknowns ih
  case record attrs =>
    sorry
  case call xfn args =>
    have ih : ∀ arg ∈ args, @Partial.Expr.ResidualsContainUnknowns arg request entities := by
      intro arg h₁
      unfold Partial.Expr.ResidualsContainUnknowns
      apply @residuals_contain_unknowns arg request entities wf_e ih_e ih_r
    exact PartialEval.Call.residuals_contain_unknowns ih

/--
  If partial evaluation returns a concrete value, then it returns the same value
  after any substitution of unknowns
-/
theorem subst_preserves_evaluation_to_literal {expr : Partial.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {v : Spec.Value} {subsmap : Map Unknown Partial.RestrictedValue} :
  Partial.evaluate expr req entities = ok (.value v) →
  req.subst subsmap = some req' →
  Partial.evaluate (expr.subst subsmap) req' (entities.subst subsmap) = ok (.value v)
:= by
  unfold Partial.evaluate Partial.Expr.subst
  cases expr <;> simp <;> intro h₁ h₂
  case lit p => simp [h₁]
  case var v =>
    cases v <;> simp at *
    case principal | action | resource =>
      split at h₁ <;> simp at h₁
      subst h₁
      split <;> simp
      case _ h₃ _ _ h₄ =>
        -- invoke a lemma about Partial.Request.subst
        sorry
      case _ h₃ _ _ h₄ =>
        -- invoke a lemma about Partial.Request.subst
        sorry
    case context =>
      split at h₁ <;> simp at h₁
      case _ kvs h₃ =>
        subst h₁
        sorry
  case and x₁ x₂ =>
    sorry
  all_goals sorry

/--
  If partial evaluation returns an error, then it returns the same error
  after any substitution of unknowns
-/
theorem subst_preserves_errors {expr : Partial.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {e : Error} {subsmap : Map Unknown Partial.RestrictedValue} :
  req.subst subsmap = some req' →
  Partial.evaluate expr req entities = error e →
  Partial.evaluate (expr.subst subsmap) req' (entities.subst subsmap) = error e
:= by
  unfold Partial.evaluate Partial.Expr.subst
  cases expr <;> simp <;> intro h₁ h₂
  case var v =>
    cases v <;> simp at *
    case context => split at h₂ <;> simp at h₂
  case and x₁ x₂ =>
    sorry
  all_goals sorry

/--
  Corollary (contrapositive) of the above:
  If partial evaluation returns ok after any substitution of unknowns,
  then it must return ok before that substitution
-/
theorem subst_preserves_errors_mt {expr : Partial.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap : Map Unknown Partial.RestrictedValue} :
  req.subst subsmap = some req' →
  (Partial.evaluate (expr.subst subsmap) req' (entities.subst subsmap)).isOk →
  (Partial.evaluate expr req entities).isOk
:= by
  unfold Except.isOk Except.toBool
  intro h₁ h₂
  by_contra h₃
  split at h₃ <;> simp at h₃
  case _ e h₄ =>
    have h₅ := subst_preserves_errors h₁ h₄
    simp [h₅] at h₂

/--
  Re-evaluation with a substitution on the residual expression, is equivalent to
  substituting first and then evaluating on the original expression.
-/
theorem eval_on_residuals_eqv_substituting_first {expr : Partial.Expr} {req req' : Partial.Request} {entities : Partial.Entities} {subsmap: Map Unknown Partial.RestrictedValue} :
  req.subst subsmap = some req' →
  (Partial.evaluate expr req entities >>= λ residual => Partial.evaluate (residual.subst subsmap).asPartialExpr req' (entities.subst subsmap)) =
  Partial.evaluate (expr.subst subsmap) req' (entities.subst subsmap)
:= by
  sorry
