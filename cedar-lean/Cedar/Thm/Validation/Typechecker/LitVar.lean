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

import Cedar.Thm.Validation.Typechecker.Basic
import Batteries.Tactic.Case

/-!
This file proves that typechecking of `.lit` and `.var` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

theorem type_of_lit_is_sound {l : Prim} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₃ : (typeOf (Expr.lit l) c₁ env) = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.lit l) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.lit l) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfLit] at h₃
  split at h₃ <;> simp [ok] at h₃
  case h_5;
  split at h₃ <;> try { simp [err] at h₃ }
  simp at h₃
  case h_5 =>
    have ⟨h₃, h₄⟩ := h₃
    subst c₂ ty
    apply And.intro empty_guarded_capabilities_invariant
    apply InstanceOfType.instance_of_entity
    simp only [InstanceOfEntityType, EntityUID.WellFormed, true_and]
    assumption
  all_goals {
    have ⟨h₃, h₄⟩ := h₃
    subst c₂ ty
    apply And.intro empty_guarded_capabilities_invariant
    first |
      exact true_is_instance_of_tt |
      exact false_is_instance_of_ff |
      apply InstanceOfType.instance_of_int |
      apply InstanceOfType.instance_of_string
  }


theorem type_of_val_is_sound {v : Value} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.val v) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.val v) c₂ request entities ∧
  ∃ w, EvaluatesTo (Expr.val v) request entities w ∧ InstanceOfType env w ty.typeOf
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf] at h₃
  -- typeOf (Expr.val v) c₁ env = typeOfVal v env, so we have typeOfVal v env = Except.ok (ty, c₂)
  have h₄ : typeOfVal v env = Except.ok (ty, c₂) := h₃
  -- We need to prove soundness by induction on the structure of v
  induction v using Value.rec generalizing ty c₂ with
  | prim p =>
    -- For primitive values, typeOfVal calls typeOfLit
    simp [typeOfVal] at h₄
    have h₅ : typeOfLit p env = Except.ok (ty, c₂) := h₄
    apply And.intro empty_guarded_capabilities_invariant
    exists (Value.prim p)
    apply And.intro
    · simp [EvaluatesTo, evaluate]
    · -- Use the soundness of typeOfLit
      have h₆ := type_of_lit_is_sound (by simp [typeOf, h₅])
      simp [EvaluatesTo, evaluate] at h₆
      exact h₆.right.right
  | set s ih =>
    -- For set values, we need to handle the recursive case
    simp [typeOfVal] at h₄
    apply And.intro empty_guarded_capabilities_invariant
    exists (Value.set s)
    apply And.intro
    · simp [EvaluatesTo, evaluate]
    · -- This would require proving that the set type is correct
      -- For now, we'll use sorry as this requires more complex reasoning
      sorry
  | record m ih =>
    -- For record values, similar to sets
    simp [typeOfVal] at h₄
    apply And.intro empty_guarded_capabilities_invariant
    exists (Value.record m)
    apply And.intro
    · simp [EvaluatesTo, evaluate]
    · -- This would require proving that the record type is correct
      sorry
  | ext e =>
    -- For extension values, typeOfVal calls typeOfExt
    simp [typeOfVal] at h₄
    apply And.intro empty_guarded_capabilities_invariant
    exists (Value.ext e)
    apply And.intro
    · simp [EvaluatesTo, evaluate]
    · -- This would require proving that the extension type is correct
      sorry

theorem type_of_var_is_sound {var : Var} {c₁ c₂ : Capabilities} {env : TypeEnv} {e' : TypedExpr} {request : Request} {entities : Entities}
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.var var) c₁ env = Except.ok (e', c₂)) :
  GuardedCapabilitiesInvariant (Expr.var var) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.var var) request entities v ∧ InstanceOfType env v e'.typeOf
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfVar] at h₃
  have hwf := h₂.wf_env
  have ⟨_, h₂, _⟩ := h₂
  simp [InstanceOfRequestType] at h₂
  cases var
  <;> simp [ok] at h₃
  <;> have ⟨h₃, h₄⟩ := h₃
  <;> subst c₂ e'
  <;> apply And.intro empty_guarded_capabilities_invariant
  case principal =>
    exists request.principal
    apply And.intro
    · simp [evaluate]
    · apply InstanceOfType.instance_of_entity
      simp only [h₂]
  case action =>
    exists request.action
    apply And.intro
    · simp [evaluate]
    · apply InstanceOfType.instance_of_entity
      simp only [h₂, InstanceOfEntityType, true_and]
      exact wf_env_implies_action_wf hwf
  case resource =>
    exists request.resource
    apply And.intro
    · simp [evaluate]
    · apply InstanceOfType.instance_of_entity
      simp only [h₂]
  case context =>
    exists request.context
    apply And.intro
    · simp [evaluate]
    · simp only [h₂, TypedExpr.typeOf]

end Cedar.Thm
