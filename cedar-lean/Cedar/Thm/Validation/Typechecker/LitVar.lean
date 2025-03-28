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

theorem type_of_lit_is_sound {l : Prim} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₃ : (typeOf (Expr.lit l) c₁ env) = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.lit l) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.lit l) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfLit] at h₃
  split at h₃ <;> simp [ok] at h₃
  case h_5;
  split at h₃ <;> try { simp [err] at h₃ }
  simp at h₃
  all_goals {
    have ⟨h₃, h₄⟩ := h₃
    subst c₂ ty
    apply And.intro empty_guarded_capabilities_invariant
    first |
      exact true_is_instance_of_tt |
      exact false_is_instance_of_ff |
      apply InstanceOfType.instance_of_int |
      apply InstanceOfType.instance_of_string |
      apply InstanceOfType.instance_of_entity; simp [InstanceOfEntityType]
  }

theorem type_of_lit_is_lit {p : Prim} {c₁ c₂ : Capabilities} {ty : TypedExpr} {env : Environment} :
  typeOf (.lit p) c₁ env = .ok (ty, c₂) →
  ∃ t, ty = (.lit p t)
:= by
  intro h
  simp [typeOf, typeOfLit] at h
  split at h <;> simp [ok] at h
  case _ =>
    rcases h with ⟨h, _⟩
    subst h
    exists (.bool .tt)
  case _ =>
    rcases h with ⟨h, _⟩
    subst h
    exists (.bool .ff)
  case _ =>
    rcases h with ⟨h, _⟩
    subst h
    exists .int
  case _ =>
    rcases h with ⟨h, _⟩
    subst h
    exists .string
  case _ uid =>
    split at h <;> simp [err] at h
    rcases h with ⟨h, _⟩
    subst h
    exists (.entity uid.ty)

theorem type_of_var_is_sound {var : Var} {c₁ c₂ : Capabilities} {env : Environment} {e' : TypedExpr} {request : Request} {entities : Entities}
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.var var) c₁ env = Except.ok (e', c₂)) :
  GuardedCapabilitiesInvariant (Expr.var var) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.var var) request entities v ∧ InstanceOfType v e'.typeOf
:= by
  simp [EvaluatesTo, evaluate]
  simp [typeOf, typeOfVar] at h₃
  have ⟨h₂, _⟩ := h₂
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
      simp only [h₂, InstanceOfEntityType]
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
