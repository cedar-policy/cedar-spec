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

import Cedar.Thm.Data.LT
import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.binaryApp .eq` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_eq_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .eq x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  match (asLit x₁ env), (asLit x₂ env) with
  | .some p₁, .some p₂ =>
    if p₁ = p₂ then ty.typeOf = (.bool .tt) else ty.typeOf = (.bool .ff)
  | _, _ =>
    ∃ ty₁ c₁ ty₂ c₂,
      typeOf x₁ c env = Except.ok (ty₁, c₁) ∧
      typeOf x₂ c env = Except.ok (ty₂, c₂) ∧
      match ty₁.typeOf ⊔ ty₂.typeOf with
      | .some _ => ty.typeOf = (.bool .anyBool)
      | .none   =>
        ty.typeOf = (.bool .ff) ∧
        ∃ ety₁ ety₂, ty₁.typeOf = .entity ety₁ ∧ ty₂.typeOf = .entity ety₂
:= by
  simp only [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp only [h₂, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  cases h₃ : typeOf x₂ c env <;> simp only [h₃, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  simp only [typeOfBinaryApp, typeOfEq, beq_iff_eq, ok, List.empty_eq, err] at h₁
  rename_i tc₁ tc₂
  split at h₁
  case h_1 hp₁ hp₂ =>
    simp only [hp₁, hp₂, List.empty_eq]
    simp only [Function.comp_apply] at h₁
    split at h₁ <;> (
      simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
      rename_i hp
      first
      | have hbty : ty.typeOf = .bool .ff := by simp only [←h₁, TypedExpr.typeOf]
      | have hbty : ty.typeOf = .bool .tt := by simp only [←h₁, TypedExpr.typeOf]
      simp only [h₁.right, hp, hbty, ↓reduceIte, and_self]
    )
  case h_2 h₄ =>
    split at h₁
    case h_1 h₅ =>
      simp only [Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₁
      replace ⟨h₁, h₁''⟩ := h₁ ; subst ty c'
      simp only [imp_false, List.empty_eq, CedarType.bool.injEq, Except.ok.injEq,
        exists_and_left, exists_and_right, true_and]
      exists tc₁.fst
      apply And.intro (by exists tc₁.snd)
      exists tc₂.fst
      apply And.intro (by exists tc₂.snd)
      simp only [h₅]
      simp only [TypedExpr.typeOf]
    case h_2 h₅ =>
      split at h₁ <;> simp only [Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq, reduceCtorEq] at h₁
      replace ⟨h₁, h₁''⟩ := h₁ ; subst ty c'
      simp only [List.empty_eq, CedarType.bool.injEq, reduceCtorEq, if_false_left, and_true,
        Except.ok.injEq, exists_and_left, exists_and_right, true_and]
      exists tc₁.fst
      apply And.intro (by exists tc₁.snd)
      exists tc₂.fst
      apply And.intro (by exists tc₂.snd)
      simp only [h₅]
      rename_i hety₁ hety₂
      and_intros
      · simp only [TypedExpr.typeOf]
      · simp only [hety₁, CedarType.entity.injEq, exists_eq']
      · simp only [hety₂, CedarType.entity.injEq, exists_eq']

theorem no_entity_type_lub_implies_not_eq {v₁ v₂ : Value} {ety₁ ety₂ : EntityType}
  (h₁ : InstanceOfType v₁ (CedarType.entity ety₁))
  (h₂ : InstanceOfType v₂ (CedarType.entity ety₂))
  (h₃ : (CedarType.entity ety₁ ⊔ CedarType.entity ety₂) = none) :
  ¬ v₁ = v₂
:= by
  by_contra h₄ ; subst h₄
  simp [lub?] at h₃
  apply h₃
  cases h₁ ; cases h₂
  rename_i h₄ h₅
  simp [InstanceOfEntityType] at h₄ h₅
  subst h₄ h₅
  contradiction

theorem as_lit_implies_lit_or_action {env : Environment} {x : Expr} {p : Prim}
  (hp : asLit x env = .some p) :
  (x = .var .action ∧ p = .entityUID env.reqty.action) ∨ x = .lit p
:= by
  simp only [asLit] at hp
  split at hp <;> simp only [reduceCtorEq, Option.some.injEq] at hp <;>
    simp only [hp, reduceCtorEq, and_self, or_true, or_false]

theorem type_of_eq_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .eq x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .eq x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .eq x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨hc, hty⟩ := type_of_eq_inversion h₃
  subst hc
  apply And.intro empty_guarded_capabilities_invariant
  split at hty
  case h_1 =>
    split at hty <;> rw [hty]
    case isTrue hp₁ hp₂ hpeq =>
      subst hpeq
      have he : evaluate (.binaryApp BinaryOp.eq x₁ x₂) request entities = .ok true := by
        simp [evaluate]
        replace hp₁ := as_lit_implies_lit_or_action hp₁
        replace hp₂ := as_lit_implies_lit_or_action hp₂
        have hact : request.action = env.reqty.action := h₂.left.right.left
        cases hp₁ <;> cases hp₂ <;> (
          rename_i p hp₁ hp₂
          try replace ⟨ hp₁, hp₁' ⟩ := hp₁
          try replace ⟨ hp₂, hp₂' ⟩ := hp₂
          try subst p
          subst x₁ x₂
          simp only [evaluate, hact, apply₂, Except.bind_ok, beq_self_eq_true]
        )
      simp [EvaluatesTo, he]
      exact true_is_instance_of_tt
    case isFalse hp₁ hp₂ hpeq =>
      have he : evaluate (.binaryApp BinaryOp.eq x₁ x₂) request entities = .ok false := by
        simp [evaluate]
        replace hp₁ := as_lit_implies_lit_or_action hp₁
        replace hp₂ := as_lit_implies_lit_or_action hp₂
        have hact : request.action = env.reqty.action := h₂.left.right.left
        cases hp₁ <;> cases hp₂ <;> (
          rename_i p₁ p₂ hp₁ hp₂
          try replace ⟨ hp₁, hp₁' ⟩ := hp₁
          try replace ⟨ hp₂, hp₂' ⟩ := hp₂
          try subst p₁
          try subst p₂
          subst x₁ x₂
          simp [evaluate, hpeq, hact, apply₂, Except.bind_ok, beq_self_eq_true]
          try simp at hpeq
        )
      simp [EvaluatesTo, he]
      exact false_is_instance_of_ff
  case h_2 =>
    replace ⟨ty₁, c₁', ty₂, c₂', ht₁, ht₂, hty⟩ := hty
    specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
    specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
    simp [EvaluatesTo, evaluate] at *
    cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
    cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
    try { simp [ih₁, ih₂] ; apply type_is_inhabited }
    replace ⟨ihl₁, ih₃⟩ := ih₁
    replace ⟨ihl₂, ih₄⟩ := ih₂
    rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
    simp [apply₂]
    split at hty
    case h_1 =>
      rw [hty]
      apply bool_is_instance_of_anyBool
    case h_2 heq =>
      have ⟨hty₀, ⟨ety₁, hty₁⟩, ⟨ety₂, hty₂⟩⟩ := hty ; clear hty
      rw [hty₁] at ih₃ heq
      rw [hty₂] at ih₄ heq
      have h₆ := no_entity_type_lub_implies_not_eq ih₃ ih₄ heq
      cases h₇ : v₁ == v₂ <;>
      simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Value.prim.injEq] at h₇
      case false => rw [hty₀]; exact false_is_instance_of_ff
      case true  => contradiction

end Cedar.Thm
