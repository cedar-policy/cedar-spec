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

/-!
This file proves that typechecking of `.ite` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

theorem type_of_ite_inversion {x₁ x₂ x₃ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.ite x₁ x₂ x₃) c env = Except.ok (ty, c')) :
  ∃ bty₁ c₁ ty₂ c₂ ty₃ c₃,
    (typeOf x₁ c env).typeOf = .ok (.bool bty₁, c₁) ∧
    match bty₁ with
    | .ff      =>
      typeOf x₃ c env = .ok (ty₃, c₃) ∧ ty = ty₃ ∧ c' = c₃
    | .tt      =>
      typeOf x₂ (c ∪ c₁) env = .ok (ty₂, c₂) ∧
      ty = ty₂ ∧ c' = c₁ ∪ c₂
    | .anyBool =>
      typeOf x₂ (c ∪ c₁) env = .ok (ty₂, c₂) ∧
      typeOf x₃ c env = .ok (ty₃, c₃) ∧
      (ty₂.typeOf ⊔ ty₃.typeOf) = (.some ty.typeOf) ∧ c' = (c₁ ∪ c₂) ∩ c₃
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂, typeOfIf] at *
  simp [ResultType.typeOf, Except.map]
  rename_i res₁
  split at h₁ <;> try { simp [ok, err] at h₁ } <;>
  rename_i c₁ hr₁
  case ok.h_1 =>
    exists BoolType.tt, res₁.snd
    simp [hr₁]
    cases h₃ : typeOf x₂ (c ∪ res₁.snd) env <;> simp [h₃] at h₁
    rename_i res₂ ; simp [ok] at h₁
    have ⟨ht₂, hc₂⟩ := h₁
    exists res₂.fst, res₂.snd
    subst ht₂ hc₂
    simp [h₃, ←hr₁]
  case ok.h_2 =>
    exists BoolType.ff, res₁.snd
    simp [hr₁]
    exact h₁
  case ok.h_3 =>
    exists BoolType.anyBool, res₁.snd
    simp [hr₁]
    cases h₃ : typeOf x₂ (c ∪ res₁.snd) env <;> simp [h₃] at h₁
    cases h₄ : typeOf x₃ c env <;> simp [h₄] at h₁
    split at h₁ <;> simp [ok, err] at h₁
    rename_i res₂ res₃ _ ty' h₅
    have ⟨ht, hc⟩ := h₁
    subst ht hc
    exists res₂.fst, res₂.snd
    simp only [←hr₁, h₃, Except.ok.injEq, true_and]
    exists res₃.fst, res₃.snd

theorem type_of_ite_is_sound {x₁ x₂ x₃ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.ite x₁ x₂ x₃) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂)
  (ih₃ : TypeOfIsSound x₃) :
  GuardedCapabilitiesInvariant (Expr.ite x₁ x₂ x₃) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.ite x₁ x₂ x₃) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨bty₁, rc₁, ty₂, rc₂, ty₃, rc₃, h₄, h₅⟩ := type_of_ite_inversion h₃
  simp [ResultType.typeOf, Except.map] at h₄
  split at h₄ <;> simp at h₄
  specialize ih₁ h₁ h₂ (by rename_i h₆ ; rw [h₆])
  have ⟨ih₁₁, v₁, ih₁₂, ih₁₃⟩ := ih₁
  simp [h₄] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃
  subst hb₁
  cases bty₁ <;> simp at h₅
  case anyBool =>
    have ⟨h₅, h₆, ht, hc⟩ := h₅
    cases b₁
    case false =>
      rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
      simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
      try exact type_is_inhabited ty.typeOf
      specialize ih₃ h₁ h₂ h₆
      have ⟨ih₃₁, v₃, ih₃₂, ih₃₃⟩ := ih₃
      rcases ih₃₂ with ih₃₂ | ih₃₂ | ih₃₂ | ih₃₂ <;> simp [ih₃₂] <;>
      try exact type_is_inhabited ty.typeOf
      apply And.intro
      case left =>
        intro h₇ ; subst h₇ hc
        simp [GuardedCapabilitiesInvariant, ih₃₂] at ih₃₁
        apply capability_intersection_invariant
        simp [ih₃₁]
      case right =>
        apply instance_of_lub ht
        simp [ih₃₃]
    case true =>
      rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
      simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
      try exact type_is_inhabited ty.typeOf
      simp [GuardedCapabilitiesInvariant, ih₁₂] at ih₁₁
      have h₇ := capability_union_invariant h₁ ih₁₁
      cases h₄
      subst rc₁
      specialize ih₂ h₇ h₂ h₅
      have ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩ := ih₂
      apply And.intro
      case left =>
        intro h₈
        simp [GuardedCapabilitiesInvariant, h₈] at ih₂₁
        subst hc
        apply capability_intersection_invariant
        apply Or.inl
        exact capability_union_invariant ih₁₁ ih₂₁
      case right =>
        rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;> simp [ih₂₂] <;>
        try exact type_is_inhabited ty.typeOf
        apply instance_of_lub ht
        simp [ih₂₃]
  case tt =>
    have ⟨h₅, ht, hc⟩ := h₅
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
    try exact type_is_inhabited ty.typeOf
    have hb₁ := instance_of_tt_is_true ih₁₃
    simp at hb₁ ; subst hb₁ ; simp only [ite_true]
    simp [GuardedCapabilitiesInvariant, ih₁₂] at ih₁₁
    have h₆ := capability_union_invariant h₁ ih₁₁
    cases h₄
    subst rc₁
    specialize ih₂ h₆ h₂ h₅
    have ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩ := ih₂
    rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;> simp [ih₂₂] <;>
    try exact type_is_inhabited ty.typeOf
    subst ht hc ; simp [ih₂₃]
    intro h₇ ; subst h₇
    simp [GuardedCapabilitiesInvariant, ih₂₂] at ih₂₁
    exact capability_union_invariant ih₁₁ ih₂₁
  case ff =>
    have ⟨h₅, ht, hc⟩ := h₅
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
    try exact type_is_inhabited ty.typeOf
    have hb₁ := instance_of_ff_is_false ih₁₃
    simp at hb₁ ; simp [hb₁]
    specialize ih₃ h₁ h₂ h₅
    have ⟨ih₃₁, v₃, ih₃₂, ih₃₃⟩ := ih₃
    subst ht hc
    apply And.intro
    · simp [GuardedCapabilitiesInvariant] at ih₃₁
      exact ih₃₁
    · exists v₃

end Cedar.Thm
