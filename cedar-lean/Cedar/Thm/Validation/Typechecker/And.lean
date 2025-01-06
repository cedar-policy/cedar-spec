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
This file proves that typechecking of `.and` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_and_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.and x₁ x₂) c env = Except.ok (ty, c')) :
  ∃ bty₁ c₁,
    (typeOf x₁ c env).typeOf = .ok (.bool bty₁, c₁) ∧
    if bty₁ = BoolType.ff
    then ty.typeOf = .bool BoolType.ff ∧ c' = ∅
    else ∃ bty₂ c₂,
      (typeOf x₂ (c ∪ c₁) env).typeOf = .ok (.bool bty₂, c₂) ∧
      if bty₂ = BoolType.ff
      then ty.typeOf = .bool BoolType.ff ∧ c' = ∅
      else ty.typeOf = .bool (lubBool bty₁ bty₂) ∧ c' = c₁ ∪ c₂
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at *
  rename_i res₁
  simp only [typeOfAnd, List.empty_eq] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  case ok.h_1 h₃ =>
    have ⟨ hl₁, hr₁ ⟩ := h₁
    subst hl₁ hr₁
    exists BoolType.ff, res₁.snd
    simp [ResultType.typeOf, Except.map, h₃]
  case ok.h_2 bty₁ h₃ h₄ =>
    exists bty₁, res₁.snd
    simp [h₄, ResultType.typeOf, Except.map]
    split ; contradiction
    cases h₄ : typeOf x₂ (c ∪ res₁.snd) env <;> simp [h₄] at *
    rename_i res₂
    split at h₁ <;> simp at h₁ <;>
    have ⟨hty, hc⟩ := h₁ <;> subst hty hc
    case isFalse.ok.h_1 hty₂ =>
      exists BoolType.ff, res₂.snd
    case isFalse.ok.h_2 hty₂ =>
      exists BoolType.tt, res₂.snd ; simp [←hty₂]
      cases bty₁ <;> simp at h₃ <;> simp [lubBool, TypedExpr.typeOf]
    case isFalse.ok.h_3 bty₂ h₄ h₅ hty₂ =>
      exists BoolType.anyBool, res₂.snd
      cases bty₂ <;> simp at *
      simp [hty₂, lubBool]
      split <;> rename_i h₆
      · simp [h₆, TypedExpr.typeOf]
      · rfl

theorem type_of_and_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.and x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.and x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.and x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨bty₁, rc₁, h₄, h₅⟩ := type_of_and_inversion h₃
  split_type_of h₄ ; rename_i h'₄ hl₄ hr₄
  specialize ih₁ h₁ h₂ h'₄
  have ⟨ih₁₁, v₁, ih₁₂, ih₁₃⟩ := ih₁
  rw [hl₄] at ih₁₃
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃
  subst hb₁
  split at h₅
  case isTrue h₆ =>
    subst h₆
    have ⟨hty, hc⟩ := h₅
    rw [hty, hc]
    apply And.intro empty_guarded_capabilities_invariant
    have h₇ := instance_of_ff_is_false ih₁₃
    simp at h₇ ; subst h₇
    simp [EvaluatesTo] at ih₁₂
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool] <;>
    try exact type_is_inhabited (CedarType.bool BoolType.ff)
    exact false_is_instance_of_ff
  case isFalse h₆ =>
    have ⟨bty₂, rc₂, hₜ, h₇⟩ := h₅
    split at h₇ <;> have ⟨hty, hc⟩ := h₇ <;> rw [hty, hc]
    case isTrue h₈ =>
      subst h₈
      apply And.intro empty_guarded_capabilities_invariant
      exists false ; simp [false_is_instance_of_ff]
      cases b₁
      case false =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool]
      case true =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool]
        simp [GuardedCapabilitiesInvariant] at ih₁₁
        specialize ih₁₁ ih₁₂
        have h₇ := capability_union_invariant h₁ ih₁₁
        split_type_of hₜ ; rename_i h'ₜ hlₜ hrₜ
        subst hr₄
        specialize ih₂ h₇ h₂ h'ₜ
        have ⟨_, v₂, ih₂₂, ih₂₃⟩ := ih₂
        simp [EvaluatesTo] at ih₂₂
        rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
        simp [Result.as, ih₂₂, Coe.coe, Value.asBool, Lean.Internal.coeM, pure, Except.pure]
        rw [hlₜ] at ih₂₃
        have h₈ := instance_of_ff_is_false ih₂₃
        subst h₈
        simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe, Coe.coe]
    case isFalse h₈ =>
      cases b₁
      case false =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
        try exact type_is_inhabited (CedarType.bool (lubBool bty₁ bty₂))
        apply instance_of_lubBool
        simp [ih₁₃]
      case true =>
        rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool, GuardedCapabilitiesInvariant] <;>
        try exact type_is_inhabited (CedarType.bool (lubBool bty₁ bty₂))
        simp [GuardedCapabilitiesInvariant] at ih₁₁
        specialize ih₁₁ ih₁₂
        split_type_of hₜ ; rename_i h'ₜ hlₜ hrₜ
        subst hr₄
        have h₇ := capability_union_invariant h₁ ih₁₁
        specialize ih₂ h₇ h₂ h'ₜ
        have ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩ := ih₂
        simp [EvaluatesTo] at ih₂₂
        rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
        simp [EvaluatesTo, evaluate, Result.as, ih₂₂, Coe.coe, Value.asBool, Lean.Internal.coeM, pure, Except.pure] <;>
        try exact type_is_inhabited (CedarType.bool (lubBool bty₁ bty₂))
        rw [hlₜ] at ih₂₃
        have ⟨b₂, hb₂⟩ := instance_of_bool_is_bool ih₂₃
        subst hb₂
        cases b₂ <;> simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe, Coe.coe]
        case false =>
          apply instance_of_lubBool ; simp [ih₂₃]
        case true =>
          apply And.intro
          · simp [GuardedCapabilitiesInvariant] at ih₂₁
            specialize ih₂₁ ih₂₂
            rw [hrₜ] at ih₂₁
            exact capability_union_invariant ih₁₁ ih₂₁
          · apply instance_of_lubBool ; simp [ih₁₃]

end Cedar.Thm
