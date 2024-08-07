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
This file proves that typechecking of `.or` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_or_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : typeOf (Expr.or x₁ x₂) c env (l == .infinite) = Except.ok (ty, c')) :
  ∃ bty₁ c₁,
    typeOf x₁ c env (l == .infinite) = .ok (.bool bty₁, c₁) ∧
    if bty₁ = BoolType.tt
    then ty = .bool BoolType.tt ∧ c' = ∅
    else ∃ bty₂ c₂,
      typeOf x₂ c env (l == .infinite) = .ok (.bool bty₂, c₂) ∧
      if bty₁ = BoolType.ff
      then ty = .bool bty₂ ∧ c' = c₂
      else if bty₂ = BoolType.tt
      then ty = .bool BoolType.tt ∧ c' = ∅
      else if bty₂ = BoolType.ff
      then ty = .bool BoolType.anyBool ∧ c' = c₁
      else ty = .bool BoolType.anyBool ∧ c' = c₁ ∩ c₂
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env (l == .infinite) <;> simp [h₂] at *
  rename_i res₁
  simp [typeOfOr] at h₁
  split at h₁ <;> simp [ok, err] at h₁ <;>
  rename_i hr₁ <;> simp at hr₁ <;>
  have ⟨ht₁, hc₁⟩ := hr₁
  case ok.h_1 c₁  =>
    exists BoolType.tt, c₁
    have ⟨ht, hc⟩ := h₁
    simp [←ht₁, ←hc₁, hc, ←ht]
  case ok.h_2 c₁ =>
    cases h₃ : typeOf x₂ c env (l == .infinite) <;> simp [h₃] at *
    rename_i res₂
    split at h₁ <;> simp [ok, err] at h₁
    rename_i bty₂ hr₂
    have ⟨ht, hc⟩ := h₁
    subst ht hc
    exists BoolType.ff, c₁
    simp [←ht₁, ←hc₁]
    exists bty₂
    simp [←hr₂]
  case ok.h_3 bty₁ c₁ hneq₁ hneq₂ =>
    cases bty₁ <;> simp at hneq₁ hneq₂
    exists BoolType.anyBool, c₁
    simp [←ht₁, ←hc₁]
    cases h₃ : typeOf x₂ c env (l == .infinite) <;> simp [h₃] at *
    rename_i res₂
    split at h₁ <;> simp [ok, err] at h₁ <;>
    rename_i hr₂ <;>
    have ⟨ht, hc⟩ := h₁ <;> subst ht hc <;> simp
    case anyBool.ok.h_1 =>
      exists BoolType.tt, res₂.snd
      simp [←hr₂]
    case anyBool.ok.h_2 =>
      exists BoolType.ff, res₂.snd
      simp [←hr₂, ht₁, hc₁]
    case anyBool.ok.h_3 bty₂ hneq₁ hneq₂ =>
      exists bty₂, res₂.snd
      simp [←hr₂, ←ht₁, ←hc₁]
      cases bty₂ <;> simp at *

theorem type_of_or_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.or x₁ x₂) c₁ env (l == .infinite) = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.or x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.or x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨bty₁, rc₁, h₄, h₅⟩ := type_of_or_inversion h₃
  specialize ih₁ h₁ h₂ h₄
  have ⟨ih₁₁, v₁, ih₁₂, ih₁₃⟩ := ih₁
  have ⟨b₁, hb₁⟩ := instance_of_bool_is_bool ih₁₃ ; subst hb₁
  split at h₅
  case inl h₆ =>
    subst h₆
    have ⟨hty, hc⟩ := h₅ ; subst hty hc
    apply And.intro empty_guarded_capabilities_invariant
    have h₇ := instance_of_tt_is_true ih₁₃
    simp at h₇ ; subst h₇
    simp [EvaluatesTo] at ih₁₂
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    simp [EvaluatesTo, evaluate, Result.as, ih₁₂, Coe.coe, Value.asBool] <;>
    try exact type_is_inhabited (CedarType.bool BoolType.tt)
    exact true_is_instance_of_tt
  case inr =>
    have ⟨bty₂, rc₂, h₅', h₇⟩ := h₅
    specialize ih₂ h₁ h₂ h₅'
    have ⟨ih₂₁, v₂, ih₂₂, ih₂₃⟩ := ih₂
    have ⟨b₂, hb₂⟩ := instance_of_bool_is_bool ih₂₃
    subst hb₂
    simp [EvaluatesTo]
    cases b₁ <;>
    rcases ih₁₂ with ih₁₂ | ih₁₂ | ih₁₂ | ih₁₂ <;>
    rcases ih₂₂ with ih₂₂ | ih₂₂ | ih₂₂ | ih₂₂ <;>
    simp [evaluate, Result.as, Coe.coe, Value.asBool, ih₁₂, ih₂₂, GuardedCapabilitiesInvariant, Lean.Internal.coeM, pure, Except.pure] <;>
    try apply type_is_inhabited
    case false.inr.inr.inr.inr.inr.inr =>
      cases b₂ <;>
      simp [CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe, Coe.coe]
      case false h₆ =>
        cases bty₁ <;> simp at h₆ h₇
        case anyBool =>
          cases bty₂ <;> simp at h₇ <;>
          have ⟨h₇, _⟩ := h₇ <;> subst h₇ <;>
          try exact bool_is_instance_of_anyBool false
          exact ih₂₃
        case ff =>
          rw [h₇.left]
          exact ih₂₃
      case true h₆ =>
        cases bty₁ <;> cases bty₂ <;> simp at h₆ h₇ <;>
        have ⟨hty, hc⟩ := h₇ <;> simp [hty, hc] at *
        case ff.ff =>
          rcases ih₂₃ with ⟨_, _, ih₂₃⟩
          simp [InstanceOfBoolType] at ih₂₃
        case anyBool.ff =>
          rcases ih₂₃ with ⟨_, _, ih₂₃⟩
          simp [InstanceOfBoolType] at ih₂₃
        case anyBool.tt =>
          apply And.intro
          · apply empty_capabilities_invariant
          · exact true_is_instance_of_tt
        case anyBool.anyBool =>
          apply And.intro
          · simp [GuardedCapabilitiesInvariant, ih₂₂] at ih₂₁
            apply capability_intersection_invariant
            simp [ih₂₁]
          · apply bool_is_instance_of_anyBool
        all_goals {
          simp [GuardedCapabilitiesInvariant, ih₂₂] at ih₂₁
          simp [ih₂₁]
          first
            | apply true_is_instance_of_tt
            | apply bool_is_instance_of_anyBool
        }
    all_goals {
      simp [GuardedCapabilitiesInvariant] at ih₁₁ ih₂₁
      simp [ih₁₂] at ih₁₁ ; simp [ih₂₂] at ih₂₁
      rename_i h₆
      rcases ih₁₃ with ⟨_, _, ih₁₃⟩
      simp [InstanceOfBoolType] at ih₁₃
      cases bty₁ <;> simp at h₆ ih₁₃ h₇
      cases bty₂ <;> simp at h₇ <;>
      have ⟨ht, hc⟩ := h₇ <;> simp [ht, hc] at * <;>
      simp [true_is_instance_of_tt, bool_is_instance_of_anyBool] <;>
      try { apply empty_capabilities_invariant } <;>
      try { assumption }
      apply capability_intersection_invariant
      simp [ih₁₁, ih₂₁]
    }


end Cedar.Thm
