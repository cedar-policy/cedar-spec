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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.unaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_not_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ bty c₁',
    ty = .bool bty.not ∧
    typeOf x₁ c₁ env = Except.ok (.bool bty, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case h_1 _ ty₁ bty _ =>
      simp [ok] at h₁
      apply And.intro
      case left => simp [h₁]
      case right =>
        exists bty, c₁'
        simp only [and_true, h₁]

theorem type_of_not_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp .not x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .not x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .not x₁) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₅, bty, c₁', h₆, h₄⟩ := type_of_not_inversion h₃
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inr.inr.inr =>
      cases bty
      case anyBool =>
        have ⟨b, h₈⟩ := instance_of_anyBool_is_bool h₇
        cases b <;>
        subst h₈ <;>
        simp [apply₁] <;>
        apply bool_is_instance_of_anyBool
      case tt =>
        have h₈ := instance_of_tt_is_true h₇
        subst h₈
        simp [apply₁, BoolType.not]
        exact false_is_instance_of_ff
      case ff =>
        have h₈ := instance_of_ff_is_false h₇
        subst h₈
        simp [apply₁, BoolType.not]
        exact true_is_instance_of_tt
    all_goals {
      exact type_is_inhabited (CedarType.bool (BoolType.not bty))
    }

theorem type_of_neg_inversion {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .int ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.int, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

theorem type_of_neg_is_sound {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp .neg x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp .neg x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp .neg x₁) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₅, h₆, c₁', h₄⟩ := type_of_neg_inversion h₃
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inr.inr.inr =>
      have ⟨i, h₈⟩ := instance_of_int_is_int h₇
      subst h₈
      simp [apply₁, intOrErr]
      cases h₉ : i.neg?
      case none =>
        simp only [or_false, or_true, true_and]
        exact type_is_inhabited CedarType.int
      case some i' =>
        simp only [Except.ok.injEq, false_or, exists_eq_left']
        apply InstanceOfType.instance_of_int
    all_goals {
      exact type_is_inhabited CedarType.int
    }

theorem type_of_like_inversion {x₁ : Expr} {p : Pattern} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ty = .bool .anyBool ∧
  ∃ c₁', typeOf x₁ c₁ env = Except.ok (.string, c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    simp [ok] at h₁
    simp [h₁]

theorem type_of_like_is_sound {x₁ : Expr} {p : Pattern} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp (.like p) x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.like p) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.like p) x₁) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₅, h₆, c₁', h₄⟩ := type_of_like_inversion h₃
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inr.inr.inr =>
      have ⟨s, h₈⟩ := instance_of_string_is_string h₇
      subst h₈
      simp [apply₁]
      exact bool_is_instance_of_anyBool (wildcardMatch s p)
    all_goals {
      exact type_is_inhabited (.bool .anyBool)
    }

theorem type_of_is_inversion {x₁ : Expr} {ety : EntityType} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂)) :
  c₂ = ∅ ∧
  ∃ ety' c₁',
    ty = (.bool (if ety = ety' then .tt else .ff)) ∧
    typeOf x₁ c₁ env = Except.ok (.entity ety', c₁')
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp [h₂] at h₁
  case ok res =>
    have ⟨ty₁, c₁'⟩ := res
    simp [typeOfUnaryApp] at h₁
    split at h₁ <;> try contradiction
    case h_4 _ _ ety' h₃ =>
      simp only [UnaryOp.is.injEq] at h₃
      subst h₃
      simp [ok] at h₁
      apply And.intro
      case left => simp [h₁]
      case right =>
        exists ety', c₁'
        simp only [h₁, and_self]

theorem type_of_is_is_sound {x₁ : Expr} {ety : EntityType} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp (.is ety) x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp (.is ety) x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp (.is ety) x₁) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨h₅, ety', c₁', h₆, h₄⟩ := type_of_is_inversion h₃
  subst h₅; subst h₆
  apply And.intro
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    have ⟨_, v₁, h₆, h₇⟩ := ih h₁ h₂ h₄ -- IH
    simp [EvaluatesTo] at h₆
    simp [EvaluatesTo, evaluate]
    rcases h₆ with h₆ | h₆ | h₆ | h₆ <;> simp [h₆]
    case inr.inr.inr =>
      have ⟨uid, h₈, h₉⟩ := instance_of_entity_type_is_entity h₇
      simp [apply₁, h₉, h₈]
      cases h₁₀ : ety == ety' <;>
      simp at h₁₀ <;>
      simp [h₁₀]
      case false => exact false_is_instance_of_ff
      case true => exact true_is_instance_of_tt
    all_goals {
      apply type_is_inhabited
    }

theorem type_of_unaryApp_is_sound {op₁ : UnaryOp} {x₁ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.unaryApp op₁ x₁) c₁ env = Except.ok (ty, c₂))
  (ih : TypeOfIsSound x₁) :
  GuardedCapabilitiesInvariant (Expr.unaryApp op₁ x₁) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.unaryApp op₁ x₁) request entities v ∧ InstanceOfType v ty
:= by
  match op₁ with
  | .not     => exact type_of_not_is_sound h₁ h₂ h₃ ih
  | .neg     => exact type_of_neg_is_sound h₁ h₂ h₃ ih
  | .like p  => exact type_of_like_is_sound h₁ h₂ h₃ ih
  | .is ety  => exact type_of_is_is_sound h₁ h₂ h₃ ih

end Cedar.Thm
