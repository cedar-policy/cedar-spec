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

import Cedar.Thm.Core.LT
import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.binaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_eq_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.binaryApp .eq x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  match x₁, x₂ with
  | .lit p₁, .lit p₂ =>
    if p₁ = p₂ then ty = (.bool .tt) else ty = (.bool .ff)
  | _, _ =>
    ∃ ty₁ c₁ ty₂ c₂,
      typeOf x₁ c env = Except.ok (ty₁, c₁) ∧
      typeOf x₂ c env = Except.ok (ty₂, c₂) ∧
      match ty₁ ⊔ ty₂ with
      | .some _ => ty = (.bool .anyBool)
      | .none   =>
        ty = (.bool .ff) ∧
        ∃ ety₁ ety₂, ty₁ = .entity ety₁ ∧ ty₂ = .entity ety₂
:= by
  simp [typeOf] at h₁ ; rename_i h₁'
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, typeOfEq, ok, err] at h₁
  rename_i tc₁ tc₂
  split at h₁
  case h_1 p₁ p₂ =>
    split at h₁ <;> simp at h₁ <;> simp [h₁] <;>
    rename_i h₄ <;> simp [h₄]
  case h_2 h₄ =>
    split at h₁
    case h_1 h₅ =>
      simp at h₁ ; simp [h₁]
      split
      case h_1 p₁ p₂ _ =>
        specialize h₄ p₁ p₂ ; simp at h₄
      case h_2 =>
        exists tc₁.fst
        constructor
        case left  => exists tc₁.snd
        case right =>
          exists tc₂.fst
          constructor
          case left  => exists tc₂.snd
          case right => simp [h₅]
    case h_2 h₅ =>
      split at h₁ <;> simp at h₁ ; simp [h₁]
      split
      case h_1 p₁ p₂ _ =>
        specialize h₄ p₁ p₂ ; simp at h₄
      case h_2 ety₁ ety₂ _ true_is_instance_of_tt _ _ _ _ =>
        exists tc₁.fst
        constructor
        case left  => exists tc₁.snd
        case right =>
          exists tc₂.fst
          constructor
          case left  => exists tc₂.snd
          case right =>
            simp [h₅]
            constructor
            case left  => exists ety₁
            case right => exists ety₂

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

theorem type_of_eq_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .eq x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .eq x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .eq x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_eq_inversion h₃) with ⟨hc, hty⟩
  subst hc
  constructor
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    split at hty
    case h_1 =>
      split at hty <;> subst hty
      case inl heq _ _ =>
        subst heq
        simp [EvaluatesTo, evaluate, apply₂]
        exact true_is_instance_of_tt
      case inr p₁ p₂ heq _ _ =>
        simp [EvaluatesTo, evaluate, apply₂]
        cases h₃ : Value.prim p₁ == Value.prim p₂ <;>
        simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Value.prim.injEq] at h₃
        case false => exact false_is_instance_of_ff
        case true  => contradiction
    case h_2 =>
      rcases hty with ⟨ty₁, c₁', ty₂, c₂', ht₁, ht₂, hty⟩
      specialize ih₁ h₁ h₂ ht₁ ; rcases ih₁ with ⟨_, v₁, ih₁⟩
      specialize ih₂ h₁ h₂ ht₂ ; rcases ih₂ with ⟨_, v₂, ih₂⟩
      simp [EvaluatesTo, evaluate] at *
      cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
      cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
      try { simp [ih₁, ih₂] ; apply type_is_inhabited }
      rcases ih₁ with ⟨ihl₁, ih₁⟩
      rcases ih₂ with ⟨ihl₂, ih₂⟩
      rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
      simp [apply₂]
      split at hty
      case h_1 =>
        rw [hty]
        apply bool_is_instance_of_anyBool
      case h_2 heq =>
        rcases hty with ⟨hty₀, ⟨ety₁, hty₁⟩, ⟨ety₂, hty₂⟩⟩
        subst hty₀ hty₁ hty₂
        rcases (no_entity_type_lub_implies_not_eq ih₁ ih₂ heq) with h₆
        cases h₇ : v₁ == v₂ <;>
        simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Value.prim.injEq] at h₇
        case false => exact false_is_instance_of_ff
        case true  => contradiction

theorem type_of_int_cmp_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : op₂ = .less ∨ op₂ = .lessEq)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .bool .anyBool ∧
  (∃ c₁, typeOf x₁ c env = Except.ok (.int, c₁)) ∧
  (∃ c₂, typeOf x₂ c env = Except.ok (.int, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp at h₂ ; simp [h₂]
    rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    constructor
    case left  => exists tc₁.snd ; simp [←h₅]
    case right => exists tc₂.snd ; simp [←h₆]
  }

theorem type_of_int_cmp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₀ : op₂ = .less ∨ op₂ = .lessEq)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_int_cmp_inversion h₀ h₃) with ⟨hc, hty, ht₁, ht₂⟩
  subst hc hty
  constructor
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases ht₁ with ⟨c₁', ht₁⟩
    rcases ht₂ with ⟨c₂', ht₂⟩
    specialize ih₁ h₁ h₂ ht₁ ; rcases ih₁ with ⟨_, v₁, ih₁⟩
    specialize ih₂ h₁ h₂ ht₂ ; rcases ih₂ with ⟨_, v₂, ih₂⟩
    simp [EvaluatesTo, evaluate] at *
    cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
    cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
    try { simp [ih₁, ih₂] ; exact type_is_inhabited (.bool .anyBool) }
    rcases ih₁ with ⟨ihl₁, ih₁⟩
    rcases ih₂ with ⟨ihl₂, ih₂⟩
    rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
    rcases (instance_of_int_is_int ih₁) with ⟨i₁, ih₁⟩
    rcases (instance_of_int_is_int ih₂) with ⟨i₂, ih₂⟩
    subst ih₁ ih₂
    rcases h₀ with h₀ | h₀
    all_goals {
      subst h₀
      simp [apply₂]
      apply bool_is_instance_of_anyBool
    }

theorem type_of_int_arith_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : op₂ = .add ∨ op₂ = .sub)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .int ∧
  (∃ c₁, typeOf x₁ c env = Except.ok (.int, c₁)) ∧
  (∃ c₂, typeOf x₂ c env = Except.ok (.int, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp at h₂ ; simp [h₂]
    rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    rcases h₂ with ⟨h₂, _⟩
    constructor
    case left  => exists tc₁.snd ; simp [←h₂, ←h₅]
    case right => exists tc₂.snd ; simp [←h₂, ←h₆]
  }

theorem type_of_int_arith_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₀ : op₂ = .add ∨ op₂ = .sub)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_int_arith_inversion h₀ h₃) with ⟨hc, hty, ht₁, ht₂⟩
  subst hc hty
  constructor
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases ht₁ with ⟨c₁', ht₁⟩
    rcases ht₂ with ⟨c₂', ht₂⟩
    specialize ih₁ h₁ h₂ ht₁ ; rcases ih₁ with ⟨_, v₁, ih₁⟩
    specialize ih₂ h₁ h₂ ht₂ ; rcases ih₂ with ⟨_, v₂, ih₂⟩
    simp [EvaluatesTo, evaluate] at *
    cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
    cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
    try { simp [ih₁, ih₂] ; exact type_is_inhabited .int }
    rcases ih₁ with ⟨ihl₁, ih₁⟩
    rcases ih₂ with ⟨ihl₂, ih₂⟩
    rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
    rcases (instance_of_int_is_int ih₁) with ⟨i₁, ih₁⟩
    rcases (instance_of_int_is_int ih₂) with ⟨i₂, ih₂⟩
    subst ih₁ ih₂
    rcases h₀ with h₀ | h₀ <;> subst h₀ <;> simp [apply₂, intOrErr]
    case inl =>
      cases h₄ : Int64.add? i₁ i₂ <;> simp [h₄]
      case none => exact type_is_inhabited CedarType.int
      case some => simp [InstanceOfType.instance_of_int]
    case inr =>
      cases h₄ : Int64.sub? i₁ i₂ <;> simp [h₄]
      case none => exact type_is_inhabited CedarType.int
      case some => simp [InstanceOfType.instance_of_int]

theorem type_of_contains_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.binaryApp .contains x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .bool .anyBool ∧
  ∃ ty₁ ty₂,
    (ty₁ ⊔ ty₂).isSome ∧
    (∃ c₁, typeOf x₁ c env = Except.ok (.set ty₁, c₁)) ∧
    (∃ c₂, typeOf x₂ c env = Except.ok (ty₂, c₂))
:= by
  simp [typeOf] at *
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, err, ok] at h₁
  split at h₁ <;> try contradiction
  simp [ifLubThenBool, err, ok] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
  simp [h₁]
  rename_i tc₁ tc₂ _ ty₁ ty₂ ty₃ _ h₄ _ _ h₅
  exists ty₃, tc₂.fst
  rw [lub_comm] at h₅
  simp [h₅, ←h₄]
  constructor
  case left  => exists tc₁.snd
  case right => exists tc₂.snd

theorem type_of_contains_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .contains x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .contains x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .contains x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_contains_inversion h₃) with ⟨hc, hty, ty₁, ty₂, _, ht₁, ht₂⟩
  subst hc hty
  constructor
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases ht₁ with ⟨c₁', ht₁⟩
    rcases ht₂ with ⟨c₂', ht₂⟩
    specialize ih₁ h₁ h₂ ht₁ ; rcases ih₁ with ⟨_, v₁, ih₁⟩
    specialize ih₂ h₁ h₂ ht₂ ; rcases ih₂ with ⟨_, v₂, ih₂⟩
    simp [EvaluatesTo, evaluate] at *
    cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
    cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
    try { simp [ih₁, ih₂] ; apply type_is_inhabited }
    rcases ih₁ with ⟨ihl₁, ih₁⟩
    rcases ih₂ with ⟨ihl₂, ih₂⟩
    rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
    rcases (instance_of_set_type_is_set ih₁) with ⟨s₁, ih₁⟩
    subst ih₁
    simp [apply₂]
    apply bool_is_instance_of_anyBool

theorem type_of_containsA_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : op₂ = .containsAll ∨ op₂ = .containsAny)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .bool .anyBool ∧
  ∃ ty₁ ty₂,
    (ty₁ ⊔ ty₂).isSome ∧
    (∃ c₁, typeOf x₁ c env = Except.ok (.set ty₁, c₁)) ∧
    (∃ c₂, typeOf x₂ c env = Except.ok (.set ty₂, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp [ifLubThenBool, err, ok] at h₂
    split at h₂ <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h₂
    simp [h₂]
    rename_i tc₁ tc₂ _ _ _ ty₁ ty₂ _ h₅ h₆ _ _ h₇
    exists ty₁, ty₂
    simp [h₇]
    constructor
    case left  => exists tc₁.snd ; simp [←h₅]
    case right => exists tc₂.snd ; simp [←h₆]
  }


theorem type_of_containsA_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₀ : op₂ = .containsAll ∨ op₂ = .containsAny)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_containsA_inversion h₀ h₃) with ⟨hc, hty, ty₁, ty₂, _, ht₁, ht₂⟩
  subst hc hty
  constructor
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases ht₁ with ⟨c₁', ht₁⟩
    rcases ht₂ with ⟨c₂', ht₂⟩
    specialize ih₁ h₁ h₂ ht₁ ; rcases ih₁ with ⟨_, v₁, ih₁⟩
    specialize ih₂ h₁ h₂ ht₂ ; rcases ih₂ with ⟨_, v₂, ih₂⟩
    simp [EvaluatesTo, evaluate] at *
    cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
    cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
    try { simp [ih₁, ih₂] ; apply type_is_inhabited }
    rcases ih₁ with ⟨ihl₁, ih₁⟩
    rcases ih₂ with ⟨ihl₂, ih₂⟩
    rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
    rcases (instance_of_set_type_is_set ih₁) with ⟨s₁, ih₁⟩
    rcases (instance_of_set_type_is_set ih₂) with ⟨s₂, ih₂⟩
    subst ih₁ ih₂
    rcases h₀ with h₀ | h₀
    all_goals {
      subst h₀
      simp [apply₂]
      apply bool_is_instance_of_anyBool
    }

theorem type_of_mem_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType}
  (h₁ : typeOf (Expr.binaryApp .mem x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ∃ (ety₁ ety₂ : EntityType),
    (∃ c₁, typeOf x₁ c env = Except.ok (.entity ety₁, c₁)) ∧
    (∃ c₂,
      (typeOf x₂ c env = Except.ok (.entity ety₂, c₂) ∧
       ty = .bool (typeOfInₑ ety₁ ety₂ x₁ x₂ env)) ∨
      (typeOf x₂ c env = Except.ok (.set (.entity ety₂), c₂) ∧
       ty = .bool (typeOfInₛ ety₁ ety₂ x₁ x₂ env)))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, ok] at h₁
  split at h₁ <;> try { contradiction }
  all_goals {
    simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
    simp [h₁]
    rename_i tc₁ tc₂ _ _ _ ety₁ ety₂ _ h₄ h₅
    exists ety₁
    constructor
    case left  => exists tc₁.snd ; simp [←h₄]
    case right => exists ety₂, tc₂.snd ; simp [←h₅, h₁]
  }

theorem entityUID?_some_implies_entity_lit {x : Expr} {euid : EntityUID}
  (h₁ : entityUID? x = some euid) :
  x = Expr.lit (.entityUID euid)
:= by
  simp [entityUID?] at h₁
  split at h₁ <;> simp at h₁ ; subst h₁ ; rfl


theorem actionUID?_some_implies_action_lit {x : Expr} {euid : EntityUID} {acts : ActionStore}
  (h₁ : actionUID? x acts = some euid) :
  x = Expr.lit (.entityUID euid) ∧
  acts.contains euid = true
:= by
  simp [actionUID?] at h₁
  cases h₂ : entityUID? x <;> simp [h₂] at h₁
  replace h₂ := entityUID?_some_implies_entity_lit h₂
  rename_i euid'
  rcases h₁ with ⟨h₀, h₁⟩
  subst h₀
  simp [h₁, h₂]

theorem entityUIDs?_some_implies_entity_lits {x : Expr} {euids : List EntityUID}
  (h₁ : entityUIDs? x = some euids) :
  x = Expr.set ((List.map (Expr.lit ∘ Prim.entityUID) euids))
:= by
  simp [entityUIDs?] at h₁
  split at h₁ <;> try simp at h₁
  rw [←List.mapM'_eq_mapM] at h₁ ; rename_i xs
  cases euids
  case nil =>
    cases hxs : xs <;> subst xs <;> simp at *
  case cons hd tl =>
    cases hxs : xs <;> subst xs <;> simp [pure, Except.pure] at *
    rename_i hd' tl'
    cases h₂ : entityUID? hd' <;> simp [h₂] at h₁
    cases h₃ : List.mapM' entityUID? tl' <;> simp [h₃] at h₁
    rcases h₁ with ⟨hhd, htl⟩ ; rw [eq_comm] at hhd htl ; subst hhd htl
    replace h₂ := entityUID?_some_implies_entity_lit h₂
    simp [h₂]
    rw [List.mapM'_eq_mapM] at h₃
    rcases (@entityUIDs?_some_implies_entity_lits (.set tl') tl) with h₄
    simp [entityUIDs?, h₃] at h₄
    exact h₄

theorem entity_type_in_false_implies_inₑ_false {euid₁ euid₂ : EntityUID} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfEntityTypeStore entities env.ets)
  (h₂ : EntityTypeStore.descendentOf env.ets euid₁.ty euid₂.ty = false) :
  inₑ euid₁ euid₂ entities = false
:= by
  simp [EntityTypeStore.descendentOf] at h₂
  simp [inₑ] ; by_contra h₃ ; simp at h₃
  rcases h₃ with h₃ | h₃
  case inl => subst h₃ ; simp at h₂
  case inr =>
  simp [Entities.ancestorsOrEmpty] at h₃
  split at h₃
  case h_1 data h₄ =>
    rw [Set.contains_prop_bool_equiv] at h₃
    rcases (h₁ euid₁ data h₄) with ⟨entry, h₂₁, _, h₂₂⟩
    specialize h₂₂ euid₂ h₃
    rw [←Set.contains_prop_bool_equiv] at h₂₂
    simp [h₂₁, h₂₂] at h₂
  case h_2 => simp [Set.contains, Set.elts, Set.empty] at h₃

theorem action_type_in_eq_action_inₑ (euid₁ euid₂ : EntityUID) {env : Environment} {entities : Entities}
  (h₁ : InstanceOfActionStore entities env.acts)
  (h₂ : env.acts.contains euid₁) :
  inₑ euid₁ euid₂ entities = ActionStore.descendentOf env.acts euid₁ euid₂
:= by
  simp [InstanceOfActionStore] at h₁
  simp [ActionStore.contains] at h₂
  cases h₃ : Map.find? env.acts euid₁ <;> simp [h₃] at h₂
  rename_i entry
  rcases (h₁ euid₁ entry h₃) with ⟨data, h₁₁, h₁₂⟩
  simp [inₑ, ActionStore.descendentOf, h₃, Entities.ancestorsOrEmpty, h₁₁]
  rcases h₄ : euid₁ == euid₂ <;> simp at h₄ <;> simp [h₄, h₁₂]

theorem type_of_mem_is_soundₑ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf x₁ c₁ env = Except.ok (CedarType.entity ety₁, c₁'))
  (h₄ : typeOf x₂ c₁ env = Except.ok (CedarType.entity ety₂, c₂'))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType v (CedarType.bool (typeOfInₑ ety₁ ety₂ x₁ x₂ env))
:= by
  rcases (ih₁ h₁ h₂ h₃) with ⟨_, v₁, hev₁, hty₁⟩
  rcases (ih₂ h₁ h₂ h₄) with ⟨_, v₂, hev₂, hty₂⟩
  simp [EvaluatesTo] at *
  simp [evaluate]
  cases h₅ : evaluate x₁ request entities <;> simp [h₅] at hev₁ <;> simp [h₅, hev₁] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₁ ; subst hev₁
  cases h₆ : evaluate x₂ request entities <;> simp [h₆] at hev₂ <;> simp [h₆, hev₂] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₂ ; subst hev₂
  replace hty₁ := instance_of_entity_type_is_entity hty₁
  rcases hty₁ with ⟨euid₁, hty₁, hty₁'⟩ ; subst hty₁ hty₁'
  replace hty₂ := instance_of_entity_type_is_entity hty₂
  rcases hty₂ with ⟨euid₂, hty₂, hty₂'⟩ ; subst hty₂ hty₂'
  simp [apply₂]
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]
  split <;> try simp only
  rename_i b bty  h₇ h₈ h₉
  simp [typeOfInₑ] at *
  rcases h₂ with ⟨_, hents, hacts⟩
  cases ha : actionUID? x₁ env.acts <;> simp [ha] at h₇ h₈ h₉
  case none =>
    cases hin : EntityTypeStore.descendentOf env.ets euid₁.ty euid₂.ty <;>
    simp [hin] at h₇ h₈ h₉
    simp [entity_type_in_false_implies_inₑ_false hents hin] at h₉
  case some =>
    cases he : entityUID? x₂ <;> simp [he] at h₇ h₈ h₉
    case none =>
      cases hin : EntityTypeStore.descendentOf env.ets euid₁.ty euid₂.ty <;>
      simp [hin] at h₇ h₈ h₉
      simp [entity_type_in_false_implies_inₑ_false hents hin] at h₉
    case some =>
      replace ha := actionUID?_some_implies_action_lit ha
      rcases ha with ⟨ha', ha⟩ ; subst ha'
      replace he := entityUID?_some_implies_entity_lit he ; subst he
      rename_i auid euid _ _
      simp [evaluate] at h₅ h₆ ; subst h₅ h₆
      rcases (action_type_in_eq_action_inₑ auid euid hacts ha) with h₁₀
      simp [h₁₀] at h₈ h₉
      cases heq : ActionStore.descendentOf env.acts auid euid <;> simp [heq] at h₈ h₉

theorem entity_set_type_implies_set_of_entities {vs : List Value} {ety : EntityType}
  (h₁ : InstanceOfType (Value.set (Set.mk vs)) (CedarType.set (CedarType.entity ety))) :
  ∃ (euids : List EntityUID),
    vs.mapM Value.asEntityUID = Except.ok euids ∧
    ∀ euid, euid ∈ euids → euid.ty = ety
:= by
  rw [←List.mapM'_eq_mapM]
  cases vs
  case nil =>
    simp [pure, Except.pure]
  case cons hd tl =>
    simp only [List.mapM'_cons]
    cases h₁ ; rename_i h₁
    rcases (h₁ hd) with h₂
    simp [Set.mem_cons_self] at h₂
    replace h₂ := instance_of_entity_type_is_entity h₂
    rcases h₂ with ⟨heuid, hdty, h₂⟩ ; subst h₂
    rw [Value.asEntityUID] ; simp
    rw [List.mapM'_eq_mapM]
    have h₃ : InstanceOfType (Value.set (Set.mk tl)) (CedarType.set (CedarType.entity ety)) := by
      apply InstanceOfType.instance_of_set
      intro v h₃
      apply h₁ v
      apply Set.mem_cons_of_mem
      exact h₃
    rcases (entity_set_type_implies_set_of_entities h₃) with ⟨tleuids, h₄, h₅⟩
    simp [h₄, pure, Except.pure, hdty]
    intro euid heuid
    apply h₅ euid heuid

theorem entity_type_in_false_implies_inₛ_false {euid : EntityUID} {euids : List EntityUID} {ety : EntityType} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfEntityTypeStore entities env.ets)
  (h₂ : EntityTypeStore.descendentOf env.ets euid.ty ety = false)
  (h₃ : ∀ euid, euid ∈ euids → euid.ty = ety) :
  Set.any (fun x => inₑ euid x entities) (Set.make euids) = false
:= by
  simp [InstanceOfEntityTypeStore] at h₁
  simp [EntityTypeStore.descendentOf] at h₂
  rw [Set.make_any_iff_any]
  by_contra h₄ ; simp at h₄
  rcases h₄ with ⟨euid', h₄, h₅⟩
  simp [inₑ] at h₅
  rcases h₅ with h₅ | h₅
  case inl =>
    subst h₅
    specialize h₃ euid h₄
    simp [h₃] at h₂
  case inr =>
    simp [Entities.ancestorsOrEmpty, Set.contains, Set.elts, Set.empty] at h₅
    cases h₆ : Map.find? entities euid <;> simp [h₆] at h₅
    rename_i data
    rcases (h₁ euid data h₆) with ⟨entry, h₁, _, h₇⟩
    specialize h₇ euid' h₅
    split at h₂ <;> try contradiction
    rename_i h₈
    specialize h₃ euid' h₄ ; subst h₃
    split at h₂ <;> rename_i h₉ <;> simp [h₁] at h₉
    subst h₉
    rcases (Set.in_set_in_list euid'.ty entry.ancestors h₇) with h₉
    simp [Set.contains, Set.elts] at h₂ h₉
    rw [←List.elem_iff] at h₉
    rw [h₂] at h₉
    contradiction


theorem mapM'_eval_lits_eq_prims {ps : List Prim} {vs : List Value} {request : Request} {entities : Entities}
  (h₁ : List.mapM' (evaluate · request entities) (List.map Expr.lit ps) = Except.ok vs) :
  vs = List.map Value.prim ps
:= by
  cases ps
  case nil =>
    simp [List.mapM', pure, Except.pure] at h₁
    subst h₁
    simp only [List.map_nil]
  case cons hd tl =>
    simp [List.mapM'] at h₁
    cases h₂ : evaluate (Expr.lit hd) request entities <;> simp [h₂] at h₁
    cases h₃ : List.mapM' (fun x => evaluate x request entities) (List.map Expr.lit tl) <;> simp [h₃] at h₁
    rename_i vhd vtl
    simp [pure, Except.pure] at h₁ ; subst h₁
    simp [List.map]
    constructor
    case left  => simp [evaluate] at h₂ ; simp [h₂]
    case right => apply mapM'_eval_lits_eq_prims h₃

theorem mapM'_asEntityUID_eq_entities {vs : List Value} {euids : List EntityUID}
  (h₁ : List.mapM' Value.asEntityUID vs = Except.ok euids) :
  vs = List.map (Value.prim ∘ Prim.entityUID) euids
:= by
  cases vs
  case nil =>
    simp [List.mapM', pure, Except.pure] at h₁
    subst h₁
    simp only [List.map_nil]
  case cons hd tl =>
    simp [List.mapM'] at h₁
    cases h₂ : Value.asEntityUID hd <;> simp [h₂] at h₁
    cases h₃ : List.mapM' Value.asEntityUID tl <;> simp [h₃] at h₁
    rename_i vhd vtl
    simp [pure, Except.pure] at h₁ ; subst h₁
    simp [List.map]
    constructor
    case left  =>
      simp [Value.asEntityUID] at h₂
      split at h₂ <;> simp at h₂
      rw [eq_comm] at h₂ ; subst h₂
      rfl
    case right =>
      apply mapM'_asEntityUID_eq_entities h₃

theorem evaluate_entity_set_eqv {vs : List Value} {euids euids' : List EntityUID} {request : Request} {entities : Entities}
  (h₁ : evaluate (Expr.set (List.map (Expr.lit ∘ Prim.entityUID) euids')) request entities =
        Except.ok (Value.set (Set.mk vs)))
  (h₂ : List.mapM Value.asEntityUID vs = Except.ok euids) :
  euids ≡ euids'
:= by
  simp [evaluate] at h₁
  cases h₃ : List.mapM₁ (List.map (Expr.lit ∘ Prim.entityUID) euids') fun x => evaluate x.val request entities <;> simp [h₃] at h₁
  rename_i vs'
  simp [List.mapM₁, List.attach, List.mapM_pmap_subtype (evaluate · request entities)] at h₃
  rw [←List.mapM'_eq_mapM, ←List.map_map] at h₃
  replace h₃ := mapM'_eval_lits_eq_prims h₃
  rw [List.map_map] at h₃
  rw [←List.mapM'_eq_mapM] at h₂
  replace h₂ := mapM'_asEntityUID_eq_entities h₂
  replace h₁ := Set.make_eqv h₁
  subst h₂ h₃
  simp [List.Equiv, List.subset_def] at *
  rcases h₁ with ⟨hl₁, hr₁⟩
  constructor
  case left  => apply hr₁
  case right => apply hl₁

theorem action_type_in_eq_action_inₛ {auid : EntityUID} {euids euids' : List EntityUID} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfActionStore entities env.acts)
  (h₂ : env.acts.contains auid)
  (h₃ : euids ≡ euids') :
  Set.any (fun x => inₑ auid x entities) (Set.make euids) ↔
  ∃ euid, euid ∈ euids' ∧ ActionStore.descendentOf env.acts auid euid
:= by
  rw [Set.make_any_iff_any]
  simp [ActionStore.contains] at h₂
  cases h₄ : Map.find? env.acts auid <;> simp [h₄] at h₂
  rename_i entry
  simp [InstanceOfActionStore] at h₁
  specialize h₁ auid entry
  constructor <;> intro h₄ <;> rename_i hfnd <;>
  simp [hfnd] at h₁ <;>
  rcases h₁ with ⟨data, hl₁, hr₁⟩
  case some.mp =>
    rw [List.any_eq_true] at h₄
    rcases h₄ with ⟨euid, h₄, h₅⟩
    exists euid
    rcases h₃ with ⟨h₃, _⟩
    simp [List.subset_def] at h₃
    specialize h₃ h₄ ; simp [h₃]
    simp [inₑ] at h₅
    rcases h₅ with h₅ | h₅
    case inl =>
      subst h₅ ; simp [ActionStore.descendentOf]
    case inr =>
      simp [ActionStore.descendentOf, hfnd]
      intro _
      simp [Entities.ancestorsOrEmpty, hl₁, hr₁] at h₅
      exact h₅
  case some.mpr =>
    rw [List.any_eq_true]
    rcases h₄ with ⟨euid, h₄, h₅⟩
    exists euid
    rcases h₃ with ⟨_, h₃⟩
    simp [List.subset_def] at h₃
    specialize h₃ h₄ ; simp [h₃]
    simp [ActionStore.descendentOf, hfnd] at h₅
    by_cases h₆ : auid = euid <;> simp [h₆] at h₅
    case pos =>
      subst h₆ ; simp [inₑ]
    case neg =>
      simp [inₑ, Entities.ancestorsOrEmpty, hl₁, hr₁, h₅]

theorem type_of_mem_is_soundₛ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf x₁ c₁ env = Except.ok (CedarType.entity ety₁, c₁'))
  (h₄ : typeOf x₂ c₁ env = Except.ok (CedarType.set (CedarType.entity ety₂), c₂'))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType v (CedarType.bool (typeOfInₛ ety₁ ety₂ x₁ x₂ env))
:= by
  rcases (ih₁ h₁ h₂ h₃) with ⟨_, v₁, hev₁, hty₁⟩
  rcases (ih₂ h₁ h₂ h₄) with ⟨_, v₂, hev₂, hty₂⟩
  simp [EvaluatesTo] at *
  simp [evaluate]
  cases h₅ : evaluate x₁ request entities <;> simp [h₅] at hev₁ <;> simp [h₅, hev₁] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₁ ; subst hev₁
  cases h₆ : evaluate x₂ request entities <;> simp [h₆] at hev₂ <;> simp [h₆, hev₂] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₂ ; subst hev₂
  rcases (instance_of_entity_type_is_entity hty₁) with ⟨euid, hty₁, hty₁'⟩ ; subst hty₁ hty₁'
  rcases (instance_of_set_type_is_set hty₂) with ⟨vs, hset⟩ ; subst hset
  cases vs ; rename_i vs
  simp [apply₂, inₛ]
  simp [Set.mapOrErr, Set.elts]
  rcases (entity_set_type_implies_set_of_entities hty₂) with ⟨euids, h₇, hty₇⟩
  simp [h₇]
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]
  split <;> try simp
  rename_i h₈ h₉ h₁₀
  rcases h₂ with ⟨_, hents, hacts⟩
  simp [typeOfInₛ] at *
  cases ha : actionUID? x₁ env.acts <;> simp [ha] at h₈ h₉ h₁₀
  case none =>
    cases hin : EntityTypeStore.descendentOf env.ets euid.ty ety₂ <;>
    simp [hin] at h₈ h₉ h₁₀
    simp [entity_type_in_false_implies_inₛ_false hents hin hty₇] at h₁₀
  case some =>
    cases he : entityUIDs? x₂ <;> simp [he] at h₈ h₉ h₁₀
    case none =>
      cases hin : EntityTypeStore.descendentOf env.ets euid.ty ety₂ <;>
      simp [hin] at h₈ h₉ h₁₀
      simp [entity_type_in_false_implies_inₛ_false hents hin hty₇] at h₁₀
    case some =>
      rcases (actionUID?_some_implies_action_lit ha) with ⟨ha', hac⟩ ; subst ha'
      rcases (entityUIDs?_some_implies_entity_lits he) with he ; subst he
      simp [evaluate] at h₅ ; rw [eq_comm] at h₅ ; subst h₅
      rename_i euids' _ _
      rcases (evaluate_entity_set_eqv h₆ h₇) with h₁₁
      rcases (action_type_in_eq_action_inₛ hacts hac h₁₁) with h₁₂
      cases h₁₃ : Set.any (fun x => inₑ euid x entities) (Set.make euids) <;>
      simp [h₁₃] at h₉ h₁₀ h₁₂
      case false =>
        apply h₁₀
        intro euid' hneg h₁₃
        specialize h₁₂ euid'
        simp [hneg, h₁₃] at h₁₂
      case true =>
        apply h₉
        intro h₁₃
        rcases h₁₂ with ⟨euid', hl₁₂, hr₁₂⟩
        specialize h₁₃ euid' hl₁₂
        simp [hr₁₂] at h₁₃

theorem type_of_mem_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .mem x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .mem x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .mem x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  rcases (type_of_mem_inversion h₃) with ⟨hc, ety₁, ety₂, ⟨c₁', h₄⟩ , c₂', h₅⟩
  subst hc
  constructor
  case left => exact empty_guarded_capabilities_invariant
  case right =>
    rcases h₅ with h₅ | h₅ <;>
    rcases h₅ with ⟨h₅, h₆⟩ <;> subst h₆
    case inl.intro =>
      apply type_of_mem_is_soundₑ h₁ h₂ h₄ h₅ ih₁ ih₂
    case inr.intro =>
      apply type_of_mem_is_soundₛ h₁ h₂ h₄ h₅ ih₁ ih₂

theorem type_of_binaryApp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  match op₂ with
  | .eq          => exact type_of_eq_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .less
  | .lessEq      => exact type_of_int_cmp_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .add
  | .sub         => exact type_of_int_arith_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .contains    => exact type_of_contains_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .containsAll
  | .containsAny => exact type_of_containsA_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .mem         => exact type_of_mem_is_sound h₁ h₂ h₃ ih₁ ih₂

end Cedar.Thm
