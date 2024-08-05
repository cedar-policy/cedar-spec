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
This file proves that typechecking of `.binaryApp` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_eq_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : typeOf (Expr.binaryApp .eq x₁ x₂) c env (l == Level.infinite) = Except.ok (ty, c')) :
  c' = ∅ ∧
  match x₁, x₂ with
  | .lit p₁, .lit p₂ =>
    if p₁ = p₂ then ty = (.bool .tt) else ty = (.bool .ff)
  | _, _ =>
    ∃ ty₁ c₁ ty₂ c₂,
      typeOf x₁ c env (l == Level.infinite) = Except.ok (ty₁, c₁) ∧
      typeOf x₂ c env (l == Level.infinite) = Except.ok (ty₂, c₂) ∧
      match ty₁ ⊔ ty₂ with
      | .some _ => ty = (.bool .anyBool)
      | .none   =>
        ty = (.bool .ff) ∧
        ∃ ety₁ l₁ ety₂ l₂, ty₁ = .entity ety₁ l₁ ∧ ty₂ = .entity ety₂ l₂
:= by
  simp [typeOf] at h₁ ; rename_i h₁'
  cases h₂ : typeOf x₁ c env (l == Level.infinite) <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env (l == Level.infinite) <;> simp [h₃] at h₁
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
        · exists tc₁.snd
        · exists tc₂.fst
          constructor
          · exists tc₂.snd
          · simp [h₅]
    case h_2 h₅ =>
      split at h₁ <;> simp at h₁ ; simp [h₁]
      split
      case h_1 p₁ p₂ _ =>
        specialize h₄ p₁ p₂ ; simp at h₄
      case h_2 ety₁ l₁ ety₂ l₂ _ true_is_instance_of_tt _ _ _ _ =>
        exists tc₁.fst
        constructor
        · exists tc₁.snd
        · exists tc₂.fst
          constructor
          · exists tc₂.snd
          · simp [h₅]
            constructor
            · exists ety₁ ; exists l₁
            · exists ety₂ ; exists l₂

theorem no_entity_type_lub_implies_not_eq {v₁ v₂ : Value} {ety₁ ety₂ : EntityType} {l₁ l₂ : Level}
  (h₁ : InstanceOfType v₁ (CedarType.entity ety₁ l₁))
  (h₂ : InstanceOfType v₂ (CedarType.entity ety₂ l₂))
  (h₃ : (CedarType.entity ety₁ l₁ ⊔ CedarType.entity ety₂ l₂) = none) :
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

theorem type_of_eq_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities}  {l : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .eq x₁ x₂) c₁ env (l == Level.infinite) = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .eq x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .eq x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨hc, hty⟩ := type_of_eq_inversion h₃
  subst hc
  apply And.intro empty_guarded_capabilities_invariant
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
      have ⟨hty₀, ⟨ety₁, l₁, hty₁⟩, ⟨ety₂, l₂, hty₂⟩⟩ := hty ; clear hty
      subst hty₀ hty₁ hty₂
      have h₆ := no_entity_type_lub_implies_not_eq ih₃ ih₄ heq
      cases h₇ : v₁ == v₂ <;>
      simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Value.prim.injEq] at h₇
      case false => exact false_is_instance_of_ff
      case true  => contradiction

theorem type_of_int_cmp_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : op₂ = .less ∨ op₂ = .lessEq)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env (l == Level.infinite) = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .bool .anyBool ∧
  (∃ c₁, typeOf x₁ c env (l == Level.infinite) = Except.ok (.int, c₁)) ∧
  (∃ c₂, typeOf x₂ c env (l == Level.infinite)= Except.ok (.int, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env (l == Level.infinite) <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env (l == Level.infinite) <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp at h₂ ; simp [h₂]
    rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    constructor
    · exists tc₁.snd ; simp [←h₅]
    · exists tc₂.snd ; simp [←h₆]
  }

theorem type_of_int_cmp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₀ : op₂ = .less ∨ op₂ = .lessEq)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env (l == Level.infinite) = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨hc, hty, ht₁, ht₂⟩ := type_of_int_cmp_inversion h₀ h₃
  subst hc hty
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; exact type_is_inhabited (.bool .anyBool) }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  have ⟨i₁, ih₁⟩ := instance_of_int_is_int ih₃
  have ⟨i₂, ih₂⟩ := instance_of_int_is_int ih₄
  subst ih₁ ih₂
  rcases h₀ with h₀ | h₀
  all_goals {
    subst h₀
    simp [apply₂]
    apply bool_is_instance_of_anyBool
  }

theorem type_of_int_arith_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env (l == Level.infinite) = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .int ∧
  (∃ c₁, typeOf x₁ c env (l == Level.infinite) = Except.ok (.int, c₁)) ∧
  (∃ c₂, typeOf x₂ c env (l == Level.infinite) = Except.ok (.int, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env (l == Level.infinite) <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env (l == Level.infinite) <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp at h₂ ; simp [h₂]
    rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    replace ⟨h₂, _⟩ := h₂
    constructor
    · exists tc₁.snd ; simp [←h₂, ←h₅]
    · exists tc₂.snd ; simp [←h₂, ←h₆]
  }

theorem type_of_int_arith_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₀ : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env (l == Level.infinite) = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨hc, hty, ht₁, ht₂⟩ := type_of_int_arith_inversion h₀ h₃
  subst hc hty
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; exact type_is_inhabited .int }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  have ⟨i₁, ih₁⟩ := instance_of_int_is_int ih₃
  have ⟨i₂, ih₂⟩ := instance_of_int_is_int ih₄
  subst ih₁ ih₂
  rcases h₀ with h₀ | h₀ | h₀ <;> subst h₀ <;> simp [apply₂, intOrErr]
  case inl =>
    cases h₄ : Int64.add? i₁ i₂ <;> simp [h₄]
    case none => exact type_is_inhabited CedarType.int
    case some => simp [InstanceOfType.instance_of_int]
  case inr.inl =>
    cases h₄ : Int64.sub? i₁ i₂ <;> simp [h₄]
    case none => exact type_is_inhabited CedarType.int
    case some => simp [InstanceOfType.instance_of_int]
  case inr.inr =>
    cases h₄ : Int64.mul? i₁ i₂ <;> simp [h₄]
    case none => exact type_is_inhabited CedarType.int
    case some => simp [InstanceOfType.instance_of_int]

theorem type_of_contains_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : typeOf (Expr.binaryApp .contains x₁ x₂) c env (l == .infinite) = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .bool .anyBool ∧
  ∃ ty₁ ty₂,
    (ty₁ ⊔ ty₂).isSome ∧
    (∃ c₁, typeOf x₁ c env (l == .infinite) = Except.ok (.set ty₁, c₁)) ∧
    (∃ c₂, typeOf x₂ c env (l == .infinite) = Except.ok (ty₂, c₂))
:= by
  simp [typeOf] at *
  cases h₂ : typeOf x₁ c env (l == .infinite) <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env (l == .infinite) <;> simp [h₃] at h₁
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
  · exists tc₁.snd
  · exists tc₂.snd

theorem type_of_contains_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .contains x₁ x₂) c₁ env (l == .infinite) = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .contains x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .contains x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨hc, hty, ty₁, ty₂, _, ht₁, ht₂⟩ := type_of_contains_inversion h₃
  subst hc hty
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; apply type_is_inhabited }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  have ⟨s₁, ih₁⟩ := instance_of_set_type_is_set ih₃
  subst ih₁
  simp [apply₂]
  apply bool_is_instance_of_anyBool

theorem type_of_containsA_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : op₂ = .containsAll ∨ op₂ = .containsAny)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env (l == .infinite) = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty = .bool .anyBool ∧
  ∃ ty₁ ty₂,
    (ty₁ ⊔ ty₂).isSome ∧
    (∃ c₁, typeOf x₁ c env (l == .infinite) = Except.ok (.set ty₁, c₁)) ∧
    (∃ c₂, typeOf x₂ c env (l == .infinite) = Except.ok (.set ty₂, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env (l == .infinite) <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env (l == .infinite) <;> simp [h₄] at h₂
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
    · exists tc₁.snd ; simp [←h₅]
    · exists tc₂.snd ; simp [←h₆]
  }


theorem type_of_containsA_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₀ : op₂ = .containsAll ∨ op₂ = .containsAny)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env (l == .infinite) = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨hc, hty, ty₁, ty₂, _, ht₁, ht₂⟩ := type_of_containsA_inversion h₀ h₃
  subst hc hty
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; apply type_is_inhabited }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  have ⟨s₁, ih₁⟩ := instance_of_set_type_is_set ih₃
  have ⟨s₂, ih₂⟩ := instance_of_set_type_is_set ih₄
  subst ih₁ ih₂
  rcases h₀ with h₀ | h₀
  all_goals {
    subst h₀
    simp [apply₂]
    apply bool_is_instance_of_anyBool
  }

theorem type_of_mem_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : CedarType} {l : Level}
  (h₁ : typeOf (Expr.binaryApp .mem x₁ x₂) c env (l == .infinite) = Except.ok (ty, c')) :
  c' = ∅ ∧
  ∃ (ety₁ ety₂ : EntityType) (l₁ l₂ : Level),
    (∃ c₁, typeOf x₁ c env (l == .infinite) = Except.ok (.entity ety₁ l₁, c₁)) ∧
    (∃ c₂,
      (typeOf x₂ c env (l == .infinite) = Except.ok (.entity ety₂ l₂, c₂) ∧
       .ok (ty, ∅) = typeOfInₑ ety₁ ety₂ l₁ x₁ x₂ env) ∨
      (typeOf x₂ c env (l == .infinite) = Except.ok (.set (.entity ety₂ l₂), c₂) ∧
       .ok (ty, ∅) = typeOfInₛ ety₁ ety₂ l₁ x₁ x₂ env))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env (l == .infinite) <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env (l == .infinite) <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, ok] at h₁
  split at h₁
    <;> try { contradiction }
    <;> rename_i tc₁ tc₂ op ty₁ ty₂ ety₁ l₁ ety₂ l₂ _ heq₁ heq₂
  all_goals {
    try unfold typeOfInₑ at h₁
    try unfold typeOfInₛ at h₁

    split at h₁ <;> try contradiction
    rename_i hlt
    injection h₁
    rename_i heq₃
    injection heq₃
    rename_i heq₃ heq₄
    rw [← heq₄]
    constructor
    simp
    exists ety₁
    exists ety₂
    exists l₁
    exists l₂
    constructor
    case inl.right.left =>
      exists tc₁.snd
      simp
      rw [← heq₁]
    case inl.right.right =>
      exists tc₂.snd
      try (
        apply Or.inl ;
        constructor ;
        rw [← heq₂]
        rw [← heq₃]
        unfold typeOfInₑ
        rw [if_pos]
        simp [ok, Functor.map, Except.map]
        apply hlt
      )
      try (
        apply Or.inr
        constructor
        rw [← heq₂]
        unfold typeOfInₛ
        rw [if_pos]
        simp [Prod.fst, Functor.map, Except.map, ok]
        rw [heq₃]
        apply hlt
      )
  }

theorem entityUID?_some_implies_entity_lit {x : Expr} {euid : EntityUID}
  (h₁ : entityUID? x = some euid) :
  x = Expr.lit (.entityUID euid)
:= by
  simp [entityUID?] at h₁
  split at h₁ <;> simp at h₁ ; subst h₁ ; rfl


theorem actionUID?_some_implies_action_lit {x : Expr} {euid : EntityUID} {acts : ActionSchema}
  (h₁ : actionUID? x acts = some euid) :
  x = Expr.lit (.entityUID euid) ∧
  acts.contains euid = true
:= by
  simp [actionUID?] at h₁
  cases h₂ : entityUID? x <;> simp [h₂] at h₁
  replace h₂ := entityUID?_some_implies_entity_lit h₂
  rename_i euid'
  replace ⟨h₀, h₁⟩ := h₁
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
    have ⟨hhd, htl⟩ := h₁ ; clear h₁ ; rw [eq_comm] at hhd htl ; subst hhd htl
    replace h₂ := entityUID?_some_implies_entity_lit h₂
    simp [h₂]
    rw [List.mapM'_eq_mapM] at h₃
    have h₄ := @entityUIDs?_some_implies_entity_lits (.set tl') tl
    simp [entityUIDs?, h₃] at h₄
    exact h₄

theorem entity_type_in_false_implies_inₑ_false {euid₁ euid₂ : EntityUID} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfEntitySchema entities env.ets)
  (h₂ : EntitySchema.descendentOf env.ets euid₁.ty euid₂.ty = false) :
  inₑ euid₁ euid₂ entities = false
:= by
  simp only [EntitySchema.descendentOf, Bool.if_true_left, Bool.or_eq_false_iff,
    decide_eq_false_iff_not] at h₂
  simp only [inₑ, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  by_contra h₃
  simp only [not_and, Bool.not_eq_false] at h₃
  simp only [not_and, Bool.not_eq_false, ← Classical.or_iff_not_imp_right] at h₃
  rcases h₃ with h₃ | h₃
  case inr => subst h₃ ; simp at h₂
  case inl =>
  simp [Entities.ancestorsOrEmpty] at h₃
  split at h₃
  case h_1 data h₄ =>
    rw [Set.contains_prop_bool_equiv] at h₃
    have ⟨entry, h₂₁, _, h₂₂⟩ := h₁ euid₁ data h₄
    specialize h₂₂ euid₂ h₃
    rw [←Set.contains_prop_bool_equiv] at h₂₂
    simp [h₂₁, h₂₂] at h₂
  case h_2 => simp [Set.contains, Set.elts, Set.empty] at h₃

theorem action_type_in_eq_action_inₑ (euid₁ euid₂ : EntityUID) {env : Environment} {entities : Entities}
  (h₁ : InstanceOfActionSchema entities env.acts)
  (h₂ : env.acts.contains euid₁) :
  inₑ euid₁ euid₂ entities = ActionSchema.descendentOf env.acts euid₁ euid₂
:= by
  simp [InstanceOfActionSchema] at h₁
  simp [ActionSchema.contains] at h₂
  cases h₃ : Map.find? env.acts euid₁ <;> simp [h₃] at h₂
  rename_i entry
  have ⟨data, h₁₁, h₁₂⟩ := h₁ euid₁ entry h₃
  simp [inₑ, ActionSchema.descendentOf, h₃, Entities.ancestorsOrEmpty, h₁₁]
  rcases h₄ : euid₁ == euid₂ <;> simp at h₄ <;> simp [h₄, h₁₂]

theorem type_of_mem_is_soundₑ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType} {ty : CedarType} {l l₁ l₂ : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf x₁ c₁ env (l == .infinite) = Except.ok (CedarType.entity ety₁ l₁, c₁'))
  (h₄ : typeOf x₂ c₁ env (l == .infinite) = Except.ok (CedarType.entity ety₂ l₂, c₂'))
  (h₅ : .ok (ty,∅) = typeOfInₑ ety₁ ety₂ l₁ x₁ x₂ env)
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType v ty
:= by
  have ⟨_, v₁, hev₁, hty₁⟩ := ih₁ h₁ h₂ h₃
  have ⟨_, v₂, hev₂, hty₂⟩ := ih₂ h₁ h₂ h₄
  simp [EvaluatesTo] at *
  simp [evaluate]
  cases h₅ : evaluate x₁ request entities <;> simp [h₅] at hev₁ <;> simp [h₅, hev₁] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₁ ; subst hev₁
  cases h₆ : evaluate x₂ request entities <;> simp [h₆] at hev₂ <;> simp [h₆, hev₂] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₂ ; subst hev₂
  replace hty₁ := instance_of_entity_type_is_entity hty₁
  replace ⟨euid₁, hty₁, hty₁'⟩ := hty₁
  subst hty₁ hty₁'
  replace hty₂ := instance_of_entity_type_is_entity hty₂
  replace ⟨euid₂, hty₂, hty₂'⟩ := hty₂
  subst hty₂ hty₂'
  simp [apply₂]

  unfold typeOfInₑ at h₅
  split at h₅ <;> try contradiction
  rename_i hgt
  simp [ok] at h₅
  subst h₅
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]
  split <;> try simp only
  rename_i b bty  h₇ h₈ h₉
  simp [typeOfInₑ] at *
  have ⟨_, hents, hacts⟩ := h₂ ; clear h₂
  unfold typeOfInₑ.type at h₇ h₈ h₉
  cases hₐ : actionUID? x₁ env.acts <;> simp [hₐ] at h₇ h₈ h₉
  case none =>
    cases hin : EntitySchema.descendentOf env.ets euid₁.ty euid₂.ty
    case _ =>
      rw [entity_type_in_false_implies_inₑ_false] at h₉
      have h₁₀ := h₉ (by rfl)
      rw [hin] at h₁₀
      contradiction
      apply hents
      apply hin
    case _ =>
      rw [h₇] at hin
      contradiction
  case some =>
    cases he : entityUID? x₂ <;> simp [he] at h₇ h₈ h₉
    case none =>
      cases hin : EntitySchema.descendentOf env.ets euid₁.ty euid₂.ty <;>
      simp [hin] at h₇ h₈ h₉
      simp [entity_type_in_false_implies_inₑ_false hents hin] at h₉
    case some =>
      replace ⟨hₐ, hₐ'⟩ := actionUID?_some_implies_action_lit hₐ
      subst hₐ
      replace he := entityUID?_some_implies_entity_lit he ; subst he
      rename_i auid euid _ _
      simp [evaluate] at h₅ h₆ ; subst h₅ h₆
      have h₁₀ := action_type_in_eq_action_inₑ auid euid hacts hₐ'
      simp [h₁₀] at h₈ h₉
      cases heq : ActionSchema.descendentOf env.acts auid euid <;> simp [heq] at h₈ h₉

theorem entity_set_type_implies_set_of_entities {vs : List Value} {ety : EntityType} {l : Level}
  (h₁ : InstanceOfType (Value.set (Set.mk vs)) (CedarType.set (CedarType.entity ety l))) :
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
    have h₂ := h₁ hd
    simp [Set.mem_cons_self] at h₂
    replace ⟨heuid, hdty, h₂⟩ := instance_of_entity_type_is_entity h₂
    subst h₂
    rw [Value.asEntityUID] ; simp only [Except.bind_ok]
    rw [List.mapM'_eq_mapM]
    have h₃ : InstanceOfType (Value.set (Set.mk tl)) (CedarType.set (CedarType.entity ety l)) := by
      apply InstanceOfType.instance_of_set
      intro v h₃
      apply h₁ v
      apply Set.mem_cons_of_mem
      exact h₃
    have ⟨tleuids, h₄, h₅⟩ := entity_set_type_implies_set_of_entities h₃
    simp [h₄, pure, Except.pure, hdty]
    intro euid heuid
    apply h₅ euid heuid

theorem entity_type_in_false_implies_inₛ_false {euid : EntityUID} {euids : List EntityUID} {ety : EntityType} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfEntitySchema entities env.ets)
  (h₂ : EntitySchema.descendentOf env.ets euid.ty ety = false)
  (h₃ : ∀ euid, euid ∈ euids → euid.ty = ety) :
  Set.any (fun x => inₑ euid x entities) (Set.make euids) = false
:= by
  simp only [InstanceOfEntitySchema] at h₁
  simp only [EntitySchema.descendentOf] at h₂
  rw [Set.make_any_iff_any]
  by_contra h₄
  simp only [Bool.not_eq_false, List.any_eq_true] at h₄
  replace ⟨euid', h₄, h₅⟩ := h₄
  simp only [inₑ, Bool.or_eq_true, beq_iff_eq] at h₅
  rcases h₅ with h₅ | h₅
  case inl =>
    subst h₅
    specialize h₃ euid h₄
    simp [h₃] at h₂
  case inr =>
    simp only [Set.contains, Set.elts, Entities.ancestorsOrEmpty, Set.empty, List.elem_eq_mem,
      decide_eq_true_eq] at h₅
    cases h₆ : Map.find? entities euid <;>
    simp only [h₆, List.not_mem_nil] at h₅
    rename_i data
    replace ⟨entry, h₁, _, h₇⟩ := h₁ euid data h₆
    specialize h₇ euid' h₅
    split at h₂ <;> try contradiction
    rename_i h₈
    specialize h₃ euid' h₄ ; subst h₃
    split at h₂ <;> rename_i h₉ <;> simp [h₁] at h₉
    subst h₉
    rw [← Set.in_list_iff_in_set] at h₇
    simp only [Set.contains, Set.elts] at h₂ h₇
    rw [← List.elem_iff] at h₇
    rw [h₂] at h₇
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
    · simp [evaluate] at h₂ ; simp [h₂]
    · exact mapM'_eval_lits_eq_prims h₃

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
    · simp [Value.asEntityUID] at h₂
      split at h₂ <;> simp at h₂
      rw [eq_comm] at h₂ ; subst h₂
      rfl
    · exact mapM'_asEntityUID_eq_entities h₃

theorem evaluate_entity_set_eqv {vs : List Value} {euids euids' : List EntityUID} {request : Request} {entities : Entities}
  (h₁ : evaluate (Expr.set (List.map (Expr.lit ∘ Prim.entityUID) euids')) request entities =
        Except.ok (Value.set (Set.mk vs)))
  (h₂ : List.mapM Value.asEntityUID vs = Except.ok euids) :
  euids ≡ euids'
:= by
  simp only [evaluate] at h₁
  cases h₃ : List.mapM₁ (List.map (Expr.lit ∘ Prim.entityUID) euids') fun x => evaluate x.val request entities <;> simp [h₃] at h₁
  rename_i vs'
  simp only [List.mapM₁, List.attach_def,
    List.mapM_pmap_subtype (evaluate · request entities)] at h₃
  rw [←List.mapM'_eq_mapM, ←List.map_map] at h₃
  replace h₃ := mapM'_eval_lits_eq_prims h₃
  rw [List.map_map] at h₃
  rw [←List.mapM'_eq_mapM] at h₂
  replace h₂ := mapM'_asEntityUID_eq_entities h₂
  replace h₁ := Set.make_mk_eqv h₁
  subst h₂ h₃
  simp [List.Equiv, List.subset_def] at *
  have ⟨hl₁, hr₁⟩ := h₁
  constructor
  · apply hr₁
  · apply hl₁

theorem action_type_in_eq_action_inₛ {auid : EntityUID} {euids euids' : List EntityUID} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfActionSchema entities env.acts)
  (h₂ : env.acts.contains auid)
  (h₃ : euids ≡ euids') :
  Set.any (fun x => inₑ auid x entities) (Set.make euids) ↔
  ∃ euid, euid ∈ euids' ∧ ActionSchema.descendentOf env.acts auid euid
:= by
  rw [Set.make_any_iff_any]
  simp only [ActionSchema.contains] at h₂
  cases h₄ : Map.find? env.acts auid <;> simp [h₄] at h₂
  rename_i entry
  simp only [InstanceOfActionSchema] at h₁
  specialize h₁ auid entry
  constructor <;> intro h₄ <;> rename_i hfnd <;>
  simp only [hfnd, true_implies] at h₁ <;>
  have ⟨data, hl₁, hr₁⟩ := h₁ <;> clear h₁
  case some.mp =>
    rw [List.any_eq_true] at h₄
    replace ⟨euid, h₄, h₅⟩ := h₄
    exists euid
    replace ⟨h₃, _⟩ := h₃
    simp only [List.subset_def] at h₃
    specialize h₃ h₄ ; simp [h₃]
    simp [inₑ] at h₅
    rcases h₅ with h₅ | h₅
    case inl =>
      subst h₅ ; simp [ActionSchema.descendentOf]
    case inr =>
      simp only [ActionSchema.descendentOf, beq_iff_eq, hfnd, Bool.if_true_left, Bool.or_eq_true,
        decide_eq_true_eq]
      simp only [Entities.ancestorsOrEmpty, hl₁, hr₁] at h₅
      simp only [h₅, or_true]
  case some.mpr =>
    rw [List.any_eq_true]
    replace ⟨euid, h₄, h₅⟩ := h₄
    exists euid
    replace ⟨_, h₃⟩ := h₃
    simp only [List.subset_def] at h₃
    specialize h₃ h₄ ; simp [h₃]
    simp only [ActionSchema.descendentOf, beq_iff_eq, hfnd, Bool.if_true_left, Bool.or_eq_true,
      decide_eq_true_eq] at h₅
    by_cases h₆ : auid = euid <;> simp [h₆] at h₅
    case pos =>
      subst h₆ ; simp [inₑ]
    case neg =>
      simp [inₑ, Entities.ancestorsOrEmpty, hl₁, hr₁, h₅]

theorem entityUIDS?_of_lits {euids : List EntityUID} :
  entityUIDs? (Expr.set (List.map (Expr.lit ∘ Prim.entityUID) euids)) = some euids
  := by
  cases euids
  case nil =>
    simp [entityUIDs?]
  case cons head tail =>
    simp [entityUIDs?]
    constructor
    case left =>
      simp [entityUID?]
    case right =>
      apply entityUIDS?_of_lits

theorem type_of_mem_is_soundₛ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType} {l l₁ l₂ : Level} {ty : CedarType}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf x₁ c₁ env (l == .infinite) = Except.ok (CedarType.entity ety₁ l₁, c₁'))
  (h₄ : typeOf x₂ c₁ env (l == .infinite) = Except.ok (CedarType.set (CedarType.entity ety₂ l₂), c₂'))
  (h₅ : .ok (ty, ∅) = typeOfInₛ ety₁ ety₂ l₁ x₁ x₂ env)
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType v ty
:= by
  have hbool : ∃ b, ty = .bool b := by
    unfold typeOfInₛ at h₅
    split at h₅ <;> try contradiction
    simp [ok] at h₅
    cases ty <;> try contradiction
    rename_i btype
    unfold typeOfInₛ.type at h₅
    split at h₅ <;> split at h₅
    case _ =>
      exists BoolType.tt
    case _ =>
      exists BoolType.ff
    case _ =>
      exists BoolType.anyBool
    case _ =>
      exists BoolType.ff
  have ⟨boolType, hbool⟩ := hbool
  subst hbool
  have ⟨_, v₁, hev₁, hty₁⟩ := ih₁ h₁ h₂ h₃
  have ⟨_, v₂, hev₂, hty₂⟩ := ih₂ h₁ h₂ h₄
  simp only [EvaluatesTo] at *
  simp only [evaluate]
  cases h₅ : evaluate x₁ request entities <;> simp [h₅] at hev₁ <;> simp [h₅, hev₁] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₁ ; subst hev₁
  cases h₆ : evaluate x₂ request entities <;> simp [h₆] at hev₂ <;> simp [h₆, hev₂] <;>
  try { apply type_is_inhabited }
  rw [eq_comm] at hev₂ ; subst hev₂
  replace ⟨euid, hty₁, hty₁'⟩ := instance_of_entity_type_is_entity hty₁
  subst hty₁ hty₁'
  have ⟨vs, hset⟩ := instance_of_set_type_is_set hty₂
  subst hset
  cases vs ; rename_i vs
  simp only [apply₂, inₛ]
  simp only [Set.mapOrErr, Set.elts]
  have ⟨euids, h₇, hty₇⟩ := entity_set_type_implies_set_of_entities hty₂
  simp only [h₇, Except.bind_ok, Except.ok.injEq, false_or, exists_eq_left']
  rename_i h₈
  apply InstanceOfType.instance_of_bool
  simp only [InstanceOfBoolType]
  split <;> try simp only
  rename_i h₈ h₉ h₁₀
  have ⟨_, hents, hacts⟩ := h₂ ; clear h₂
  simp only [List.any_eq_true, imp_false] at *
  cases ha : actionUID? x₁ env.acts
  case none =>
    rename_i hok _
    cases hin : EntitySchema.descendentOf env.ets euid.ty ety₂
    <;> simp [typeOfInₛ, typeOfInₛ.type, ha, hin] at hok
    <;> split at hok
    <;> simp [ok, err] at hok
    case false.inl  =>
      apply h₁₀
      apply entity_type_in_false_implies_inₛ_false
      repeat assumption
    case true.inl =>
      apply h₈
      assumption
  case some =>
    cases he : entityUIDs? x₂
    case none =>
      cases hin : EntitySchema.descendentOf env.ets euid.ty ety₂
      <;> rename_i hok _ euid
      <;>  simp [typeOfInₛ, typeOfInₛ.type] at hok
      <;> split at hok <;> simp [ha,he,hin,ok,err] at hok
      case false =>
        apply h₁₀
        apply entity_type_in_false_implies_inₛ_false
        repeat assumption
      case true =>
        apply h₈
        assumption
    case some =>
      replace ⟨ha, hac⟩ := actionUID?_some_implies_action_lit ha
      subst ha
      have he := entityUIDs?_some_implies_entity_lits he
      subst he
      simp only [evaluate, Except.ok.injEq, Value.prim.injEq, Prim.entityUID.injEq] at h₅
      rw [eq_comm] at h₅ ; subst h₅
      rename_i euids' _ _
      have h₁₁ := evaluate_entity_set_eqv h₆ h₇
      have h₁₂ := action_type_in_eq_action_inₛ hacts hac h₁₁
      cases h₁₃ : Set.any (fun x => inₑ euid x entities) (Set.make euids) <;>
      simp only [h₁₃, Bool.false_eq_true, Bool.true_eq_false, false_implies,
        exists_prop, false_implies, true_implies, false_iff, true_iff,
        not_exists, not_and, Bool.not_eq_true] at h₉ h₁₀ h₁₂
      case false =>
        simp [typeOfInₛ, typeOfInₛ.type] at h₈
        split at h₈ <;> simp [ok,err] at h₈
        case _ =>
          clear h₉
          split at h₈ <;> split at h₈
          case _ =>
            subst h₈
            rename_i heq₁ heq₂ h
            simp [actionUID?, entityUID?] at heq₁
            replace ⟨heq₁, heq₃⟩ := heq₁
            rw [entityUIDS?_of_lits] at heq₂
            injection heq₂
            rename_i heq₂
            have ⟨x, h₁, h₂⟩ := h
            subst heq₃
            subst heq₂
            rw [h₁₂] at h₂
            contradiction
            repeat assumption
          case _ =>
            apply h₁₀
            assumption
          case _ =>
            rename_i hcontra _ _ _ _ _ _ _
            apply hcontra
            assumption
          case _ =>
            apply h₁₀
            assumption
      case true =>
        replace ⟨euid', h₁₂⟩ := h₁₂
        simp [typeOfInₛ, typeOfInₛ.type, err] at h₈
        split at h₈ <;> try assumption
        simp [actionUID?, entityUID?, hac, entityUIDS?_of_lits]  at h₈
        split at h₈
        case _ =>
          simp [ok] at h₈
          apply h₉
          assumption
        case _ =>
          rename_i contra
          apply contra
          exists euid'

theorem type_of_mem_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .mem x₁ x₂) c₁ env (l == .infinite) = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .mem x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .mem x₁ x₂) request entities v ∧ InstanceOfType v ty
:= by
  have ⟨hc, ety₁, ety₂, l₁, l₂, ⟨c₁', h₄⟩ , c₂', h₅⟩ := type_of_mem_inversion h₃
  subst hc
  apply And.intro empty_guarded_capabilities_invariant
  rcases h₅ with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩ --<;> subst h₆
  case _ =>
    have heq : .ok (ty, ∅) = typeOfInₑ ety₁ ety₂ l₁ x₁ x₂ env := by
      simp [typeOfInₑ] at h₆
      split at h₆ <;> simp [ok,err] at h₆
      simp only [typeOfInₑ.type, List.empty_eq, typeOfInₑ, gt_iff_lt, ↓reduceIte, *]
      rfl
    exact type_of_mem_is_soundₑ h₁ h₂ h₄ h₅ heq ih₁ ih₂
  case _ =>
    have heq : .ok (ty, ∅) = typeOfInₛ ety₁ ety₂ l₁ x₁ x₂ env := by
      simp [typeOfInₛ] at h₆
      split at h₆ <;> simp [ok,err] at h₆
      simp only [typeOfInₛ.type, List.empty_eq, typeOfInₛ, gt_iff_lt, ↓reduceIte, *]
      rfl
    exact type_of_mem_is_soundₛ h₁ h₂ h₄ h₅ heq ih₁ ih₂

theorem type_of_binaryApp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : CedarType} {request : Request} {entities : Entities} {l : Level}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env (l == .infinite) = Except.ok (ty, c₂))
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
  | .sub
  | .mul         => exact type_of_int_arith_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .contains    => exact type_of_contains_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .containsAll
  | .containsAny => exact type_of_containsA_is_sound (by simp) h₁ h₂ h₃ ih₁ ih₂
  | .mem         => exact type_of_mem_is_sound h₁ h₂ h₃ ih₁ ih₂

end Cedar.Thm
