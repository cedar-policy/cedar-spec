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

theorem type_of_eq_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .eq x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  match x₁, x₂ with
  | .lit p₁, .lit p₂ =>
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
  simp [typeOf] at h₁ ; rename_i h₁'
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp only [typeOfBinaryApp, typeOfEq, beq_iff_eq, ok, List.empty_eq, err] at h₁
  rename_i tc₁ tc₂
  split at h₁
  case h_1 p₁ p₂ =>
    split at h₁ <;> simp at h₁ <;> simp [←h₁] <;>
    rename_i h₄ <;> simp [h₄, TypedExpr.typeOf]
  case h_2 h₄ =>
    split at h₁
    case h_1 h₅ =>
      simp only [Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₁
      replace ⟨h₁, h₁''⟩ := h₁ ; subst ty c'
      simp only [imp_false, List.empty_eq, CedarType.bool.injEq, Except.ok.injEq,
        exists_and_left, exists_and_right, true_and]
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
          · rw [h₅]
            simp [TypedExpr.typeOf]
    case h_2 h₅ =>
      split at h₁ <;> simp only [Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq, reduceCtorEq] at h₁
      replace ⟨h₁, h₁''⟩ := h₁ ; subst ty c'
      simp only [List.empty_eq, CedarType.bool.injEq, reduceCtorEq, if_false_left, and_true,
        Except.ok.injEq, exists_and_left, exists_and_right, true_and]
      split
      case h_1 p₁ p₂ _ =>
        specialize h₄ p₁ p₂ ; simp at h₄
      case h_2 ety₁ ety₂ _ true_is_instance_of_tt _ _ _ _ =>
        exists tc₁.fst
        constructor
        · exists tc₁.snd
        · exists tc₂.fst
          constructor
          · exists tc₂.snd
          · rw [h₅]; simp [TypedExpr.typeOf]
            constructor
            · exists ety₁
            · exists ety₂

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
    case isTrue heq _ _ =>
      subst heq
      simp [EvaluatesTo, evaluate, apply₂]
      exact true_is_instance_of_tt
    case isFalse p₁ p₂ heq _ =>
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
      have ⟨hty₀, ⟨ety₁, hty₁⟩, ⟨ety₂, hty₂⟩⟩ := hty ; clear hty
      rw [hty₁] at ih₃ heq
      rw [hty₂] at ih₄ heq
      have h₆ := no_entity_type_lub_implies_not_eq ih₃ ih₄ heq
      cases h₇ : v₁ == v₂ <;>
      simp only [beq_iff_eq, beq_eq_false_iff_ne, ne_eq, Value.prim.injEq] at h₇
      case false => rw [hty₀]; exact false_is_instance_of_ff
      case true  => contradiction

theorem type_of_int_cmp_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : op₂ = .less ∨ op₂ = .lessEq)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty.typeOf = .bool .anyBool ∧
  (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.int, c₁)) ∧
  (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (.int, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp at h₂ ; simp [←h₂, TypedExpr.typeOf]
    rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    constructor
    · exists tc₁.snd ; simp [←h₅, ResultType.typeOf, Except.map]
    · exists tc₂.snd ; simp [←h₆, ResultType.typeOf, Except.map]
  }

theorem type_of_int_cmp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : op₂ = .less ∨ op₂ = .lessEq)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨hc, hty, ht₁, ht₂⟩ := type_of_int_cmp_inversion h₀ h₃
  subst hc ; rw [hty]
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  split_type_of ht₁ ; rename_i ht₁ htl₁ htr₁
  split_type_of ht₂ ; rename_i ht₂ htl₂ htr₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; exact type_is_inhabited (.bool .anyBool) }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  rw [htl₁] at ih₃
  rw [htl₂] at ih₄
  have ⟨i₁, ih₁⟩ := instance_of_int_is_int ih₃
  have ⟨i₂, ih₂⟩ := instance_of_int_is_int ih₄
  subst ih₁ ih₂
  rcases h₀ with h₀ | h₀
  all_goals {
    subst h₀
    simp [apply₂]
    apply bool_is_instance_of_anyBool
  }

theorem type_of_int_arith_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty.typeOf = .int ∧
  (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.int, c₁)) ∧
  (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (.int, c₂))
:= by
  simp [typeOf] at *
  cases h₃ : typeOf x₁ c env <;> simp [h₃] at h₂
  cases h₄ : typeOf x₂ c env <;> simp [h₄] at h₂
  rcases h₁ with h₁ | h₁ | h₁
  all_goals {
    subst h₁
    simp [typeOfBinaryApp, err, ok] at h₂
    split at h₂ <;> try contradiction
    simp at h₂ ; simp [h₂]
    rename_i tc₁ tc₂ _ _ _ _ h₅ h₆
    replace ⟨h₂, _⟩ := h₂
    rw [←h₂]
    simp only [TypedExpr.typeOf, true_and]
    constructor
    · exists tc₁.snd ; simp [←h₂, ←h₅, ResultType.typeOf, Except.map]
    · exists tc₂.snd ; simp [←h₂, ←h₆, ResultType.typeOf, Except.map]
  }

theorem type_of_int_arith_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : op₂ = .add ∨ op₂ = .sub ∨ op₂ = .mul)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨hc, hty, ht₁, ht₂⟩ := type_of_int_arith_inversion h₀ h₃
  subst hc ; rw [hty]
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  split_type_of ht₁ ; rename_i ht₁ htl₁ htr₁
  split_type_of ht₂ ; rename_i ht₂ htl₂ htr₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; exact type_is_inhabited .int }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  rw [htl₁] at ih₃
  have ⟨i₁, ih₁⟩ := instance_of_int_is_int ih₃
  rw [htl₂] at ih₄
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

theorem type_of_contains_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .contains x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty.typeOf = .bool .anyBool ∧
  ∃ ty₁ ty₂,
    (ty₁ ⊔ ty₂).isSome ∧
    (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.set ty₁, c₁)) ∧
    (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (ty₂, c₂))
:= by
  simp [typeOf] at *
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, err, ok] at h₁
  split at h₁ <;> try contradiction
  simp only [ifLubThenBool, ok, List.empty_eq, err] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, Except.bind_ok, Except.bind_err, Prod.mk.injEq, reduceCtorEq] at h₁
  simp [←h₁, TypedExpr.typeOf]
  rename_i tc₁ tc₂ _ ty₁ ty₂ ty₃ _ h₄ _ _ h₅
  exists ty₃, tc₂.fst.typeOf
  rw [lub_comm] at h₅
  simp [h₅, ←h₄]
  constructor
  · exists tc₁.snd
  · exists tc₂.snd

theorem type_of_contains_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .contains x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .contains x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .contains x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨hc, hty, ty₁, ty₂, _, ht₁, ht₂⟩ := type_of_contains_inversion h₃
  subst hc ; rw [hty]
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  split_type_of ht₁ ; rename_i ht₁ htl₁ htr₁
  split_type_of ht₂ ; rename_i ht₂ htl₂ htr₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; apply type_is_inhabited }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  rw [htl₁] at ih₃
  have ⟨s₁, ih₁⟩ := instance_of_set_type_is_set ih₃
  subst ih₁
  simp [apply₂]
  apply bool_is_instance_of_anyBool

theorem type_of_containsA_inversion {op₂ : BinaryOp} {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : op₂ = .containsAll ∨ op₂ = .containsAny)
  (h₂ : typeOf (Expr.binaryApp op₂ x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ty.typeOf = .bool .anyBool ∧
  ∃ ty₁ ty₂,
    (ty₁ ⊔ ty₂).isSome ∧
    (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.set ty₁, c₁)) ∧
    (∃ c₂, (typeOf x₂ c env).typeOf = Except.ok (.set ty₂, c₂))
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
    split at h₂ <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h₂
    simp [←h₂, TypedExpr.typeOf]
    rename_i tc₁ tc₂ _ _ _ ty₁ ty₂ _ h₅ h₆ _ _ h₇
    exists ty₁, ty₂
    simp [h₇]
    constructor
    · exists tc₁.snd ; simp [←h₅, ResultType.typeOf, Except.map]
    · exists tc₂.snd ; simp [←h₆, ResultType.typeOf, Except.map]
  }


theorem type_of_containsA_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : op₂ = .containsAll ∨ op₂ = .containsAny)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨hc, hty, ty₁, ty₂, _, ht₁, ht₂⟩ := type_of_containsA_inversion h₀ h₃
  subst hc ; rw [hty]
  apply And.intro empty_guarded_capabilities_invariant
  replace ⟨c₁', ht₁⟩ := ht₁
  replace ⟨c₂', ht₂⟩ := ht₂
  split_type_of ht₁ ; rename_i ht₁ htl₁ htr₁
  split_type_of ht₂ ; rename_i ht₂ htl₂ htr₂
  specialize ih₁ h₁ h₂ ht₁ ; replace ⟨_, v₁, ih₁⟩ := ih₁
  specialize ih₂ h₁ h₂ ht₂ ; replace ⟨_, v₂, ih₂⟩ := ih₂
  simp [EvaluatesTo, evaluate] at *
  cases h₄ : evaluate x₁ request entities <;> simp [h₄] at * <;>
  cases h₅ : evaluate x₂ request entities <;> simp [h₅] at * <;>
  try { simp [ih₁, ih₂] ; apply type_is_inhabited }
  replace ⟨ihl₁, ih₃⟩ := ih₁
  replace ⟨ihl₂, ih₄⟩ := ih₂
  rw [eq_comm] at ihl₁ ihl₂; subst ihl₁ ihl₂
  rw [htl₁] at ih₃
  rw [htl₂] at ih₄
  have ⟨s₁, ih₁⟩ := instance_of_set_type_is_set ih₃
  have ⟨s₂, ih₂⟩ := instance_of_set_type_is_set ih₄
  subst ih₁ ih₂
  rcases h₀ with h₀ | h₀
  all_goals {
    subst h₀
    simp [apply₂]
    apply bool_is_instance_of_anyBool
  }

theorem type_of_mem_inversion {x₁ x₂ : Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .mem x₁ x₂) c env = Except.ok (ty, c')) :
  c' = ∅ ∧
  ∃ (ety₁ ety₂ : EntityType),
    (∃ c₁, (typeOf x₁ c env).typeOf = Except.ok (.entity ety₁, c₁)) ∧
    (∃ c₂,
      ((typeOf x₂ c env).typeOf = Except.ok (.entity ety₂, c₂) ∧
       ty.typeOf = .bool (typeOfInₑ ety₁ ety₂ x₁ x₂ env)) ∨
      ((typeOf x₂ c env).typeOf = Except.ok (.set (.entity ety₂), c₂) ∧
       ty.typeOf = .bool (typeOfInₛ ety₁ ety₂ x₁ x₂ env)))
:= by
  simp [typeOf] at h₁
  cases h₂ : typeOf x₁ c env <;> simp [h₂] at h₁
  cases h₃ : typeOf x₂ c env <;> simp [h₃] at h₁
  simp [typeOfBinaryApp, ok] at h₁
  split at h₁ <;> try { contradiction }
  all_goals {
    simp only [Except.ok.injEq, Prod.mk.injEq] at h₁
    simp [←h₁, TypedExpr.typeOf]
    rename_i tc₁ tc₂ _ _ _ ety₁ ety₂ _ h₄ h₅
    exists ety₁
    constructor
    · exists tc₁.snd ; simp [←h₄, ResultType.typeOf, Except.map]
    · exists ety₂, tc₂.snd ; simp [←h₅, h₁, ResultType.typeOf, Except.map]
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
  subst euid'
  simp [h₀, h₂]

theorem entityUIDs?_some_implies_entity_lits {x : Expr} {euids : List EntityUID}
  (h₁ : entityUIDs? x = some euids) :
  x = Expr.set ((List.map (Expr.lit ∘ Prim.entityUID) euids))
:= by
  simp [entityUIDs?] at h₁
  split at h₁ <;> try simp at h₁
  rename_i xs
  simp [List.mapM_some_iff_forall₂] at *
  cases euids
  case nil =>
    cases xs <;> simp only [List.Forall₂.nil, List.map_nil] at *
    case cons hd tl => simp only [List.forall₂_nil_right_iff, reduceCtorEq] at h₁
  case cons hd tl =>
    cases xs <;> simp [pure, Except.pure] at *
    case nil => simp only [List.forall₂_nil_left_iff, reduceCtorEq] at h₁
    case cons hd' tl' =>
      cases h₂ : entityUID? hd' <;> simp [h₂] at h₁
      replace ⟨h₁', h₁⟩ := h₁
      replace h₂ := entityUID?_some_implies_entity_lit h₂
      subst hd hd'
      simp only [true_and]
      have h₄ := @entityUIDs?_some_implies_entity_lits (.set tl') tl
      simp [entityUIDs?] at h₄
      apply h₄ ; clear h₄
      simp only [List.mapM_some_iff_forall₂, h₁]

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
    have ⟨entry, h₂₁, _, h₂₂, _⟩ := h₁ euid₁ data h₄
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

theorem type_of_mem_is_soundₑ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety₁, c₁'))
  (h₄ : (typeOf x₂ c₁ env).typeOf = Except.ok (CedarType.entity ety₂, c₂'))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType v (CedarType.bool (typeOfInₑ ety₁ ety₂ x₁ x₂ env))
:= by
  split_type_of h₃ ; rename_i h₃ hl₃ hr₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
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
  rw [hl₃] at hty₁
  replace hty₁ := instance_of_entity_type_is_entity hty₁
  replace ⟨euid₁, hty₁, hty₁'⟩ := hty₁
  subst hty₁ hty₁'
  rw [hl₄] at hty₂
  replace hty₂ := instance_of_entity_type_is_entity hty₂
  replace ⟨euid₂, hty₂, hty₂'⟩ := hty₂
  subst hty₂ hty₂'
  simp [apply₂]
  apply InstanceOfType.instance_of_bool
  simp [InstanceOfBoolType]
  split <;> try simp only
  rename_i b bty  h₇ h₈ h₉
  simp [typeOfInₑ] at *
  have ⟨_, hents, hacts⟩ := h₂ ; clear h₂
  cases hₐ : actionUID? x₁ env.acts <;> simp [hₐ] at h₇ h₈ h₉
  case none =>
    cases hin : EntitySchema.descendentOf env.ets euid₁.ty euid₂.ty <;>
    simp [hin] at h₇ h₈ h₉
    simp [entity_type_in_false_implies_inₑ_false hents hin] at h₉
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
    have h₂ := h₁ hd
    simp [Set.mem_cons_self] at h₂
    replace ⟨heuid, hdty, h₂⟩ := instance_of_entity_type_is_entity h₂
    subst h₂
    rw [Value.asEntityUID] ; simp only [Except.bind_ok]
    rw [List.mapM'_eq_mapM]
    have h₃ : InstanceOfType (Value.set (Set.mk tl)) (CedarType.set (CedarType.entity ety)) := by
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
    replace ⟨entry, h₁, _, h₇, _⟩ := h₁ euid data h₆
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

theorem type_of_mem_is_soundₛ {x₁ x₂ : Expr} {c₁ c₁' c₂' : Capabilities} {env : Environment} {request : Request} {entities : Entities} {ety₁ ety₂ : EntityType}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : (typeOf x₁ c₁ env).typeOf = Except.ok (CedarType.entity ety₁, c₁'))
  (h₄ : (typeOf x₂ c₁ env).typeOf = Except.ok (CedarType.set (CedarType.entity ety₂), c₂'))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  ∃ v,
    EvaluatesTo (Expr.binaryApp BinaryOp.mem x₁ x₂) request entities v ∧
    InstanceOfType v (CedarType.bool (typeOfInₛ ety₁ ety₂ x₁ x₂ env))
:= by
  split_type_of h₃ ; rename_i h₃ hl₃ hr₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
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
  rw [hl₃] at hty₁
  replace ⟨euid, hty₁, hty₁'⟩ := instance_of_entity_type_is_entity hty₁
  subst hty₁ hty₁'
  rw [hl₄] at hty₂
  have ⟨vs, hset⟩ := instance_of_set_type_is_set hty₂
  subst hset
  cases vs ; rename_i vs
  simp only [apply₂, inₛ]
  simp only [Set.mapOrErr, Set.elts]
  have ⟨euids, h₇, hty₇⟩ := entity_set_type_implies_set_of_entities hty₂
  simp only [h₇, Except.bind_ok, Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
  apply InstanceOfType.instance_of_bool
  simp only [InstanceOfBoolType]
  split <;> try simp only
  rename_i h₈ h₉ h₁₀
  have ⟨_, hents, hacts⟩ := h₂ ; clear h₂
  simp only [typeOfInₛ, List.any_eq_true, imp_false] at *
  cases ha : actionUID? x₁ env.acts <;>
  simp only [ha, ite_eq_left_iff, Bool.not_eq_true, imp_false, Bool.not_eq_false,
    ite_eq_right_iff, reduceCtorEq] at h₈ h₉ h₁₀
  case none =>
    cases hin : EntitySchema.descendentOf env.ets euid.ty ety₂ <;>
    simp only [hin, Bool.false_eq_true, ↓reduceIte, not_false_eq_true, implies_true, imp_false,
      Bool.not_eq_false, Bool.true_eq_false] at h₈ h₉ h₁₀
    simp only [entity_type_in_false_implies_inₛ_false hents hin hty₇,
      Bool.false_eq_true] at h₁₀
  case some =>
    cases he : entityUIDs? x₂ <;>
    simp only [he, ite_eq_left_iff, not_exists, not_and, Bool.not_eq_true, imp_false,
      Classical.not_forall, not_imp, Bool.not_eq_false, ite_eq_right_iff, reduceCtorEq] at h₈ h₉ h₁₀
    case none =>
      cases hin : EntitySchema.descendentOf env.ets euid.ty ety₂ <;>
      simp only [hin, Bool.false_eq_true, ↓reduceIte, not_false_eq_true, implies_true, imp_false,
        Bool.not_eq_false, Bool.true_eq_false] at h₈ h₉ h₁₀
      simp only [entity_type_in_false_implies_inₛ_false hents hin hty₇, Bool.false_eq_true] at h₁₀
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
        replace ⟨euid', h₁₀⟩ := h₁₀
        specialize h₁₂ euid' h₁₀.left
        simp only [h₁₀.right, Bool.true_eq_false] at h₁₂
      case true =>
        replace ⟨euid', h₁₂⟩ := h₁₂
        specialize h₉ euid' h₁₂.left
        simp only [h₁₂.right, Bool.true_eq_false] at h₉

theorem type_of_mem_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .mem x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .mem x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .mem x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨hc, ety₁, ety₂, ⟨c₁', h₄⟩ , c₂', h₅⟩ := type_of_mem_inversion h₃
  subst hc
  apply And.intro empty_guarded_capabilities_invariant
  rcases h₅ with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩ <;> rw [h₆]
  · exact type_of_mem_is_soundₑ h₁ h₂ h₄ h₅ ih₁ ih₂
  · exact type_of_mem_is_soundₛ h₁ h₂ h₄ h₅ ih₁ ih₂

theorem type_of_hasTag_inversion {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .hasTag x₁ x₂) c₁ env = .ok (ty, c₂)) :
  ∃ ety c₁' c₂',
    (typeOf x₁ c₁ env).typeOf = .ok (.entity ety, c₁') ∧
    (typeOf x₂ c₁ env).typeOf = .ok (.string, c₂') ∧
    typeOfHasTag ety x₁ x₂ c₁ env = .ok (ty.typeOf, c₂)
:= by
  simp only [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp only [h₂, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  cases h₃ : typeOf x₂ c₁ env <;> simp only [h₃, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  rename_i tyc₁ tyc₂
  cases tyc₁
  cases tyc₂
  rename_i ty₁ c₁' ty₂ c₂'
  simp only at h₁
  cases h₄ : ty₁.typeOf <;> simp only [h₄, typeOfBinaryApp, err, reduceCtorEq] at h₁
  cases h₅ : ty₂.typeOf <;> simp only [h₅, typeOfBinaryApp, err, reduceCtorEq] at h₁
  rename_i ety
  cases h₆ : typeOfHasTag ety x₁ x₂ c₁ env <;>
  simp only [h₆, Except.bind_err, Except.bind_ok, ok, reduceCtorEq, Except.ok.injEq, Prod.mk.injEq] at h₁
  exists ety, c₁', c₂'
  simp only [h₄, h₅, ResultType.typeOf, Except.map]
  simp [←h₁, h₆, TypedExpr.typeOf]

private theorem map_empty_contains_instance_of_ff [DecidableEq α] [DecidableEq β] {k : α} :
  InstanceOfType (Value.prim (Prim.bool ((Map.empty : Map α β).contains k))) (CedarType.bool BoolType.ff)
:= by
  simp only [Map.not_contains_of_empty, false_is_instance_of_ff]

private theorem no_tags_type_implies_no_tags {uid : EntityUID} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfEntitySchema entities env.ets)
  (h₂ : env.ets.tags? uid.ty = .some .none) :
  InstanceOfType (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.ff)
:= by
  simp only [Entities.tagsOrEmpty]
  split
  · rename_i d hf
    replace ⟨e, hf', _, _, h₁⟩ := h₁ uid d hf
    simp only [InstanceOfEntityTags] at h₁
    simp only [EntitySchema.tags?, Option.map_eq_some'] at h₂
    replace ⟨e', h₂, h₃⟩ := h₂
    simp only [hf', Option.some.injEq] at h₂
    subst h₂
    simp only [h₃] at h₁
    simp only [h₁, map_empty_contains_instance_of_ff]
  · exact map_empty_contains_instance_of_ff

private theorem no_type_implies_no_tags {uid : EntityUID} {env : Environment} {entities : Entities}
  (h₁ : InstanceOfEntitySchema entities env.ets)
  (h₂ : env.ets.tags? uid.ty = .none) :
  InstanceOfType (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.ff)
:= by
  simp only [Entities.tagsOrEmpty]
  split
  · rename_i d hf
    replace ⟨e, h₁, _, _, _⟩ := h₁ uid d hf
    simp only [EntitySchema.tags?, Option.map_eq_none'] at h₂
    simp only [h₁, reduceCtorEq] at h₂
  · exact map_empty_contains_instance_of_ff

private theorem mem_capabilities_implies_mem_tags {x₁ x₂ : Expr} {c₁ : Capabilities} {request : Request} {entities : Entities} {uid : EntityUID} {s : String}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (ih₁ : evaluate x₁ request entities = Except.ok (Value.prim (Prim.entityUID uid)))
  (ih₂ : evaluate x₂ request entities = Except.ok (Value.prim (Prim.string s)))
  (hin : (x₁, Key.tag x₂) ∈ c₁) :
  InstanceOfType (Value.prim (Prim.bool ((entities.tagsOrEmpty uid).contains s))) (CedarType.bool BoolType.tt)
:= by
  replace h₁ := h₁.right x₁ x₂ hin
  simp only [EvaluatesTo, evaluate, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, Except.ok.injEq,
    Value.prim.injEq, Prim.bool.injEq, false_or, reduceCtorEq] at h₁
  simp only [h₁, true_is_instance_of_tt]

private theorem hasTag_true_implies_cap_inv {x₁ x₂ : Expr} {request : Request} {entities : Entities} {uid : EntityUID} {s : String}
  (ih₁ : evaluate x₁ request entities = Except.ok (Value.prim (Prim.entityUID uid)))
  (ih₂ : evaluate x₂ request entities = Except.ok (Value.prim (Prim.string s)))
  (ht : (entities.tagsOrEmpty uid).contains s = true) :
  CapabilitiesInvariant (Capabilities.singleton x₁ (Key.tag x₂)) request entities
:= by
  constructor <;>
  intro e k hin <;>
  simp only [Capabilities.singleton, List.mem_singleton, Prod.mk.injEq, and_false, Key.tag.injEq, reduceCtorEq] at hin
  replace ⟨hin, hin'⟩ := hin
  subst hin hin'
  simp only [EvaluatesTo, evaluate, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, ht, or_true]

theorem type_of_hasTag_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .hasTag x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .hasTag x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .hasTag x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  replace ⟨ety, c₁', c₂', h₄, h₅, h₃⟩ := type_of_hasTag_inversion h₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  split_type_of h₅ ; rename_i h₅ hl₅ hr₅
  replace ⟨_, v₁, ih₁, hty₁⟩ := ih₁ h₁ h₂ h₄
  replace ⟨_, v₂, ih₂, hty₂⟩ := ih₂ h₁ h₂ h₅
  simp only [EvaluatesTo] at *
  simp only [GuardedCapabilitiesInvariant, evaluate]
  rcases ih₁ with ih₁ | ih₁ | ih₁ | ih₁ <;>
  simp only [ih₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_is_inhabited)
  rcases ih₂ with ih₂ | ih₂ | ih₂ | ih₂ <;>
  simp only [ih₂, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_is_inhabited)
  rw [hl₄] at hty₁
  replace ⟨uid, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hty₁
  rw [hl₅] at hty₂
  replace ⟨s, hv₂⟩ := instance_of_string_is_string hty₂
  subst hv₁ hv₂ hty₁
  simp only [apply₂, hasTag, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or, exists_eq_left']
  simp only [typeOfHasTag, List.empty_eq] at h₃
  have hempty := empty_capabilities_invariant request entities
  simp only [List.empty_eq] at hempty
  split at h₃
  case h_1 heq =>
    simp [ok] at h₃
    have ⟨ hl₃, hr₃ ⟩ := h₃
    simp only [implies_true, reduceCtorEq, false_or, exists_eq_left', true_and, hr₃, ←hl₃, hempty]
    apply no_tags_type_implies_no_tags h₂.right.left heq
  case h_2 =>
    split at h₃ <;> simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h₃ <;>
    replace ⟨h₃, h₆⟩ := h₃ <;>
    rw [←h₆, ←h₃]
    case isTrue hin =>
      simp only [hempty, implies_true, reduceCtorEq, false_or, exists_eq_left', true_and]
      exact mem_capabilities_implies_mem_tags h₁ ih₁ ih₂ hin
    case isFalse =>
      simp only [reduceCtorEq, false_or, exists_eq_left', bool_is_instance_of_anyBool, and_true]
      intro ht
      exact hasTag_true_implies_cap_inv ih₁ ih₂ ht
  case h_3 heq =>
    split at h₃ <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h₃
    rename_i hact
    simp only [←h₃, hempty, implies_true, reduceCtorEq, false_or, exists_eq_left', true_and]
    exact no_type_implies_no_tags h₂.right.left heq

theorem type_of_getTag_inversion {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.binaryApp .getTag x₁ x₂) c₁ env = .ok (ty, c₂)) :
  c₂ = [] ∧
  ∃ ety c₁' c₂',
    (typeOf x₁ c₁ env).typeOf = .ok (.entity ety, c₁') ∧
    (typeOf x₂ c₁ env).typeOf = .ok (.string, c₂') ∧
    env.ets.tags? ety = some (some ty.typeOf) ∧
    (x₁, .tag x₂) ∈ c₁
:= by
  simp only [typeOf] at h₁
  cases h₂ : typeOf x₁ c₁ env <;> simp only [h₂, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  cases h₃ : typeOf x₂ c₁ env <;> simp only [h₃, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
  rename_i tyc₁ tyc₂
  cases tyc₁
  cases tyc₂
  rename_i ty₁ c₁' ty₂ c₂'
  simp only at h₁
  cases h₄ : ty₁.typeOf <;> simp [typeOfBinaryApp, err, reduceCtorEq, h₄] at h₁
  cases h₅ : ty₂.typeOf <;> simp [typeOfBinaryApp, err, reduceCtorEq, h₅] at h₁
  rename_i ety
  simp only [typeOfGetTag, List.empty_eq] at h₁
  split at h₁ <;> simp only [ok, err, Except.bind_err, reduceCtorEq] at h₁
  split at h₁ <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Prod.mk.injEq, List.nil_eq, reduceCtorEq] at h₁
  rename_i h₆ h₇
  replace ⟨h₁, h₁'⟩ := h₁
  subst h₁ h₁'
  simp only [true_and]
  exists ety
  simp only [ResultType.typeOf, Except.map, h₄, h₅, h₆, h₇]
  simp [TypedExpr.typeOf]

theorem type_of_getTag_is_sound {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp .getTag x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp .getTag x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp .getTag x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  replace ⟨hc, ety, c₁', c₂', h₃, h₄, h₅, h₆⟩ := type_of_getTag_inversion h₃
  subst hc
  split_type_of h₃ ; rename_i h₃ hl₃ hr₃
  split_type_of h₄ ; rename_i h₄ hl₄ hr₄
  replace ⟨_, v₁, ih₁, hty₁⟩ := ih₁ h₁ h₂ h₃
  replace ⟨_, v₂, ih₂, hty₂⟩ := ih₂ h₁ h₂ h₄
  simp only [EvaluatesTo] at *
  simp only [GuardedCapabilitiesInvariant, evaluate]
  rcases ih₁ with ih₁ | ih₁ | ih₁ | ih₁ <;>
  simp only [ih₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_is_inhabited)
  rcases ih₂ with ih₂ | ih₂ | ih₂ | ih₂ <;>
  simp only [ih₂, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_false, or_true, true_and, reduceCtorEq]
  any_goals (apply type_is_inhabited)
  rw [hl₃] at hty₁
  replace ⟨uid, hty₁, hv₁⟩ := instance_of_entity_type_is_entity hty₁
  rw [hl₄] at hty₂
  replace ⟨s, hv₂⟩ := instance_of_string_is_string hty₂
  subst hv₁ hv₂ hty₁
  simp only [apply₂, hasTag, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq, false_or, exists_eq_left']
  simp only [getTag, Entities.tags]
  have hf₁ := Map.findOrErr_returns entities uid Error.entityDoesNotExist
  rcases hf₁ with ⟨d, hf₁⟩ | hf₁ <;>
  simp only [hf₁, Except.bind_ok, Except.bind_err, false_implies, Except.error.injEq, or_self, or_false, true_and,
    type_is_inhabited, and_self, reduceCtorEq]
  rw [Map.findOrErr_ok_iff_find?_some] at hf₁
  replace ⟨entry, hf₂, _, _, h₂⟩  := h₂.right.left uid d hf₁
  simp only [InstanceOfEntityTags] at h₂
  simp only [EntitySchema.tags?, Option.map_eq_some'] at h₅
  replace ⟨_, h₅, h₇⟩ := h₅
  simp only [hf₂, Option.some.injEq] at h₅
  subst h₅
  simp only [h₇] at h₂
  have hf₃ := Map.findOrErr_returns d.tags s Error.tagDoesNotExist
  rcases hf₃ with ⟨v, hf₃⟩ | hf₃ <;>
  simp only [hf₃, false_implies, Except.error.injEq, or_self, false_and, exists_const, and_false,
    Except.ok.injEq, false_or, exists_eq_left', reduceCtorEq]
  · simp only [← List.empty_eq, empty_capabilities_invariant request entities, implies_true, true_and, reduceCtorEq]
    apply h₂
    exact Map.findOrErr_ok_implies_in_values hf₃
  · replace h₁ := h₁.right x₁ x₂ h₆
    simp only [EvaluatesTo, evaluate, ih₁, ih₂, apply₂, hasTag, Except.bind_ok, Except.ok.injEq,
      Value.prim.injEq, Prim.bool.injEq, false_or, reduceCtorEq] at h₁
    simp only [Entities.tagsOrEmpty, hf₁, Map.contains_iff_some_find?] at h₁
    replace ⟨_, h₁⟩ := h₁
    simp only [Map.findOrErr_err_iff_find?_none, h₁, reduceCtorEq] at hf₃

theorem type_of_binaryApp_is_sound {op₂ : BinaryOp} {x₁ x₂ : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.binaryApp op₂ x₁ x₂) c₁ env = Except.ok (ty, c₂))
  (ih₁ : TypeOfIsSound x₁)
  (ih₂ : TypeOfIsSound x₂) :
  GuardedCapabilitiesInvariant (Expr.binaryApp op₂ x₁ x₂) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.binaryApp op₂ x₁ x₂) request entities v ∧ InstanceOfType v ty.typeOf
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
  | .hasTag      => exact type_of_hasTag_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .getTag      => exact type_of_getTag_is_sound h₁ h₂ h₃ ih₁ ih₂

end Cedar.Thm
