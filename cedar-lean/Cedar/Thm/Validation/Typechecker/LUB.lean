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

import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Core.Std

/-!
This file contains useful definitions and lemmas about the
least upper bound (LUB) functions on Cedar types.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

inductive IsLubOfRecordTypes : List (Attr × Qualified CedarType) → List (Attr × Qualified CedarType) → List (Attr × Qualified CedarType) → Prop :=
  | nil : IsLubOfRecordTypes [] [] []
  | cons {a : Attr} {qty qty₁ qty₂ : Qualified CedarType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
    (h₁ : lubQualifiedType qty₁ qty₂ = .some qty)
    (h₂ : IsLubOfRecordTypes rty rty₁ rty₂) :
    IsLubOfRecordTypes ((a, qty) :: rty) ((a, qty₁) :: rty₁) ((a, qty₂) :: rty₂)

theorem lubRecordType_is_lub_of_record_types {rty rty₁ rty₂ : List (Attr × Qualified CedarType)} :
  lubRecordType rty₁ rty₂ = .some rty →
  IsLubOfRecordTypes rty rty₁ rty₂
:= by
  intro h₁
  unfold lubRecordType at h₁
  split at h₁ <;> try simp at h₁
  case h_1 => subst h₁ ; exact IsLubOfRecordTypes.nil
  case h_2 a hd₁ tl₁ a' hd₂ tl₂ =>
    split at h₁ <;> try contradiction
    rename_i h₂ ; subst h₂
    cases h₂ : lubQualifiedType hd₁ hd₂ <;> simp [h₂] at h₁
    cases h₃ : lubRecordType tl₁ tl₂ <;> simp [h₃] at h₁
    rename_i hd tl ; subst h₁
    apply IsLubOfRecordTypes.cons h₂
    apply lubRecordType_is_lub_of_record_types h₃

theorem lubRecord_find_implies_find {a : Attr} {qty : QualifiedType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.find? (Map.mk rty) a = .some qty) :
  (∃ qty₁ qty₂,
    Map.find? (Map.mk rty₁) a = .some qty₁ ∧
    Map.find? (Map.mk rty₂) a = .some qty₂ ∧
    lubQualifiedType qty₁ qty₂ = .some qty)
:= by
  simp [Map.find?, Map.kvs] at *
  induction h₁
  case nil => simp [List.find?] at h₂
  case cons a' hd hd₁ hd₂ tl tl₁ tl₂ h₃ _ ih =>
    simp [Map.find?, Map.kvs] at *
    cases h₅ : a' == a
    case false =>
      simp [List.find?, h₅] at *
      apply ih h₂
    case true =>
      simp [List.find?, h₅] at *
      simp [h₂, h₃]

theorem lubRecord_find_implied_by_find_left {a : Attr} {qty₁ : QualifiedType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.find? (Map.mk rty₁) a = .some qty₁) :
  (∃ qty qty₂,
    Map.find? (Map.mk rty₂) a = .some qty₂ ∧
    Map.find? (Map.mk rty) a = .some qty ∧
    lubQualifiedType qty₁ qty₂ = .some qty)
:= by
  simp [Map.find?, Map.kvs] at *
  induction h₁
  case nil => simp [List.find?] at h₂
  case cons a' hd hd₁ hd₂ tl tl₁ tl₂ h₃ _ ih =>
    simp [Map.find?, Map.kvs] at *
    cases h₅ : a' == a
    case false =>
      simp [List.find?, h₅] at *
      apply ih h₂
    case true =>
      simp [List.find?, h₅] at *
      simp [←h₂, h₃]

theorem lubRecord_contains_left {a : Attr} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.contains (Map.mk rty₁) a = true) :
  Map.contains (Map.mk rty) a = true
:= by
  simp [Map.contains_iff_some_find?] at *
  rcases h₂ with ⟨qty₁, h₂⟩
  rcases (lubRecord_find_implied_by_find_left h₁ h₂) with ⟨qty, _, h₃⟩
  exists qty ; simp [h₃]

theorem lubRecord_find_implies_find_left {a : Attr} {qty : QualifiedType} {rty rty₁ rty₂ : List (Attr × Qualified CedarType)}
  (h₁ : IsLubOfRecordTypes rty rty₁ rty₂)
  (h₂ : Map.find? (Map.mk rty) a = some qty) :
  ∃ qty₁,
    Map.find? (Map.mk rty₁) a = some qty₁ ∧
    Qualified.isRequired qty₁ = Qualified.isRequired qty
:= by
  rcases (lubRecord_find_implies_find h₁ h₂) with ⟨qty₁, qty₂, h₃, h₄, h₅⟩
  exists qty₁ ; simp [h₃]
  unfold lubQualifiedType at h₅
  split at h₅ <;> try simp at h₅
  all_goals {
    rename_i ty₁ ty₂
    cases h₆ : ty₁ ⊔ ty₂ <;> simp [h₆] at h₅
    subst h₅
    simp [Qualified.isRequired]
  }

theorem lubRecordType_nil_some {rty₁ rty₂ : List (Attr × QualifiedType)} :
  lubRecordType [] rty₁ = some rty₂ →
  (rty₁ = [] ∧ rty₂ = [])
:= by
  unfold lubRecordType
  cases rty₁ <;> simp
  intro h₁ ; simp [h₁]

theorem lubBool_comm {bty₁ bty₂ : BoolType} :
  lubBool bty₁ bty₂ = lubBool bty₂ bty₁
:= by
  simp [lubBool] ; split <;> rename_i h <;>
  rw [eq_comm] at h <;> simp [h]

mutual
theorem lubQualified_comm {qty₁ qty₂ : Qualified CedarType} :
  lubQualifiedType qty₁ qty₂ = lubQualifiedType qty₂ qty₁
:= by
  unfold lubQualifiedType
  split
  case h_1 | h_2 =>
    rename_i ty₁ ty₂
    rcases (@lub_comm ty₁ ty₂) with h
    simp [h]
  case h_3 =>
    rename_i h₁ h₂
    split <;> try { rfl } <;>
    rename_i ty₁ ty₂ <;> by_contra
    apply h₁ ty₂ ty₁ <;> rfl
    apply h₂ ty₂ ty₁ <;> rfl

theorem lubRecord_comm {rty₁ rty₂ : List (Attr × Qualified CedarType)} :
  lubRecordType rty₁ rty₂ = lubRecordType rty₂ rty₁
:= by
  unfold lubRecordType
  split <;> simp
  case h_2 =>
    rename_i a₁ hd₁ tl₁ a₂ hd₂ tl₂
    split <;> rename_i h₃ <;> rw [eq_comm] at h₃ <;> simp [h₃]
    subst h₃
    rcases (@lubQualified_comm hd₁ hd₂) with h₄
    rcases (@lubRecord_comm tl₁ tl₂) with h₅
    simp [h₄, h₅]
  case h_3 =>
    rename_i h₁ h₂
    split <;> try { contradiction } <;> try rfl
    split <;> try rfl
    rename_i a₁ hd₁ tl₁ a₂ hd₂ tl₂ h₃ ; subst h₃
    by_contra
    apply h₂ a₁ hd₂ tl₂ a₁ hd₁ tl₁ <;> rfl

theorem lub_comm {ty₁ ty₂ : CedarType} :
  (ty₁ ⊔ ty₂) = (ty₂ ⊔ ty₁)
:= by
  unfold lub?
  split
  case h_1 => simp [lubBool_comm]
  case h_2 =>
    rename_i s₁ s₂
    rcases (@lub_comm s₁ s₂) with h
    simp [h]
  case h_3 =>
    rename_i rty₁ rty₂
    rcases (@lubRecord_comm rty₁ rty₂) with h
    simp [h]
  case h_4 =>
    rename_i h₁ h₂ h₃
    split <;> split <;> rename_i h₄
    case inl.h_4 | inr.h_4 =>
      rename_i _ _ h₅ _ _ _ _
      rw [eq_comm] at h₅
      simp [h₅]
    all_goals {
      rename_i v₁ v₂
      by_contra
      try { apply h₁ v₂ v₁ <;> rfl  }
      try { apply h₂ v₂ v₁ <;> rfl  }
      try { apply h₃ v₂ v₁ <;> rfl  }
    }
end

mutual
theorem lub_refl (ty : CedarType) :
  (ty ⊔ ty) = some ty
:= by
  unfold lub?
  split <;> try simp
  case h_1 => simp [lubBool]
  case h_2 eltTy =>
    rcases (lub_refl eltTy) with h₁
    simp [h₁]
  case h_3 rty =>
    rcases (lubRecordType_refl rty) with h₁
    simp [h₁]

theorem lubRecordType_refl (rty : List (Attr × QualifiedType)) :
  lubRecordType rty rty = some rty
:= by
  unfold lubRecordType
  split <;> try simp
  case h_2 k qty tl =>
    rcases (lubQualifiedType_refl qty) with h₁
    rcases (lubRecordType_refl tl) with h₂
    simp [h₁, h₂]
  case h_3 h₁ h₂ =>
    cases rty <;> simp at h₁
    case cons hd tl =>
      specialize h₂ hd.fst hd.snd tl hd.fst hd.snd tl
      simp at h₂

theorem lubQualifiedType_refl (qty : QualifiedType) :
  lubQualifiedType qty qty = some qty
:= by
  unfold lubQualifiedType
  split
  case h_3 h₁ h₂ =>
    cases qty
    all_goals {
      rename_i ty
      specialize h₁ ty ty
      specialize h₂ ty ty
      simp at h₁ h₂
    }
  all_goals {
    rename_i ty
    rcases (lub_refl ty) with h₁
    simp [h₁]
  }
end

theorem lubQualified_is_lub_of_getType {qty qty₁ qty₂: Qualified CedarType}
  (h₁ : lubQualifiedType qty₁ qty₂ = .some qty) :
  (qty₁.getType ⊔ qty₂.getType) = .some qty.getType
:= by
  unfold lubQualifiedType at h₁
  split at h₁ <;> try simp at h₁
  all_goals {
    rename_i aty₁ aty₂
    cases h₂ : (aty₁ ⊔ aty₂) <;> simp [h₂] at h₁
    simp [Qualified.getType, ←h₁]
  }

mutual
theorem lub_trans {ty₁ ty₂ ty₃ : CedarType} :
  (ty₁ ⊔ ty₂) = some ty₂ →
  (ty₂ ⊔ ty₃) = some ty₃ →
  (ty₁ ⊔ ty₃) = some ty₃
:= by
  intro h₁ h₂
  unfold lub? ; split
  case h_1 bty₁ bty₃ =>
    unfold lub? at h₁ h₂
    cases ty₂ <;> simp at h₁ h₂
    simp [lubBool] at *
    rename_i bty₄
    split ; assumption
    split at h₁ <;> subst h₁ <;>
    split at h₂ <;> try assumption
    subst h₂ ; contradiction
  case h_2 sty₁ sty₃ =>
    unfold lub? at h₁ h₂
    cases ty₂ <;> simp at h₁ h₂
    rename_i sty₂
    cases h₃ : sty₁ ⊔ sty₂ <;> simp [h₃] at h₁
    cases h₄ : sty₂ ⊔ sty₃ <;> simp [h₄] at h₂
    rw [eq_comm] at h₁ h₂ ; subst h₁ h₂
    rcases (lub_trans h₃ h₄) with h₅
    simp [h₅]
  case h_3 rty₁ rty₃ =>
    unfold lub? at h₁ h₂
    cases ty₂ <;> simp at h₁ h₂
    rename_i mty₂ ; cases mty₂ ; rename_i rty₂
    simp at h₁ h₂
    cases h₃ : lubRecordType rty₁ rty₂ <;> simp [h₃] at h₁
    cases h₄ : lubRecordType rty₂ rty₃ <;> simp [h₄] at h₂
    rw [eq_comm] at h₁ h₂ ; subst h₁ h₂
    rcases (lubRecordType_trans h₃ h₄) with h₅
    simp [h₅]
  case h_4 =>
    split
    case inl h₃ => simp [h₃]
    case inr h₃ h₄ h₅ h₆ =>
      unfold lub? at h₁ h₂
      cases ty₁ <;> cases ty₂ <;> simp at h₁ <;>
      cases ty₃ <;> simp at h₂ <;> simp at h₆
      case bool bty₁ _ bty₃ =>
        apply h₃ bty₁ bty₃ <;> rfl
      case set sty₁ _ sty₃ =>
        apply h₄ sty₁ sty₃ <;> rfl
      case record rty₁ _ rty₃ =>
        cases rty₁ ; cases rty₃
        rename_i rty₁' rty₃'
        apply h₅ rty₁' rty₃' <;> rfl
      all_goals {
        rename_i ety₁ ety₂ ety₃
        split at h₁ <;> try contradiction
        split at h₂ <;> try contradiction
        simp at h₂
        subst h₂
        contradiction
      }

theorem lubRecordType_trans {rty₁ rty₂ rty₃ : List (Attr × QualifiedType)} :
  (lubRecordType rty₁ rty₂) = some rty₂ →
  (lubRecordType rty₂ rty₃) = some rty₃ →
  (lubRecordType rty₁ rty₃) = some rty₃
:= by
  unfold lubRecordType
  intro h₁ h₂
  cases rty₁ <;> cases rty₃ <;>
  simp
  case cons.cons hd₁ tl₁ hd₃ tl₃ =>
    cases rty₂ <;> simp at h₁ h₂
    rename_i hd₂ tl₂
    split at h₁ <;> try contradiction
    split at h₂ <;> try contradiction
    rename_i h₃ h₄ ; rw [eq_comm] at h₃ h₄
    simp [h₃] at * ; simp [h₄] at *
    cases h₅ : lubQualifiedType hd₁.snd hd₂.snd <;> simp [h₅] at h₁
    cases h₆ : lubRecordType tl₁ tl₂ <;> simp [h₆] at h₁
    rename_i qty₁ rty₁'
    cases h₇ : lubQualifiedType hd₂.snd hd₃.snd <;> simp [h₇] at h₂
    cases h₈ : lubRecordType tl₂ tl₃ <;> simp [h₈] at h₂
    rename_i qty₂ rty₂'
    rcases h₁ with ⟨hl₁, hr₁⟩
    rcases h₂ with ⟨hl₂, hr₂⟩
    rw [eq_comm] at hl₁ hl₂ hr₁ hr₂
    subst hl₁ hl₂ hr₁ hr₂
    simp [Prod.snd] at *
    rcases (lubQualifiedType_trans h₅ h₇) with h₉
    rcases (lubRecordType_trans h₆ h₈) with h₁₀
    simp [h₉, h₁₀]
  all_goals {
    cases rty₂ <;> simp at h₁ h₂
  }

theorem lubQualifiedType_trans {qty₁ qty₂ qty₃ : QualifiedType} :
  (lubQualifiedType qty₁ qty₂) = some qty₂ →
  (lubQualifiedType qty₂ qty₃) = some qty₃ →
  (lubQualifiedType qty₁ qty₃) = some qty₃
:= by
  unfold lubQualifiedType
  intro h₁ h₂
  cases qty₁ <;> cases qty₃ <;> simp
  case optional.optional ty₁' ty₃' | required.required ty₁' ty₃' =>
    cases qty₂ <;> simp at h₁ h₂
    rename_i ty₂'
    cases h₃ : ty₁' ⊔ ty₂' <;> simp [h₃] at h₁
    cases h₄ : ty₂' ⊔ ty₃' <;> simp [h₄] at h₂
    rw [eq_comm] at h₁ h₂ ; subst h₁ h₂
    rcases (lub_trans h₃ h₄) with h₅
    simp [h₅]
  all_goals {
    cases qty₂ <;> simp at h₁ h₂
  }

end

theorem subty_trans {ty₁ ty₂ ty₃ : CedarType} :
  ty₁ ⊑ ty₂ → ty₂ ⊑ ty₃ → ty₁ ⊑ ty₃
:= by
  unfold subty
  intro h₁ h₂
  split at h₁ <;> try contradiction
  split at h₂ <;> try contradiction
  rename_i ty₄ h₃ _ ty₅ h₄
  simp at h₁ h₂ ; rw [eq_comm] at h₁ h₂; subst h₁ h₂
  rcases (lub_trans h₃ h₄) with h₅
  simp [h₅]

mutual
theorem lub_left_subty {ty₁ ty₂ ty₃ : CedarType} :
  (ty₁ ⊔ ty₂) = some ty₃ → ty₁ ⊑ ty₃
:= by
  unfold lub? subty
  intro h₁
  split at h₁
  case h_1 bty₁ bty₂ =>
    simp [lubBool] at h₁
    split at h₁
    case inl h₂ =>
      subst h₁
      simp [lub?, lubBool]
    case inr h₂ =>
      subst h₁
      simp [lub?, lubBool]
      split ; assumption ; rfl
  case h_2 sty₁ sty₂ =>
    cases h₂ : sty₁ ⊔ sty₂ <;> simp [h₂] at h₁
    rename_i sty₃
    subst h₁
    simp [lub?]
    cases h₃ : sty₁ ⊔ sty₃ <;>
    simp [h₃] <;>
    rcases (lub_left_subty h₂) with h₄ <;>
    simp [subty, h₃] at h₄
    assumption
  case h_3 rty₁ rty₂ =>
    cases h₂ : lubRecordType rty₁ rty₂ <;> simp [h₂] at h₁
    rename_i rty₃
    subst h₁
    simp [lub?]
    cases h₃ : lubRecordType rty₁ rty₃ <;>
    simp [h₃] <;>
    rcases (lubRecordType_left_subty h₂) with h₄ <;>
    simp [h₃] at h₄
    assumption
  case h_4 =>
    split at h₁ <;> try contradiction
    rename_i h₂
    subst h₂
    simp at h₁
    subst h₁
    simp [lub_refl ty₁]

theorem lubRecordType_left_subty {rty₁ rty₂ rty₃ : List (Attr × QualifiedType)} :
  lubRecordType rty₁ rty₂ = some rty₃ →
  lubRecordType rty₁ rty₃ = some rty₃
:= by
  unfold lubRecordType
  intro h₁
  split at h₁ <;> try simp at h₁
  case h_1 =>
    subst h₁ ; simp
  case h_2 a₁ qty₁ rty₁' a₂ qty₂ rty₂' =>
    split at h₁ <;> try contradiction
    rename_i h₂ ; subst h₂
    cases h₂ : lubQualifiedType qty₁ qty₂ <;> simp [h₂] at h₁
    rename_i qty₃
    cases h₃ : lubRecordType rty₁' rty₂' <;> simp [h₃] at h₁
    rename_i rty₃'
    rcases (lubQualifiedType_left_subty h₂) with h₄
    rcases (lubRecordType_left_subty h₃) with h₅
    simp [←h₁, h₄, h₅]

theorem lubQualifiedType_left_subty {qty₁ qty₂ qty₃ : QualifiedType} :
  lubQualifiedType qty₁ qty₂ = some qty₃ →
  lubQualifiedType qty₁ qty₃ = some qty₃
:= by
  unfold lubQualifiedType
  intro h₁
  split at h₁ <;> try simp at h₁
  all_goals {
    rename_i aty₁ aty₂
    cases h₂ : aty₁ ⊔ aty₂ <;> simp [h₂] at h₁
    rename_i aty₃
    subst h₁ ; simp only
    rcases (lub_left_subty h₂) with h₃
    simp [subty] at h₃
    split at h₃ <;> try contradiction
    rename_i aty₄ h₄
    simp [h₄]
    by_contra h₅
    simp [h₅] at h₃
  }

end

theorem sizeOf_qualified_lt_sizeOf_record_type (x : Attr × Qualified CedarType) (xs : List (Attr × Qualified CedarType)) :
  sizeOf x.snd < sizeOf (x :: xs)
:= by
  simp only [List.cons.sizeOf_spec]
  simp [Nat.add_assoc]; rw [Nat.add_comm]
  apply Nat.lt_add_right
  apply Nat.lt_add_right
  simp [sizeOf, Prod._sizeOf_1]
  apply Nat.lt_add_of_one_and_other

theorem lubBool_assoc_none_some {ty₁ ty₂ : CedarType} {bty₁ bty₂ : BoolType}
  (h₁ : (ty₁ ⊔ CedarType.bool bty₁) = none)
  (h₂ : some (CedarType.bool (lubBool bty₁ bty₂)) = some ty₂) :
  (ty₁ ⊔ ty₂) = none
:= by
  simp at h₂
  unfold lub? at h₁
  split at h₁ <;> try contradiction
  rename_i ty₁' ty₂' ty₃' h₃ h₄ h₅
  subst h₂
  cases ty₁' <;> simp [lub?]
  rename_i bty₃
  split at h₁ <;> try contradiction
  apply h₃ bty₃ bty₁ <;> rfl

mutual

theorem lub_assoc_none_some {ty₁ ty₂ ty₃ ty₄ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = none)
  (h₂ : (ty₂ ⊔ ty₃) = some ty₄) :
  (ty₁ ⊔ ty₄) = none
:= by
  unfold lub? at h₂
  split at h₂
  case h_1 =>
    exact lubBool_assoc_none_some h₁ h₂
  case h_2 sty₂ sty₃ =>
    cases h₃ : sty₂ ⊔ sty₃ <;> simp [h₃] at h₂
    rename_i sty₄
    subst h₂
    unfold lub? at h₁ ; unfold lub?
    cases ty₁ <;> simp at *
    rename_i ty₁'
    cases h₄ : ty₁' ⊔ sty₂ <;> simp [h₄] at h₁
    rcases (lub_assoc_none_some h₄ h₃) with h₅
    simp [h₅]
  case h_3 rty₂ rty₃ =>
    cases h₃ : lubRecordType rty₂ rty₃ <;> simp [h₃] at h₂
    subst h₂
    unfold lub? at h₁ ; unfold lub?
    cases ty₁ <;> simp at *
    rename_i mty₁ ; cases mty₁ ; rename_i rty₁
    simp at *
    cases h₄ : lubRecordType rty₁ rty₂ <;> simp [h₄] at h₁
    rcases (lubRecordType_assoc_none_some h₄ h₃) with h₅
    simp [h₅]
  case h_4 =>
    split at h₂ <;> try contradiction
    rename_i h₃ ; simp at h₂
    subst h₂ h₃
    exact h₁

theorem lubRecordType_assoc_none_some {rty₁ rty₂ rty₃ rty₄ : List (Attr × QualifiedType)}
  (h₁ : (lubRecordType rty₁ rty₂) = none)
  (h₂ : (lubRecordType rty₂ rty₃) = some rty₄) :
  (lubRecordType rty₁ rty₄) = none
:= by
  unfold lubRecordType at h₂
  split at h₂ <;> try contradiction
  case h_1 =>
    simp at h₂ ; subst h₂ ; exact h₁
  case h_2 a₂ qty₂ rty₂' a₃ qty₃ rty₃'  =>
    simp at h₂
    split at h₂ <;> try contradiction
    rename_i h₃
    cases h₄ : lubQualifiedType qty₂ qty₃ <;> simp [h₄] at h₂
    cases h₅ : lubRecordType rty₂' rty₃' <;> simp [h₅] at h₂
    subst h₂ h₃
    rename_i qty₁ rty₁'
    unfold lubRecordType at h₁
    cases hrty₁ : rty₁ <;> simp at h₁
    case nil =>
      simp [lubRecordType]
    case cons hd tl =>
      simp [hrty₁] at h₁
      split at h₁
      case inl h₆ =>
        unfold lubRecordType
        simp [h₆]
        cases h₇ : lubQualifiedType hd.snd qty₂ <;> simp [h₇] at h₁
        case none =>
          have _ : sizeOf hd.snd < sizeOf rty₁ := by -- termination
            rw [hrty₁]
            apply sizeOf_qualified_lt_sizeOf_record_type hd tl
          rcases (lubQualifiedType_assoc_none_some h₇ h₄) with h₈
          simp [h₈]
        case some =>
          cases h₈ : lubRecordType tl rty₂' <;> simp [h₈] at h₁
          rcases (lubRecordType_assoc_none_some h₈ h₅) with h₉
          simp [h₉]
          cases h₁₀ : lubQualifiedType hd.snd qty₁ <;> simp [h₁₀]
      case inr h₆ =>
        unfold lubRecordType
        simp [h₆]

theorem lubQualifiedType_assoc_none_some {qty₁ qty₂ qty₃ qty₄ : QualifiedType}
  (h₁ : (lubQualifiedType qty₁ qty₂) = none)
  (h₂ : (lubQualifiedType qty₂ qty₃) = some qty₄) :
  (lubQualifiedType qty₁ qty₄) = none
:= by
  unfold lubQualifiedType at h₂
  split at h₂ <;> try contradiction
  all_goals {
    rename_i ty₂' ty₃'
    cases h₃ : ty₂' ⊔ ty₃' <;> simp [h₃] at h₂
    rename_i ty₄ ; subst h₂
    unfold lubQualifiedType at h₁
    cases qty₁ <;> simp at h₁ <;>
    simp [lubQualifiedType]
    rename_i ty₁'
    cases h₄ : ty₁' ⊔ ty₂' <;> simp [h₄] at h₁
    rcases (lub_assoc_none_some h₄ h₃) with h₅
    simp [h₅]
  }

end
termination_by
lub_assoc_none_some ty₁ ty₂ ty₃ _ _ _ => (sizeOf ty₁)
lubRecordType_assoc_none_some rty₁ rty₂ rty₃ _ _ _ => (sizeOf rty₁)
lubQualifiedType_assoc_none_some qty₁ qty₂ qty₃ _ _ _ => (sizeOf qty₁)

theorem lubBool_assoc_some_some {ty₄ ty₅ : CedarType } { bty₁ bty₂ bty₃ : BoolType }
  (h₁ : CedarType.bool (lubBool bty₁ bty₂) = ty₄)
  (h₂ : CedarType.bool (lubBool bty₂ bty₃) = ty₅) :
(ty₄ ⊔ CedarType.bool bty₃) = (CedarType.bool bty₁ ⊔ ty₅)
:= by
  simp [lubBool] at h₁ h₂
  subst h₁ h₂
  simp [lub?, lubBool]
  cases bty₁ <;> cases bty₂ <;> cases bty₃ <;> simp only

mutual

theorem lub_assoc_some_some {ty₁ ty₂ ty₃ ty₄ ty₅ : CedarType}
  (h₁ : (ty₁ ⊔ ty₂) = some ty₄)
  (h₂ : (ty₂ ⊔ ty₃) = some ty₅) :
  (ty₄ ⊔ ty₃) = (ty₁ ⊔ ty₅)
:= by
  unfold lub? at h₁ h₂
  cases ty₁ <;> cases ty₂ <;> cases ty₃ <;> simp at h₁ h₂
  case bool =>
    exact lubBool_assoc_some_some h₁ h₂
  case int | string =>
    subst h₁ h₂
    simp [lub?]
  case entity | ext =>
    split at h₁ <;> simp at h₁
    split at h₂ <;> simp at h₂
    subst h₁ h₂ ; rename_i h₁ h₂
    simp [lub?, h₁, h₂]
  case set sty₁ sty₂ sty₃ =>
    cases h₃ : sty₁ ⊔ sty₂ <;> simp [h₃] at h₁
    cases h₄ : sty₂ ⊔ sty₃ <;> simp [h₄] at h₂
    rename_i sty₄ sty₅ ; subst h₁ h₂
    simp [lub?]
    rcases (lub_assoc_some_some h₃ h₄) with h₅
    simp [h₅]
  case record mty₁ mty₂ mty₃ =>
    cases mty₁ ; cases mty₂ ; cases mty₃
    simp at *
    rename_i rty₁ rty₂ rty₃
    cases h₃ : lubRecordType rty₁ rty₂ <;> simp [h₃] at h₁
    cases h₄ : lubRecordType rty₂ rty₃ <;> simp [h₄] at h₂
    rename_i rty₄ rty₅ ; subst h₁ h₂
    simp [lub?]
    rcases (lubRecordType_assoc_some_some h₃ h₄) with h₅
    simp [h₅]

theorem lubRecordType_assoc_some_some {rty₁ rty₂ rty₃ rty₄ rty₅ : List (Attr × QualifiedType)}
  (h₁ : (lubRecordType rty₁ rty₂) = some rty₄)
  (h₂ : (lubRecordType rty₂ rty₃) = some rty₅) :
  (lubRecordType rty₄ rty₃) = (lubRecordType rty₁ rty₅)
:= by
  cases hrty₁ : rty₁
  case nil =>
    subst hrty₁
    rcases (lubRecordType_nil_some h₁) with ⟨h₃, h₄⟩
    subst h₃ h₄
    rcases (lubRecordType_nil_some h₂) with ⟨h₃, h₄⟩
    subst h₃ h₄
    rfl
  case cons hd₁ tl₁ =>
    cases hrty₂ : rty₂
    case nil =>
      subst hrty₂
      rw [lubRecord_comm] at h₁
      rcases (lubRecordType_nil_some h₁) with ⟨h₃, _⟩
      subst h₃
      contradiction
    case cons hd₂ tl₂ =>
      cases rty₃
      case nil =>
        subst hrty₂
        rw [lubRecord_comm] at h₂
        rcases (lubRecordType_nil_some h₂) with ⟨_, _⟩
        contradiction
      case cons hd₃ tl₃ =>
        have _ : sizeOf hd₁.snd < sizeOf rty₁ := by -- termination
          rw [hrty₁]
          apply sizeOf_qualified_lt_sizeOf_record_type hd₁ tl₁
        have _ : sizeOf hd₂.snd < sizeOf rty₂ := by -- termination
          rw [hrty₂]
          apply sizeOf_qualified_lt_sizeOf_record_type hd₂ tl₂
        subst hrty₁ hrty₂
        unfold lubRecordType at *
        simp only [bne_iff_ne, ne_eq, ite_not] at h₁
        split at h₁ <;> try contradiction
        split at h₂ <;> try contradiction
        rename_i h₁₂ h₂₃
        cases h₃ : lubQualifiedType hd₁.snd hd₂.snd <;> simp [h₃] at h₁
        cases h₄ : lubRecordType tl₁ tl₂ <;> simp [h₄] at h₁
        cases h₅ : lubQualifiedType hd₂.snd hd₃.snd <;> simp [h₅] at h₂
        cases h₆ : lubRecordType tl₂ tl₃ <;> simp [h₆] at h₂
        subst h₁ h₂
        simp [h₁₂, h₂₃]
        rcases (lubQualifiedType_assoc_some_some h₃ h₅) with h₇
        rcases (lubRecordType_assoc_some_some h₄ h₆) with h₈
        simp [h₇, h₈]

theorem lubQualifiedType_assoc_some_some {qty₁ qty₂ qty₃ qty₄ qty₅ : QualifiedType}
  (h₁ : (lubQualifiedType qty₁ qty₂) = some qty₄)
  (h₂ : (lubQualifiedType qty₂ qty₃) = some qty₅) :
  (lubQualifiedType qty₄ qty₃) = (lubQualifiedType qty₁ qty₅)
:= by
  unfold lubQualifiedType at *
  cases qty₁ <;> cases qty₂ <;> cases qty₃ <;> simp at h₁ h₂
  all_goals {
    rename_i ty₁' ty₂' ty₃'
    cases h₃ : (ty₁' ⊔ ty₂') <;> simp [h₃] at h₁
    cases h₄ : (ty₂' ⊔ ty₃') <;> simp [h₄] at h₂
    rcases (lub_assoc_some_some h₃ h₄) with h₅
    subst h₁ h₂
    simp [h₄, h₅]
  }

end
termination_by
lub_assoc_some_some ty₁ ty₂ ty₃ _ _ _ => (sizeOf ty₁)
lubRecordType_assoc_some_some rty₁ rty₂ rty₃ _ _ _ => (sizeOf rty₁)
lubQualifiedType_assoc_some_some qty₁ qty₂ qty₃ _ _ _ => (sizeOf qty₁)

theorem lub_assoc (ty₁ ty₂ ty₃ : CedarType) :
  (do let ty₄ ← (ty₁ ⊔ ty₂) ; (ty₄ ⊔ ty₃)) =
  (do let ty₄ ← (ty₂ ⊔ ty₃) ; (ty₁ ⊔ ty₄))
:= by
  cases h₁ : (ty₁ ⊔ ty₂) <;>
  cases h₂ : (ty₂ ⊔ ty₃) <;>
  simp
  case none.some ty₄ =>
    rw [eq_comm]
    exact lub_assoc_none_some h₁ h₂
  case some.none ty₄ =>
    rw [lub_comm] at *
    apply lub_assoc_none_some h₂ h₁
  case some.some ty₄ ty₅ =>
    exact lub_assoc_some_some h₁ h₂

end Cedar.Thm
