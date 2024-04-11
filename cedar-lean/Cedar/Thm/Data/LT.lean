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
import Std

/-!
This file contains proofs that the less-than (`<`) relation on Cedar values is strict.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data

namespace Decide
-- Temporary `simp` lemmas.  We should be able to get rid of these when we upgrade to a
-- future version of Lean.
@[simp] theorem decide_eq_true_eq {_ : Decidable p} : (decide p = true) = p := propext <| Iff.intro of_decide_eq_true decide_eq_true
@[simp] theorem decide_eq_false_eq {h : Decidable p} : (decide p = false) = ¬ p := by cases h <;> simp [decide, *]
@[simp] theorem decide_not {h : Decidable p} : decide (¬ p) = !decide p := by cases h <;> rfl
@[simp] theorem not_decide_eq_true {h : Decidable p} : ((!decide p) = true) = ¬ p := by cases h <;> simp [decide, *]
end Decide


----- `<` is strict on `IPNet` -----

theorem IPNet.lt_asymm {a₁ a₂ p₁ p₂ : Nat} :
  a₁ < a₂ ∨ a₁ = a₂ ∧ p₁ < p₂ → ¬(a₂ < a₁ ∨ a₂ = a₁ ∧ p₂ < p₁)
:= by omega

theorem IPNet.lt_trans {a₁ a₂ a₃ p₁ p₂ p₃ : Nat}
  (h₁ : a₁ < a₂ ∨ a₁ = a₂ ∧ p₁ < p₂)
  (h₂ : a₂ < a₃ ∨ a₂ = a₃ ∧ p₂ < p₃) :
  a₁ < a₃ ∨ a₁ = a₃ ∧ p₁ < p₃
:= by omega

theorem IPNet.lt_conn {a₁ a₂ p₁ p₂ : Nat}
  (h₁ : a₁ = a₂ → ¬p₁ = p₂) :
  (a₁ < a₂ ∨ a₁ = a₂ ∧ p₁ < p₂) ∨ a₂ < a₁ ∨ a₂ = a₁ ∧ p₂ < p₁
:= by omega

instance IPNet.strictLT : StrictLT Ext.IPAddr.IPNet where
  asymmetric a b   := by
    cases a <;> cases b <;> simp only [LT.lt] <;> simp only [Ext.IPAddr.IPNet.lt, UInt32.val_val_eq_toNat, Nat.lt_eq, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, not_false_eq_true, not_true_eq_false, imp_self]
    case V4 a₁ p₁ a₂ p₂ =>
      cases a₁ ; rename_i a₁ ; cases a₁
      cases a₂ ; rename_i a₂ ; cases a₂
      cases p₁ ; cases p₂
      simp only [Fin.mk.injEq]
      exact IPNet.lt_asymm
    case V6 a₁ p₁ a₂ p₂ =>
      cases a₁ ; cases a₂ ; cases p₁ ; cases p₂
      exact IPNet.lt_asymm
  transitive a b c := by
    intro h₁ h₂
    simp only [LT.lt] at h₁ h₂
    simp only [Ext.IPAddr.IPNet.lt, Nat.lt_eq] at h₁ h₂
    split at h₁ <;> split at h₂ <;>
    simp only [LT.lt] <;> simp only [Ext.IPAddr.IPNet.V6.injEq, Nat.lt_eq, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Ext.IPAddr.IPNet.V4.injEq, Ext.IPAddr.IPNet.lt, UInt32.val_val_eq_toNat] at * <;>
    rename_i h₃ <;>
    have ⟨h₃, h₄⟩ := h₃ <;> subst h₃ h₄
    case h_3 a₁ p₁ a₂ p₂ _ _ a₃ p₃ =>
      cases a₁ ; rename_i a₁ ; cases a₁
      cases a₂ ; rename_i a₂ ; cases a₂
      cases a₃ ; rename_i a₃ ; cases a₃
      cases p₁ ; cases p₂ ; cases p₃
      simp only [Fin.mk.injEq] at *
      exact IPNet.lt_trans h₁ h₂
    case h_4 a₁ p₁ a₂ p₂ _ _ a₃ p₃ =>
      cases a₁ ; cases a₂ ; cases a₃ ; cases p₁ ; cases p₂ ; cases p₃
      simp only at *
      exact IPNet.lt_trans h₁ h₂
  connected  a b   := by
    cases a <;> cases b <;> simp only [LT.lt] <;> simp only [Ext.IPAddr.IPNet.lt, ne_eq, Bool.or_eq_true, or_false, UInt32.val_val_eq_toNat, not_and, not_false_eq_true, imp_self, Bool.and_eq_true, Ext.IPAddr.IPNet.V6.injEq, Ext.IPAddr.IPNet.V4.injEq, decide_eq_true_eq, or_true, Nat.lt_eq] <;> intro h₁
    case V4 a₁ p₁ a₂ p₂ =>
      cases a₁ ; rename_i a₁ ; cases a₁
      cases a₂ ; rename_i a₂ ; cases a₂
      cases p₁ ; cases p₂
      simp only [Fin.mk.injEq] at *
      rename_i a₁ _ a₂ _ p₁ _ p₂ _
      apply IPNet.lt_conn
      intro h₂
      simp only [UInt32.toNat] at h₂
      simp only [h₂, forall_const] at h₁
      exact h₁
    case V6 a₁ p₁ a₂ p₂ =>
      cases a₁ ; cases a₂ ; cases p₁ ; cases p₂
      simp only [Fin.mk.injEq] at *
      exact IPNet.lt_conn h₁


----- `<` is strict on `Ext` -----

instance Ext.strictLT : StrictLT Ext where
  asymmetric a b   := by
    cases a <;> cases b <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ <;> intro h₁
    case decimal =>
      have h₂ := Int64.strictLT.asymmetric x₁ x₂
      simp [LT.lt] at h₂
      cases h₃ : Int64.lt x₁ x₂ <;>
      simp [h₃] at h₁ h₂ ; simp [h₂]
    case ipaddr =>
      have h₂ := IPNet.strictLT.asymmetric x₁ x₂
      simp [LT.lt] at h₂
      cases h₃ : Ext.IPAddr.IPNet.lt x₁ x₂ <;>
      simp [h₃] at h₁ h₂ ; simp [h₂]
  transitive a b c := by
    cases a <;> cases b <;> cases c <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ x₃ <;> intro h₁ h₂
    case decimal =>
      have h₃ := Int64.strictLT.transitive x₁ x₂ x₃
      simp [LT.lt] at h₃
      cases h₄ : Int64.lt x₁ x₂ <;> simp [h₄] at *
      cases h₅ : Int64.lt x₂ x₃ <;> simp [h₅] at *
      simp [h₃]
    case ipaddr =>
      have h₃ := IPNet.strictLT.transitive x₁ x₂ x₃
      simp [LT.lt] at h₃
      cases h₄ : Ext.IPAddr.IPNet.lt x₁ x₂ <;> simp [h₄] at *
      cases h₅ : Ext.IPAddr.IPNet.lt x₂ x₃ <;> simp [h₅] at *
      simp [h₃]
  connected  a b   := by
    cases a <;> cases b <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ <;> intro h₁
    case decimal =>
      have h₂ := Int64.strictLT.connected x₁ x₂
      simp [LT.lt, h₁] at h₂
      rcases h₂ with h₂ | h₂ <;> simp [h₂]
    case ipaddr =>
      have h₂ := IPNet.strictLT.connected x₁ x₂
      simp [LT.lt, h₁] at h₂
      rcases h₂ with h₂ | h₂ <;> simp [h₂]

----- `<` is strict on `Name` -----

instance Name.strictLT : StrictLT Name where
  asymmetric a b   := by
    simp [LT.lt, Name.lt]
    apply List.lt_asymm
  transitive a b c := by
    simp [LT.lt, Name.lt]
    apply List.lt_trans
  connected  a b   := by
    simp [LT.lt, Name.lt]
    intro h₁
    apply List.lt_conn
    by_contra h₂
    simp at h₂
    cases a; cases b
    simp at *
    simp [h₂] at h₁

----- `<` is strict on `EntityUID` -----

theorem EntityUID.lt_asymm {a b : EntityUID} :
  a < b → ¬ b < a
:= by
  simp [LT.lt, EntityUID.lt]
  intro h₁
  by_contra h₂
  have h₃ := Name.strictLT.asymmetric a.ty b.ty
  simp [LT.lt] at h₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    simp only [h₁, h₂, forall_const] at h₃
  case inl.inr =>
    have ⟨h₂, _⟩ := h₂
    rw [h₂] at h₁ h₃
    simp [h₁] at h₃
  case inr.inl =>
    have h₄ := StrictLT.not_eq b.ty a.ty h₂
    simp [h₁] at h₄
  case inr.inr =>
    have h₄ := String.strictLT.asymmetric a.eid b.eid
    simp [LT.lt, h₁, h₂] at h₄

theorem EntityUID.lt_trans {a b c : EntityUID} :
  a < b → b < c → a < c
:= by
  simp [LT.lt, EntityUID.lt]
  intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    have h₃ := Name.strictLT.transitive a.ty b.ty c.ty h₁ h₂
    simp only [LT.lt] at h₃
    simp [h₃]
  case inl.inr =>
    have ⟨h₂, _⟩ := h₂
    simp [h₂] at h₁
    simp [h₁]
  case inr.inl =>
    have ⟨h₁, _⟩ := h₁
    simp [←h₁] at h₂
    simp [h₂]
  case inr.inr =>
    have ⟨hl₁, hr₁⟩ := h₁
    have ⟨hl₂, hr₂⟩ := h₂
    simp [hl₁] at * ; simp [hl₂] at *
    have h₃ := String.strictLT.transitive a.eid b.eid c.eid hr₁ hr₂
    simp only [LT.lt] at h₃
    simp [h₃]

theorem EntityUID.lt_conn {a b : EntityUID} :
  a ≠ b → (a < b ∨ b < a)
:= by
  cases a ; cases b ; rename_i ty₁ eid₁ ty₂ eid₂
  simp [LT.lt]
  intro h₁
  unfold EntityUID.lt
  by_cases (ty₁ = ty₂)
  case pos h₂ =>
    subst h₂ ; simp only [forall_const, true_and] at *
    simp [StrictLT.irreflexive ty₁]
    apply String.strictLT.connected
    simp [h₁]
  case neg h₂ =>
    have h₃ := Name.strictLT.connected ty₁ ty₂ h₂
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

instance EntityUID.strictLT : StrictLT EntityUID where
  asymmetric _ _   := EntityUID.lt_asymm
  transitive _ _ _ := EntityUID.lt_trans
  connected _ _    := EntityUID.lt_conn

----- `<` is strict on `Prim` -----

theorem Prim.lt_asymm {a b : Prim} :
  a < b → ¬ b < a
:= by
  cases a <;> cases b <;> simp [LT.lt] <;>
  simp [Prim.lt]
  case bool b₁ b₂          => exact Bool.strictLT.asymmetric b₁ b₂
  case int i₁ i₂           => exact (Int64.strictLT.asymmetric i₁ i₂)
  case string s₁ s₂        => exact (String.strictLT.asymmetric s₁ s₂)
  case entityUID uid₁ uid₂ => exact (EntityUID.strictLT.asymmetric uid₁ uid₂)

theorem Prim.lt_trans {a b c : Prim} :
  a < b → b < c → a < c
:= by
  cases a <;> cases b <;> cases c <;> simp [LT.lt] <;>
  simp [Prim.lt]
  case bool b₁ b₂ b₃            => exact (Bool.strictLT.transitive b₁ b₂ b₃)
  case int i₁ i₂ i₃             => exact (Int64.strictLT.transitive i₁ i₂ i₃)
  case string s₁ s₂ s₃          => exact (String.strictLT.transitive s₁ s₂ s₃)
  case entityUID uid₁ uid₂ uid₃ => exact (EntityUID.strictLT.transitive uid₁ uid₂ uid₃)

theorem Prim.lt_conn {a b : Prim} :
  a ≠ b → (a < b ∨ b < a)
:= by
  cases a <;> cases b <;> simp [LT.lt] <;>
  simp [Prim.lt]
  case bool b₁ b₂          => exact (Bool.strictLT.connected b₁ b₂)
  case int i₁ i₂           => exact (Int64.strictLT.connected i₁ i₂)
  case string s₁ s₂        => exact (String.strictLT.connected s₁ s₂)
  case entityUID uid₁ uid₂ => exact (EntityUID.strictLT.connected uid₁ uid₂)

instance Prim.strictLT : StrictLT Prim where
  asymmetric a b   := by exact Prim.lt_asymm
  transitive a b c := by exact Prim.lt_trans
  connected  a b   := by exact Prim.lt_conn

----- `<` is strict on `Value` -----

mutual
theorem Value.lt_irrefl (v : Value) :
  ¬ Value.lt v v
:= by
  cases v <;> simp [Value.lt] <;> rename_i w
  case prim => exact StrictLT.irreflexive w
  case set =>
    cases w ; rename_i ws ; simp [Value.lt]
    have h₁ := Values.lt_irrefl ws
    simp [h₁]
  case record =>
    cases w ; rename_i ws ; simp [Value.lt]
    have h₁ := ValueAttrs.lt_irrefl ws
    simp [h₁]
  case ext => exact StrictLT.irreflexive w

theorem Values.lt_irrefl (vs : List Value) :
  ¬ Values.lt vs vs
:= by
  cases vs ; simp [Values.lt] ; rename_i hd tl ; simp [Values.lt]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    have h₂ := Value.lt_irrefl hd
    simp [h₁] at h₂
  case inr =>
    have h₂ := Values.lt_irrefl tl
    simp [h₁] at h₂

theorem ValueAttrs.lt_irrefl (vs : List (Attr × Value)) :
  ¬ ValueAttrs.lt vs vs
:= by
  cases vs ; simp [ValueAttrs.lt] ; rename_i hd tl
  cases hd ; rename_i a v ; simp [ValueAttrs.lt]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    rcases h₁ with h₁ | h₁
    case inl =>
      have h₂ := StrictLT.irreflexive a
      contradiction
    case inr =>
      have h₂ := Value.lt_irrefl v
      contradiction
  case inr =>
    have h₂ := ValueAttrs.lt_irrefl tl
    contradiction

end

theorem Value.lt_not_eq {x y : Value} :
  x < y → ¬ x = y
:= by
  intro h₁
  by_contra h₂
  subst h₂
  have h₃ := Value.lt_irrefl x
  contradiction

mutual
theorem Value.lt_asymm {a b : Value} :
  a < b → ¬ b < a
:= by
  cases a <;> cases b <;> simp [LT.lt] <;> try simp [Value.lt]
  case prim p₁ p₂ => apply Prim.strictLT.asymmetric p₁ p₂
  case set s₁ s₂ =>
    cases s₁ ; cases s₂ ; rename_i vs₁ vs₂
    simp [Value.lt]
    intro h₁
    have h₂ := Values.lt_asym h₁
    simp [h₂]
  case record r₁ r₂ =>
    cases r₁ ; cases r₂ ; rename_i avs₁ avs₂
    simp [Value.lt]
    intro h₁
    have h₂ := ValueAttrs.lt_asym h₁
    simp [h₂]
  case ext x₁ x₂ => apply Ext.strictLT.asymmetric x₁ x₂

theorem Values.lt_asym {vs₁ vs₂: List Value} :
  Values.lt vs₁ vs₂ → ¬ Values.lt vs₂ vs₁
:= by
  cases vs₁ <;> cases vs₂ <;> simp [Values.lt]
  rename_i hd₁ tl₁ hd₂ tl₂
  intro h₁ ; rcases h₁ with h₁ | h₁
  case inl =>
    have h₂ := Value.lt_asymm h₁
    simp [LT.lt] at h₂
    simp [h₂] ; intro h₃ ; subst h₃
    simp [h₁] at h₂
  case inr =>
    have ⟨hl₁, h₂⟩ := h₁
    subst hl₁ ; simp only [true_and]
    have h₂ := Values.lt_asym h₂
    simp [h₂, Value.lt_irrefl hd₁]

theorem ValueAttrs.lt_asym {vs₁ vs₂: List (Attr × Value)} :
  ValueAttrs.lt vs₁ vs₂ → ¬ ValueAttrs.lt vs₂ vs₁
:= by
  cases vs₁ <;> cases vs₂ <;> simp [ValueAttrs.lt]
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂ ; simp [ValueAttrs.lt]
  rename_i a₁ v₁ a₂ v₂
  intro h₁ ; rcases h₁ with h₁ | h₁
  case inl =>
    rcases h₁ with h₁ | h₁
    case inl =>
      have h₂ := String.strictLT.asymmetric a₁ a₂ h₁
      have h₃ := StrictLT.not_eq a₁ a₂ h₁
      rw [eq_comm] at h₃
      simp [h₂, h₃]
    case inr =>
      have ⟨hl₁, h₂⟩ := h₁
      subst hl₁
      simp only [decide_True, Bool.true_and]
      have h₃ := Value.lt_asymm h₂
      simp [LT.lt] at h₃ ; simp [h₃]
      have h₄ := StrictLT.irreflexive a₁
      have h₅ := Value.lt_not_eq h₂
      rw [eq_comm] at h₅
      simp [h₄, h₅]
  case inr =>
    have ⟨h₂, h₃⟩ := h₁
    have ⟨hl₂, hr₂⟩ := h₂
    subst hl₂ hr₂
    simp only [decide_True, Bool.true_and, Bool.and_self]
    have h₃ := ValueAttrs.lt_asym h₃
    have h₄ := StrictLT.irreflexive a₁
    have h₅ := Value.lt_irrefl v₁
    simp [h₃, h₄, h₅]

end

mutual
theorem Value.lt_trans {a b c : Value} :
  a < b → b < c → a < c
:= by
  cases a <;> cases b <;> cases c <;> simp [LT.lt] <;> try simp [Value.lt]
  case prim p₁ p₂ p₃ => apply Prim.strictLT.transitive p₁ p₂ p₃
  case set s₁ s₂ s₃ =>
    cases s₁ ; cases s₂ ; cases s₃ ; rename_i vs₁ vs₂ vs₃
    simp [Value.lt]
    intro h₁ h₂
    apply Values.lt_trans h₁ h₂
  case record r₁ r₂ r₃ =>
    cases r₁ ; cases r₂ ; cases r₃ ; rename_i vs₁ vs₂ vs₃
    simp [Value.lt]
    intro h₁ h₂
    apply ValueAttrs.lt_trans h₁ h₂
  case ext x₁ x₂ x₃ => apply Ext.strictLT.transitive x₁ x₂ x₃


theorem Values.lt_trans {vs₁ vs₂ vs₃: List Value}
  (h₁ : Values.lt vs₁ vs₂)
  (h₂ : Values.lt vs₂ vs₃) :
  Values.lt vs₁ vs₃
:= by
  cases vs₁ <;> cases vs₂ <;> cases vs₃ <;> simp [Values.lt] at *
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    have h₃ := Value.lt_trans h₁ h₂
    simp [LT.lt] at h₃ ; simp [h₃]
  case inl.inr =>
    have ⟨h₂, _⟩ := h₂
    subst h₂ ; simp [h₁]
  case inr.inl =>
    have ⟨h₁, _⟩ := h₁
    subst h₁ ; simp [h₂]
  case inr.inr =>
    have ⟨hl₁, h₃⟩ := h₁ ; subst hl₁
    have ⟨hl₂, h₄⟩ := h₂ ; subst hl₂
    have h₃ := Values.lt_trans h₃ h₄
    simp [h₃]

theorem ValueAttrs.lt_trans {vs₁ vs₂ vs₃: List (Attr × Value)}
  (h₁ : ValueAttrs.lt vs₁ vs₂)
  (h₂ : ValueAttrs.lt vs₂ vs₃) :
  ValueAttrs.lt vs₁ vs₃
:= by
  cases vs₁ <;> cases vs₂ <;> cases vs₃ <;> try { simp [ValueAttrs.lt] at * }
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  cases hd₁ ; cases hd₂ ; cases hd₃ ; simp [ValueAttrs.lt] at *
  rename_i a₁ v₁ a₂ v₂ a₃ v₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    case inl.inl =>
      have h₃ := String.strictLT.transitive a₁ a₂ a₃ h₁ h₂
      simp [h₃]
    case inl.inr =>
      have ⟨h₂, _⟩ := h₂ ; subst h₂ ; simp [h₁]
    case inr.inl =>
      have ⟨h₁, _⟩ := h₁ ; subst h₁ ; simp [h₂]
    case inr.inr =>
      have ⟨hl₁, h₃⟩ := h₁ ; subst hl₁
      have ⟨hl₂, h₄⟩ := h₂ ; subst hl₂
      have h₃ := Value.lt_trans h₃ h₄
      simp [LT.lt] at h₃ ; simp [h₃]
  case inl.inr =>
    have ⟨⟨hl₂, hr₂⟩, _⟩ := h₂
    subst hl₂ hr₂
    simp [h₁]
  case inr.inl =>
    have ⟨⟨hl₁, hr₁⟩, _⟩ := h₁
    subst hl₁ hr₁
    simp [h₂]
  case inr.inr =>
    have ⟨⟨hl₁, hr₁⟩, h₃⟩ := h₁
    subst hl₁ hr₁
    have ⟨⟨hl₂, hr₂⟩, h₄⟩ := h₂
    subst hl₂ hr₂
    have h₅ := ValueAttrs.lt_trans h₃ h₄
    simp [h₅]
end

mutual
theorem Value.lt_conn {a b : Value} :
  a ≠ b → (a < b ∨ b < a)
:= by
  cases a <;> cases b <;> simp [LT.lt] <;> try simp [Value.lt]
  case prim p₁ p₂ => apply Prim.strictLT.connected p₁ p₂
  case set s₁ s₂ =>
    cases s₁ ; cases s₂ ; rename_i vs₁ vs₂
    simp [Value.lt]
    intro h₁
    apply Values.lt_conn h₁
  case record r₁ r₂ =>
    cases r₁ ; cases r₂ ; rename_i vs₁ vs₂
    simp [Value.lt]
    intro h₁
    apply ValueAttrs.lt_conn h₁
  case ext x₁ x₂ => apply Ext.strictLT.connected x₁ x₂


theorem Values.lt_conn {vs₁ vs₂ : List Value}
  (h₁ : ¬vs₁ = vs₂) :
  Values.lt vs₁ vs₂ ∨ Values.lt vs₂ vs₁
:= by
  cases vs₁ <;> cases vs₂ <;> simp [Values.lt] <;> try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  simp only [List.cons.injEq, not_and] at h₁
  by_cases h₂ : (hd₁ = hd₂)
  case pos =>
    simp [h₂] at *
    have h₃ := Values.lt_conn h₁
    rcases h₃ with h₃ | h₃ <;> simp [h₃]
  case neg =>
    have h₃ := Value.lt_conn h₂
    simp [LT.lt] at h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

theorem ValueAttrs.lt_conn {vs₁ vs₂ : List (Attr × Value)}
  (h₁ : ¬vs₁ = vs₂) :
  ValueAttrs.lt vs₁ vs₂ ∨ ValueAttrs.lt vs₂ vs₁
:= by
  cases vs₁ <;> cases vs₂ <;> try { simp [ValueAttrs.lt] } <;> try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂ ; simp [ValueAttrs.lt]
  rename_i a₁ v₁ a₂ v₂
  simp only [List.cons.injEq, Prod.mk.injEq, not_and, and_imp] at h₁
  by_cases h₂ : (a₁ = a₂)
  case pos =>
    subst h₂ ; simp only [forall_const, true_and] at *
    by_cases h₃ : (v₁ = v₂)
    case pos =>
      subst h₃ ; simp only [forall_const, true_and] at *
      have h₂ := ValueAttrs.lt_conn h₁
      rcases h₂ with h₂ | h₂ <;> simp [h₂]
    case neg =>
      have h₄ := Value.lt_conn h₃
      simp [LT.lt] at h₄
      rcases h₄ with h₄ | h₄ <;> simp [h₄]
  case neg =>
    have h₃ := String.strictLT.connected a₁ a₂
    simp [h₂] at h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

end

instance Value.strictLT : StrictLT Value where
  asymmetric a b   := by exact Value.lt_asymm
  transitive a b c := by exact Value.lt_trans
  connected  a b   := by exact Value.lt_conn

end Cedar.Thm
