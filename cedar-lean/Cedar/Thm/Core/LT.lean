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
:= by
  intro h₁
  rcases h₁ with h₁ | h₁ <;> by_contra h₂
  case inl =>
    rcases h₂ with h₂ | h₂
    case inl =>
      rcases (Nat.lt_asymm h₁) with h₂
      contradiction
    case inr =>
      rcases (StrictLT.not_eq a₁ a₂ h₁) with h₃
      rw [eq_comm] at h₃
      simp [h₃] at h₂
  case inr =>
    simp [h₁] at h₂
    rcases h₁ with ⟨_, h₁⟩
    rcases (Nat.lt_asymm h₁) with h₃
    contradiction

theorem IPNet.lt_trans {a₁ a₂ a₃ p₁ p₂ p₃ : Nat}
  (h₁ : a₁ < a₂ ∨ a₁ = a₂ ∧ p₁ < p₂)
  (h₂ : a₂ < a₃ ∨ a₂ = a₃ ∧ p₂ < p₃) :
  a₁ < a₃ ∨ a₁ = a₃ ∧ p₁ < p₃
:= by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases (Nat.lt_trans h₁ h₂) with h₃ ; simp [h₃]
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩ ; subst h₂ ; simp [h₁]
  case inr.inl =>
    rcases h₁ with ⟨h₁, _⟩ ; subst h₁ ; simp [h₂]
  case inr.inr =>
    rcases h₁ with ⟨hl₁, h₁⟩ ; subst hl₁
    rcases h₂ with ⟨hl₂, h₂⟩ ; subst hl₂
    rcases (Nat.lt_trans h₁ h₂) with h₃ ; simp [h₃]

theorem IPNet.lt_conn {a₁ a₂ p₁ p₂ : Nat}
  (h₁ : a₁ = a₂ → ¬p₁ = p₂) :
  (a₁ < a₂ ∨ a₁ = a₂ ∧ p₁ < p₂) ∨ a₂ < a₁ ∨ a₂ = a₁ ∧ p₂ < p₁
:= by
  rcases (Nat.lt_trichotomy a₁ a₂) with h₂
  rcases h₂ with h₂ | h₂ | h₂ <;> simp [h₂]
  simp [h₂] at h₁
  apply Nat.strictLT.connected ; simp [h₁]

instance IPNet.strictLT : StrictLT Ext.IPAddr.IPNet where
  asymmetric a b   := by
    cases a <;> cases b <;> simp [LT.lt, Ext.IPAddr.IPNet.lt]
    case V4 a₁ p₁ a₂ p₂ =>
      cases a₁ ; rename_i a₁ ; cases a₁
      cases a₂ ; rename_i a₂ ; cases a₂
      cases p₁ ; cases p₂
      simp only [Fin.mk.injEq]
      exact IPNet.lt_asymm
    case V6 a₁ p₁ a₂ p₂ =>
      cases a₁ ; cases a₂ ; cases p₁ ; cases p₂
      simp only
      exact IPNet.lt_asymm
  transitive a b c := by
    intro h₁ h₂
    simp [LT.lt, Ext.IPAddr.IPNet.lt] at h₁ h₂ ; split at h₁ <;> split at h₂ <;>
    simp [LT.lt, Ext.IPAddr.IPNet.lt] at * <;>
    rename_i h₃ <;>
    rcases h₃ with ⟨h₃, h₄⟩ <;> subst h₃ h₄
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
    cases a <;> cases b <;> simp [LT.lt, Ext.IPAddr.IPNet.lt] <;> intro h₁
    case V4 a₁ p₁ a₂ p₂ =>
      cases a₁ ; rename_i a₁ ; cases a₁
      cases a₂ ; rename_i a₂ ; cases a₂
      cases p₁ ; cases p₂
      simp at *
      rename_i a₁ _ a₂ _ p₁ _ p₂ _
      apply IPNet.lt_conn
      intro h₂ ; simp [h₂] at h₁ ; exact h₁
    case V6 a₁ p₁ a₂ p₂ =>
      cases a₁ ; cases a₂ ; cases p₁ ; cases p₂
      simp at *
      exact IPNet.lt_conn h₁

----- `<` is strict on `Ext` -----

instance Ext.strictLT : StrictLT Ext where
  asymmetric a b   := by
    cases a <;> cases b <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ <;> intro h₁
    case decimal =>
      rcases (Int64.strictLT.asymmetric x₁ x₂) with h₂
      simp [LT.lt] at h₂
      cases h₃ : Int64.lt x₁ x₂ <;>
      simp [h₃] at h₁ h₂ ; simp [h₂]
    case ipaddr =>
      rcases (IPNet.strictLT.asymmetric x₁ x₂) with h₂
      simp [LT.lt] at h₂
      cases h₃ : Ext.IPAddr.IPNet.lt x₁ x₂ <;>
      simp [h₃] at h₁ h₂ ; simp [h₂]
  transitive a b c := by
    cases a <;> cases b <;> cases c <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ x₃ <;> intro h₁ h₂
    case decimal =>
      rcases (Int64.strictLT.transitive x₁ x₂ x₃) with h₃
      simp [LT.lt] at h₃
      cases h₄ : Int64.lt x₁ x₂ <;> simp [h₄] at *
      cases h₅ : Int64.lt x₂ x₃ <;> simp [h₅] at *
      simp [h₃]
    case ipaddr =>
      rcases (IPNet.strictLT.transitive x₁ x₂ x₃) with h₃
      simp [LT.lt] at h₃
      cases h₄ : Ext.IPAddr.IPNet.lt x₁ x₂ <;> simp [h₄] at *
      cases h₅ : Ext.IPAddr.IPNet.lt x₂ x₃ <;> simp [h₅] at *
      simp [h₃]
  connected  a b   := by
    cases a <;> cases b <;> simp [LT.lt, Ext.lt] <;>
    rename_i x₁ x₂ <;> intro h₁
    case decimal =>
      rcases (Int64.strictLT.connected x₁ x₂) with h₂
      simp [LT.lt, h₁] at h₂
      rcases h₂ with h₂ | h₂ <;> simp [h₂]
    case ipaddr =>
      rcases (IPNet.strictLT.connected x₁ x₂) with h₂
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
  rcases (Name.strictLT.asymmetric a.ty b.ty) with h₃
  simp [LT.lt] at h₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    simp only [h₁, h₂, forall_const] at h₃
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩
    rw [h₂] at h₁ h₃
    simp [h₁] at h₃
  case inr.inl =>
    rcases (StrictLT.not_eq b.ty a.ty h₂) with h₄
    simp [h₁] at h₄
  case inr.inr =>
    rcases (String.strictLT.asymmetric a.eid b.eid) with h₄
    simp [LT.lt, h₁, h₂] at h₄

theorem EntityUID.lt_trans {a b c : EntityUID} :
  a < b → b < c → a < c
:= by
  simp [LT.lt, EntityUID.lt]
  intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases (Name.strictLT.transitive a.ty b.ty c.ty h₁ h₂) with h₃
    simp only [LT.lt] at h₃
    simp [h₃]
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩
    simp [h₂] at h₁
    simp [h₁]
  case inr.inl =>
    rcases h₁ with ⟨h₁, _⟩
    simp [←h₁] at h₂
    simp [h₂]
  case inr.inr =>
    rcases h₁ with ⟨hl₁, hr₁⟩
    rcases h₂ with ⟨hl₂, hr₂⟩
    simp [hl₁] at * ; simp [hl₂] at *
    rcases (String.strictLT.transitive a.eid b.eid c.eid hr₁ hr₂) with h₃
    simp only [LT.lt] at h₃
    simp [h₃]

theorem EntityUID.lt_conn {a b : EntityUID} :
  a ≠ b → (a < b ∨ b < a)
:= by
  cases a ; cases b ; rename_i ty₁ eid₁ ty₂ eid₂
  simp [LT.lt]
  intro h₁
  simp [EntityUID.lt]
  by_cases (ty₁ = ty₂)
  case pos h₂ =>
    subst h₂ ; simp only [forall_const, true_and] at *
    simp [StrictLT.irreflexive ty₁]
    apply String.strictLT.connected
    simp [h₁]
  case neg h₂ =>
    rcases (Name.strictLT.connected ty₁ ty₂ h₂) with h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

instance EntityUID.strictLT : StrictLT EntityUID where
  asymmetric a b   := by exact EntityUID.lt_asymm
  transitive a b c := by exact EntityUID.lt_trans
  connected a b    := by exact EntityUID.lt_conn

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
    rcases (Values.lt_irrefl ws) with h₁
    simp [h₁]
  case record =>
    cases w ; rename_i ws ; simp [Value.lt]
    rcases (ValueAttrs.lt_irrefl ws) with h₁
    simp [h₁]
  case ext => exact StrictLT.irreflexive w

theorem Values.lt_irrefl (vs : List Value) :
  ¬ Values.lt vs vs vs.length
:= by
  cases vs ; simp [Values.lt] ; rename_i hd tl ; simp [Values.lt]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    rcases (Value.lt_irrefl hd) with h₂
    simp [h₁] at h₂
  case inr =>
    rcases (Values.lt_irrefl tl) with h₂
    simp [h₁] at h₂

theorem ValueAttrs.lt_irrefl (vs : List (Attr × Value)) :
  ¬ ValueAttrs.lt vs vs vs.length
:= by
  cases vs ; simp [ValueAttrs.lt] ; rename_i hd tl
  cases hd ; rename_i a v ; simp [ValueAttrs.lt]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    rcases h₁ with h₁ | h₁
    case inl =>
      rcases (StrictLT.irreflexive a) with h₂
      contradiction
    case inr =>
      rcases (Value.lt_irrefl v) with h₂
      contradiction
  case inr =>
    rcases (ValueAttrs.lt_irrefl tl) with h₂
    contradiction

end

theorem Value.lt_not_eq {x y : Value} :
  x < y → ¬ x = y
:= by
  intro h₁
  by_contra h₂
  subst h₂
  rcases (Value.lt_irrefl x) with h₃
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
    rcases (Values.lt_asym h₁) with h₂
    simp [h₂]
  case record r₁ r₂ =>
    cases r₁ ; cases r₂ ; rename_i avs₁ avs₂
    simp [Value.lt]
    intro h₁
    rcases (ValueAttrs.lt_asym h₁) with h₂
    simp [h₂]
  case ext x₁ x₂ => apply Ext.strictLT.asymmetric x₁ x₂

theorem Values.lt_asym {vs₁ vs₂: List Value} :
  Values.lt vs₁ vs₂ vs₁.length → ¬ Values.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [Values.lt]
  rename_i hd₁ tl₁ hd₂ tl₂
  intro h₁ ; rcases h₁ with h₁ | h₁
  case inl =>
    rcases (Value.lt_asymm h₁) with h₂
    simp [LT.lt] at h₂
    simp [h₂] ; intro h₃ ; subst h₃
    simp [h₁] at h₂
  case inr =>
    rcases h₁ with ⟨hl₁, h₁⟩
    subst hl₁ ; simp only [true_and]
    rcases (Values.lt_asym h₁) with h₂
    simp [h₂, Value.lt_irrefl hd₁]

theorem ValueAttrs.lt_asym {vs₁ vs₂: List (Attr × Value)} :
  ValueAttrs.lt vs₁ vs₂ vs₁.length → ¬ ValueAttrs.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [ValueAttrs.lt]
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂ ; simp [ValueAttrs.lt]
  rename_i a₁ v₁ a₂ v₂
  intro h₁ ; rcases h₁ with h₁ | h₁
  case inl =>
    rcases h₁ with h₁ | h₁
    case inl =>
      rcases (String.strictLT.asymmetric a₁ a₂ h₁) with h₂
      rcases (StrictLT.not_eq a₁ a₂ h₁) with h₃
      rw [eq_comm] at h₃
      simp [h₂, h₃]
    case inr =>
      rcases h₁ with ⟨hl₁, h₁⟩ ; subst hl₁
      simp only [decide_True, Bool.true_and]
      rcases (Value.lt_asymm h₁) with h₂
      simp [LT.lt] at h₂ ; simp [h₂]
      rcases (StrictLT.irreflexive a₁) with h₃
      rcases (Value.lt_not_eq h₁) with h₄
      rw [eq_comm] at h₄
      simp [h₃, h₄]
  case inr =>
    rcases h₁ with ⟨h₂, h₁⟩
    rcases h₂ with ⟨hl₂, hr₂⟩ ; subst hl₂ hr₂
    simp only [decide_True, Bool.true_and, Bool.and_self]
    rcases (ValueAttrs.lt_asym h₁) with h₂
    rcases (StrictLT.irreflexive a₁) with h₃
    rcases (Value.lt_irrefl v₁) with h₄
    simp [h₂, h₃, h₄]

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
  (h₁ : Values.lt vs₁ vs₂ vs₁.length)
  (h₂ : Values.lt vs₂ vs₃ vs₂.length ) :
  Values.lt vs₁ vs₃ vs₁.length
:= by
  cases vs₁ <;> cases vs₂ <;> cases vs₃ <;> simp [Values.lt] at *
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases (Value.lt_trans h₁ h₂) with h₃
    simp [LT.lt] at h₃ ; simp [h₃]
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩ ; subst h₂ ; simp [h₁]
  case inr.inl =>
    rcases h₁ with ⟨h₁, _⟩ ; subst h₁ ; simp [h₂]
  case inr.inr =>
    rcases h₁ with ⟨hl₁, h₁⟩ ; subst hl₁
    rcases h₂ with ⟨hl₂, h₂⟩ ; subst hl₂
    rcases (Values.lt_trans h₁ h₂) with h₃
    simp [h₃]

theorem ValueAttrs.lt_trans {vs₁ vs₂ vs₃: List (Attr × Value)}
  (h₁ : ValueAttrs.lt vs₁ vs₂ vs₁.length)
  (h₂ : ValueAttrs.lt vs₂ vs₃ vs₂.length) :
  ValueAttrs.lt vs₁ vs₃ vs₁.length
:= by
  cases vs₁ <;> cases vs₂ <;> cases vs₃ <;> simp [ValueAttrs.lt] at *
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  cases hd₁ ; cases hd₂ ; cases hd₃ ; simp [ValueAttrs.lt] at *
  rename_i a₁ v₁ a₂ v₂ a₃ v₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    case inl.inl =>
      rcases (String.strictLT.transitive a₁ a₂ a₃ h₁ h₂) with h₃
      simp [h₃]
    case inl.inr =>
      rcases h₂ with ⟨h₂, _⟩ ; subst h₂ ; simp [h₁]
    case inr.inl =>
      rcases h₁ with ⟨h₁, _⟩ ; subst h₁ ; simp [h₂]
    case inr.inr =>
      rcases h₁ with ⟨hl₁, h₁⟩ ; subst hl₁
      rcases h₂ with ⟨hl₂, h₂⟩ ; subst hl₂
      rcases (Value.lt_trans h₁ h₂) with h₃
      simp [LT.lt] at h₃ ; simp [h₃]
  case inl.inr =>
    rcases h₂ with ⟨h₂, _⟩
    rcases h₂ with ⟨hl₂, hr₂⟩ ; subst hl₂ hr₂
    simp [h₁]
  case inr.inl =>
    rcases h₁ with ⟨h₁, _⟩
    rcases h₁ with ⟨hl₁, hr₁⟩ ; subst hl₁ hr₁
    simp [h₂]
  case inr.inr =>
    rcases h₁ with ⟨h₁, h₃⟩
    rcases h₁ with ⟨hl₁, hr₁⟩ ; subst hl₁ hr₁
    rcases h₂ with ⟨h₂, h₄⟩
    rcases h₂ with ⟨hl₂, hr₂⟩ ; subst hl₂ hr₂
    rcases (ValueAttrs.lt_trans h₃ h₄) with h₅
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
  Values.lt vs₁ vs₂ vs₁.length ∨ Values.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [Values.lt] <;> try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  simp only [List.cons.injEq, not_and] at h₁
  by_cases h₂ : (hd₁ = hd₂)
  case pos =>
    simp [h₂] at *
    rcases (Values.lt_conn h₁) with h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]
  case neg =>
    rcases (Value.lt_conn h₂) with h₃
    simp [LT.lt] at h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

theorem ValueAttrs.lt_conn {vs₁ vs₂ : List (Attr × Value)}
  (h₁ : ¬vs₁ = vs₂) :
  ValueAttrs.lt vs₁ vs₂ vs₁.length ∨ ValueAttrs.lt vs₂ vs₁ vs₂.length
:= by
  cases vs₁ <;> cases vs₂ <;> simp [ValueAttrs.lt] <;> try contradiction
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
      rcases (ValueAttrs.lt_conn h₁) with h₂
      rcases h₂ with h₂ | h₂ <;> simp [h₂]
    case neg =>
      rcases (Value.lt_conn h₃) with h₄
      simp [LT.lt] at h₄
      rcases h₄ with h₄ | h₄ <;> simp [h₄]
  case neg =>
    rcases (String.strictLT.connected a₁ a₂) with h₃
    simp [h₂] at h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

end

instance Value.strictLT : StrictLT Value where
  asymmetric a b   := by exact Value.lt_asymm
  transitive a b c := by exact Value.lt_trans
  connected  a b   := by exact Value.lt_conn

end Cedar.Thm
