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

import Cedar.Validation

namespace Cedar.Thm

/-!
This file contains some simple lemmas about the `checkLevel` and `typedAtLevel`
functions that do not need reason about the slicing functions.
-/

open Cedar.Validation
open Cedar.Data
open Cedar.Spec

def DereferencingBinaryOp : BinaryOp → Prop
  | .mem | .hasTag | .getTag => True
  | _ => False

mutual

inductive TypedExpr.EntityAccessAtLevel : TypedExpr → Nat → Nat → List Attr → Prop where
  | var (v : Var) (ty : CedarType) (n nmax : Nat) (path : List Attr):
    EntityAccessAtLevel  (.var v ty) n nmax path
  | ite (tx₁ tx₂ tx₃ : TypedExpr) (ty : CedarType) (n nmax : Nat) (path : List Attr)
    (hl₁ : AtLevel tx₁ nmax)
    (hl₂ : EntityAccessAtLevel tx₂ n nmax path)
    (hl₃ : EntityAccessAtLevel tx₃ n nmax path) :
    EntityAccessAtLevel (.ite tx₁ tx₂ tx₃ ty) n nmax path
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n nmax : Nat) (path : List Attr)
    (hl₁ : EntityAccessAtLevel tx₁ n nmax [])
    (hl₂ : AtLevel tx₂ nmax) :
    EntityAccessAtLevel (.binaryApp .getTag tx₁ tx₂ ty) (n + 1) nmax path
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (n nmax : Nat) {path : List Attr}
    (hl₁ : EntityAccessAtLevel tx₁ n nmax [])
    (hty : tx₁.typeOf = .entity ety) :
    EntityAccessAtLevel (.getAttr tx₁ a ty) (n + 1) nmax path
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n nmax : Nat) {path : List Attr}
    (hl₁ : EntityAccessAtLevel tx₁ n nmax (a :: path))
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    EntityAccessAtLevel (.getAttr tx₁ a ty) n nmax path
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType) (n nmax : Nat) {a : Attr} {path : List Attr}
    (hl₁ : ∀ atx ∈ attrs, AtLevel atx.snd nmax)
    (hf : (Map.make attrs).find? a = some tx)
    (hl₂ : EntityAccessAtLevel tx n nmax path) :
    EntityAccessAtLevel (.record attrs ty) n nmax (a :: path)

inductive TypedExpr.AtLevel : TypedExpr → Nat → Prop where
  | lit (p : Prim) (ty : CedarType) (n : Nat) :
    AtLevel (.lit p ty) n
  | var (v : Var) (ty : CedarType) (n : Nat) :
    AtLevel (.var v ty) n
  | ite (tx₁ tx₂ tx₃ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ n)
    (hl₃ : AtLevel tx₃ n) :
    AtLevel (.ite tx₁ tx₂ tx₃ ty) n
  | and (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ n) :
    AtLevel (.and tx₁ tx₂ ty) n
  | or (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ n) :
    AtLevel (.or tx₁ tx₂ ty) n
  | unaryApp (op : UnaryOp) (tx₁ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : AtLevel tx₁ n) :
    AtLevel (.unaryApp op tx₁ ty) n
  | mem (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ n (n + 1) [])
    (hl₂ : AtLevel tx₂ (n + 1)) :
    AtLevel (.binaryApp .mem tx₁ tx₂ ty) (n + 1)
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ n (n + 1) [])
    (hl₂ : AtLevel tx₂ (n + 1)) :
    AtLevel (.binaryApp .getTag tx₁ tx₂ ty) (n + 1)
  | hasTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ n (n + 1) [])
    (hl₂ : AtLevel tx₂ (n + 1)) :
    AtLevel (.binaryApp .hasTag tx₁ tx₂ ty) (n + 1)
  | binaryApp (op : BinaryOp) (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hop : ¬ DereferencingBinaryOp op)
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ n) :
    AtLevel (.binaryApp op tx₁ tx₂ ty) n
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ n (n + 1) [])
    (hty : tx₁.typeOf = .entity ety) :
    AtLevel (.getAttr tx₁ a ty) (n + 1)
  | hasAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ n (n + 1) [])
    (hty : tx₁.typeOf = .entity ety) :
    AtLevel (.hasAttr tx₁ a ty) (n + 1)
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (hl₁ : AtLevel tx₁ n)
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    AtLevel (.getAttr tx₁ a ty) n
  | hasAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (hl₁ : AtLevel tx₁ n)
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    AtLevel (.hasAttr tx₁ a ty) n
  | set (txs : List TypedExpr) (ty : CedarType) (n : Nat)
    (hl : ∀ tx ∈ txs, AtLevel tx n) :
    AtLevel (.set txs ty) n
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType) (n : Nat)
    (hl : ∀ atx ∈ attrs, AtLevel atx.snd n) :
    AtLevel (.record attrs ty) n
  | call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType) (n : Nat)
    (hl : ∀ tx ∈ args, AtLevel tx n) :
    AtLevel (.call xfn args ty) n
end


theorem entity_access_at_level_succ {tx : TypedExpr} {n n' : Nat}
  (h₁ : TypedExpr.EntityAccessAtLevel tx n n' path) :
  TypedExpr.EntityAccessAtLevel tx (n + 1) n' path
:= by
  cases h₁
  case record tx attrs _ ha _ _ _ _ =>
    apply TypedExpr.EntityAccessAtLevel.record
    · assumption
    · assumption
    · rename_i path hf _ hl
      have : sizeOf tx < sizeOf attrs := by
        have h₁ := List.sizeOf_lt_of_mem ∘ Map.make_mem_list_mem ∘ Map.find?_mem_toList $ hf
        rw [Prod.mk.sizeOf_spec ha tx] at h₁
        omega
      exact entity_access_at_level_succ hl

  case getAttrRecord h₁ h₂ =>
    have h₃ := entity_access_at_level_succ h₂
    apply TypedExpr.EntityAccessAtLevel.getAttrRecord <;> assumption
  all_goals
    constructor <;> first
    | assumption
    | exact entity_access_at_level_succ (by assumption)
termination_by tx

theorem entity_access_at_level_then_at_level {tx : TypedExpr} {n : Nat} {path : List Attr}
  (h₁ : TypedExpr.EntityAccessAtLevel tx n (n + 1) path) :
  TypedExpr.AtLevel tx (n + 1)
:= by
  cases h₁
  case getAttrRecord =>
    apply TypedExpr.AtLevel.getAttrRecord
    · apply entity_access_at_level_then_at_level
      assumption
    · assumption
  all_goals
    constructor <;>
    first
    | assumption
    | exact entity_access_at_level_succ (by assumption)
    | exact entity_access_at_level_then_at_level (by assumption)
termination_by tx

mutual

theorem entity_access_level_spec {tx : TypedExpr} {n nmax : Nat} {path : List Attr} :
  (TypedExpr.EntityAccessAtLevel tx n nmax path) ↔ (checkEntityAccessLevel tx n nmax path)
:= by
  cases tx
  case var =>
    simp [checkEntityAccessLevel]
    constructor
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @entity_access_level_spec tx₂
    have ih₃ := @entity_access_level_spec tx₃
    simp [checkEntityAccessLevel]
    rw [←ih₁, ←ih₂, ←ih₃]
    apply Iff.intro
    · intro hl; cases hl
      and_intros <;> assumption
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      constructor <;> assumption
  case binaryApp op tx₁ tx₂ _ =>
    cases op
    case getTag =>
      have ih₁ := @entity_access_level_spec tx₁
      have ih₂ := @level_spec tx₂
      simp [checkEntityAccessLevel]
      rw [←ih₁, ←ih₂]
      apply Iff.intro
      · intro hl; cases hl
        and_intros <;> first
          | assumption
          | simp only [Nat.zero_lt_succ]
      · intro ⟨ ⟨h₁, h₂⟩, h₃ ⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
        subst n
        constructor <;> assumption
    all_goals
      simp only [checkEntityAccessLevel, Bool.false_eq_true, iff_false]
      intro hc
      cases hc
  case getAttr tx₁ a ty =>
    simp [checkEntityAccessLevel]
    split
    · have ih₁ := @entity_access_level_spec tx₁
      simp [←ih₁]
      apply Iff.intro
      · intro hl
        cases hl
        · apply And.intro
          · simp only [Nat.zero_lt_succ]
          · simp only [Nat.add_one_sub_one]
            assumption
        · rename_i h₂ h₁ _
          simp [h₂] at h₁
      · intro ⟨h₁, h₂⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
        subst n
        apply TypedExpr.EntityAccessAtLevel.getAttr
        · simp at h₂
          assumption
        · assumption
    · have ih₁ := @entity_access_level_spec tx₁
      simp [←ih₁]
      apply Iff.intro
      · intro hl
        cases hl
        · rename_i h₁ _ _ h₂ _
          simp [h₂] at h₁
        · assumption
      · intro hl
        apply TypedExpr.EntityAccessAtLevel.getAttrRecord <;> assumption
  case record atxs _ =>
    cases path
    case nil =>
      simp [checkEntityAccessLevel]
      intro hc
      cases hc
    case cons =>
      simp [checkEntityAccessLevel]
      split <;> simp
      · apply Iff.intro
        · intro hl
          cases hl
          rename_i tx h₁ tx' h₃ h₄ h₅
          rw [h₁] at h₄
          simp at h₄
          subst tx
          and_intros
          · have : sizeOf tx' < 1 + sizeOf atxs := by
              replace h₁ := List.sizeOf_lt_of_mem ∘ Map.make_mem_list_mem ∘ Map.find?_mem_toList $ h₁
              rw [Prod.mk.sizeOf_spec _ tx'] at h₁
              omega
            have ih := @entity_access_level_spec tx'
            rw [←ih]
            assumption
          · intros
            rename_i a tx h₂
            have : sizeOf tx < 1 + sizeOf atxs := by
              have h₄ := List.sizeOf_lt_of_mem h₂
              rw [Prod.mk.sizeOf_spec a tx] at h₄
              omega
            have ih := @level_spec tx
            rw [←ih]
            specialize h₃ (a, tx) h₂
            simpa using h₃
        · intro ⟨ h₁, h₂ ⟩
          constructor
          · intro atx hatx
            specialize h₂ atx.fst atx.snd hatx
            have : sizeOf atx.snd < 1 + sizeOf atxs := by
              have h₄ := List.sizeOf_lt_of_mem hatx
              rw [Prod.mk.sizeOf_spec _ atx.snd] at h₄
              omega
            have ih := @level_spec atx.snd
            rw [ih]
            assumption
          · assumption
          · rename_i a _ tx hf
            have : sizeOf tx < 1 + sizeOf atxs := by
              replace h₁ := List.sizeOf_lt_of_mem ∘ Map.make_mem_list_mem ∘ Map.find?_mem_toList $ hf
              rw [Prod.mk.sizeOf_spec _ tx] at h₁
              omega
            have ih := @entity_access_level_spec tx
            rw [ih]
            assumption
      · intro hc
        cases hc
        rename_i h₁ _  _ h₂ _
        simp [h₁] at h₂
  all_goals
    simp only [checkEntityAccessLevel, Bool.false_eq_true, iff_false]
    intro hc
    cases hc
termination_by tx

theorem level_spec {tx : TypedExpr} {n : Nat}:
  (TypedExpr.AtLevel tx n) ↔ (checkLevel tx n = true)
:= by
  cases tx
  case lit =>
    simp [checkLevel]
    constructor
  case var =>
    simp [checkLevel]
    constructor
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @level_spec tx₂
    have ih₃ := @level_spec tx₃
    simp [checkLevel]
    rw [←ih₁, ←ih₂, ←ih₃]
    apply Iff.intro
    · intros h
      cases h
      and_intros <;> assumption
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      constructor <;> assumption

  case or tx₁ tx₂ _ | and tx₁ tx₂ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @level_spec tx₂
    simp [checkLevel]
    rw [←ih₁, ←ih₂]
    apply Iff.intro
    · intro h
      cases h
      constructor <;> assumption
    · intro ⟨ h₁, h₂ ⟩
      constructor <;> assumption

  case unaryApp op tx₁ _ =>
    have ih₁ := @level_spec tx₁
    simp [checkLevel]
    rw [←ih₁]
    apply Iff.intro
    · intro h
      cases h
      assumption
    · intro h₁
      constructor
      assumption

  case binaryApp op tx₁ tx₂ _ =>
    cases op
    case getTag | hasTag | mem =>
      have ih₁ := @entity_access_level_spec tx₁
      have ih₂ := @level_spec tx₂
      simp [checkLevel]
      rw [←ih₁, ←ih₂]
      apply Iff.intro
      · intro h
        cases h
        rename_i h₁ h₂ h₃
        and_intros <;> (
          try simp
          try assumption
        )
        rename_i hop _ _
        simp [DereferencingBinaryOp] at hop
      · intro ⟨ ⟨ h₁, h₂⟩, h₃ ⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
        subst n
        constructor <;> assumption
    all_goals
      have ih₁ := @level_spec tx₁
      have ih₂ := @level_spec tx₂
      simp only [checkLevel, Bool.and_eq_true]
      rw [←ih₁, ←ih₂]
      apply Iff.intro
      · intro h
        cases h
        apply And.intro <;> assumption
      · intro ⟨ h₁, h₂ ⟩
        constructor <;> first
        | simp only [DereferencingBinaryOp, not_false_eq_true]
        | assumption

  case getAttr tx₁ a _  | hasAttr tx₁ a _  =>
    simp [checkLevel]
    split
    · apply Iff.intro
      · intro h
        cases h <;> simp [*] at *
        rename_i n _ _ _ _
        have ih₁ := @entity_access_level_spec tx₁
        rw [←ih₁]
        assumption
      · have ih₁ := @entity_access_level_spec tx₁
        simp
        rw [←ih₁]
        intro h₁ h₂
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
        subst n
        constructor <;> assumption
    · apply Iff.intro
      · intro h
        cases h <;> simp [*] at *
        have ih₁ := @level_spec tx₁
        rw [←ih₁]
        assumption
      · intro h
        have ih₁ := @level_spec tx₁
        rw [←ih₁] at h
        constructor <;> assumption

  case call | set =>
    simp [checkLevel]
    apply Iff.intro
    · intro h₁ tx h₂
      have ih := @level_spec tx
      cases h₁
      rename_i h₃
      specialize h₃ tx h₂
      rw [←ih]
      exact h₃
    · intro h₁
      constructor
      intro tx h₂
      have _ := List.sizeOf_lt_of_mem h₂
      have ih := @level_spec tx
      rw [ih]
      exact h₁ tx h₂

  case record attrs _ =>
    simp [checkLevel]
    apply Iff.intro
    · intro h₁ a tx h₂
      cases h₁
      rename_i h₃
      specialize h₃ (a, tx) h₂
      simp at h₃
      have : sizeOf tx < 1 + sizeOf attrs := by
        have h₄ := List.sizeOf_lt_of_mem h₂
        rw [Prod.mk.sizeOf_spec a tx] at h₄
        omega
      have ih := @level_spec tx
      rw [←ih]
      exact h₃
    · intro h₁
      constructor
      intro atx h₂
      specialize h₁ atx.fst atx.snd h₂
      have : sizeOf atx.snd < 1 + sizeOf attrs := by
        have h₄ := List.sizeOf_lt_of_mem h₂
        rw [Prod.mk.sizeOf_spec atx.fst atx.snd] at h₄
        omega
      have ih := @level_spec atx.snd
      rw [ih]
      exact h₁
termination_by tx

end
