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

inductive TypedExpr.EntityAccessAtLevel : TypedExpr → Environment → Nat → Nat → List Attr → Prop where
  | var (v : Var) (ty : CedarType) (env : Environment) (n nmax : Nat) (path : List Attr) :
    EntityAccessAtLevel  (.var v ty) env n nmax path
  | action (ty : CedarType) (env : Environment) (n nmax : Nat) (path : List Attr) :
    EntityAccessAtLevel  (.lit (.entityUID env.reqty.action) ty) env n nmax path
  | ite (tx₁ tx₂ tx₃ : TypedExpr) (ty : CedarType) (env : Environment) (n nmax : Nat) (path : List Attr)
    (hl₁ : AtLevel tx₁ env nmax)
    (hl₂ : EntityAccessAtLevel tx₂ env n nmax path)
    (hl₃ : EntityAccessAtLevel tx₃ env n nmax path) :
    EntityAccessAtLevel (.ite tx₁ tx₂ tx₃ ty) env n nmax path
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (env : Environment) (n nmax : Nat) (path : List Attr)
    (hl₁ : EntityAccessAtLevel tx₁ env n nmax [])
    (hl₂ : AtLevel tx₂ env nmax) :
    EntityAccessAtLevel (.binaryApp .getTag tx₁ tx₂ ty) env (n + 1) nmax path
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (env : Environment) {ety : EntityType} (n nmax : Nat) {path : List Attr}
    (hl₁ : EntityAccessAtLevel tx₁ env n nmax [])
    (hty : tx₁.typeOf = .entity ety) :
    EntityAccessAtLevel (.getAttr tx₁ a ty) env (n + 1) nmax path
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (env : Environment) (n nmax : Nat) {path : List Attr}
    (hl₁ : EntityAccessAtLevel tx₁ env n nmax (a :: path))
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    EntityAccessAtLevel (.getAttr tx₁ a ty) env n nmax path
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType) (env : Environment) (n nmax : Nat) {a : Attr} {path : List Attr}
    (hl₁ : ∀ atx ∈ attrs, AtLevel atx.snd env nmax)
    (hf : (Map.make attrs).find? a = some tx)
    (hl₂ : EntityAccessAtLevel tx env n nmax path) :
    EntityAccessAtLevel (.record attrs ty) env n nmax (a :: path)

inductive TypedExpr.AtLevel : TypedExpr → Environment → Nat → Prop where
  | lit (p : Prim) (ty : CedarType) (env : Environment) (n : Nat) :
    AtLevel (.lit p ty) env n
  | var (v : Var) (ty : CedarType) (env : Environment) (n : Nat) :
    AtLevel (.var v ty) env n
  | ite (tx₁ tx₂ tx₃ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : AtLevel tx₁ env n)
    (hl₂ : AtLevel tx₂ env n)
    (hl₃ : AtLevel tx₃ env n) :
    AtLevel (.ite tx₁ tx₂ tx₃ ty) env n
  | and (tx₁ tx₂ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : AtLevel tx₁ env n)
    (hl₂ : AtLevel tx₂ env n) :
    AtLevel (.and tx₁ tx₂ ty) env n
  | or (tx₁ tx₂ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : AtLevel tx₁ env n)
    (hl₂ : AtLevel tx₂ env n) :
    AtLevel (.or tx₁ tx₂ ty) env n
  | unaryApp (op : UnaryOp) (tx₁ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : AtLevel tx₁ env n) :
    AtLevel (.unaryApp op tx₁ ty) env n
  | mem (tx₁ tx₂ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ env n (n + 1) [])
    (hl₂ : AtLevel tx₂ (env : Environment) (n + 1)) :
    AtLevel (.binaryApp .mem tx₁ tx₂ ty) (env : Environment) (n + 1)
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ env n (n + 1) [])
    (hl₂ : AtLevel tx₂ (env : Environment) (n + 1)) :
    AtLevel (.binaryApp .getTag tx₁ tx₂ ty) (env : Environment) (n + 1)
  | hasTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ env n (n + 1) [])
    (hl₂ : AtLevel tx₂ (env : Environment) (n + 1)) :
    AtLevel (.binaryApp .hasTag tx₁ tx₂ ty) (env : Environment) (n + 1)
  | binaryApp (op : BinaryOp) (tx₁ tx₂ : TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hop : ¬ DereferencingBinaryOp op)
    (hl₁ : AtLevel tx₁ env n)
    (hl₂ : AtLevel tx₂ env n) :
    AtLevel (.binaryApp op tx₁ tx₂ ty) env n
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (env : Environment) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ env n (n + 1) [])
    (hty : tx₁.typeOf = .entity ety) :
    AtLevel (.getAttr tx₁ a ty) (env : Environment) (n + 1)
  | hasAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (env : Environment) (n : Nat)
    (hl₁ : EntityAccessAtLevel tx₁ env n (n + 1) [])
    (hty : tx₁.typeOf = .entity ety) :
    AtLevel (.hasAttr tx₁ a ty) (env : Environment) (n + 1)
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : AtLevel tx₁ env n)
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    AtLevel (.getAttr tx₁ a ty) env n
  | hasAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl₁ : AtLevel tx₁ env n)
    (hty : ∀ ety, tx₁.typeOf ≠ .entity ety) :
    AtLevel (.hasAttr tx₁ a ty) env n
  | set (txs : List TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl : ∀ tx ∈ txs, AtLevel tx env n) :
    AtLevel (.set txs ty) env n
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType) (env : Environment) (n : Nat)
    (hl : ∀ atx ∈ attrs, AtLevel atx.snd env n) :
    AtLevel (.record attrs ty) env n
  | call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType) (env : Environment) (n : Nat)
    (hl : ∀ tx ∈ args, AtLevel tx env n) :
    AtLevel (.call xfn args ty) env n
end


theorem entity_access_at_level_succ {tx : TypedExpr} {env : Environment} {n n' : Nat}
  (h₁ : TypedExpr.EntityAccessAtLevel tx env n n' path) :
  TypedExpr.EntityAccessAtLevel tx env (n + 1) n' path
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

theorem entity_access_at_level_then_at_level {tx : TypedExpr} {n : Nat} {env : Environment} {path : List Attr}
  (h₁ : TypedExpr.EntityAccessAtLevel tx env n (n + 1) path) :
  TypedExpr.AtLevel tx env (n + 1)
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

theorem entity_access_level_spec {tx : TypedExpr} {env : Environment} {n nmax : Nat} {path : List Attr} :
  (TypedExpr.EntityAccessAtLevel tx env n nmax path) ↔ (checkEntityAccessLevel tx env n nmax path)
:= by
  cases tx
  case var =>
    simp only [checkEntityAccessLevel, iff_true]
    constructor
  case lit p _ =>
    cases p
    case entityUID =>
      simp only [checkEntityAccessLevel, beq_iff_eq]
      apply Iff.intro
      · intro hl ; cases hl
        rfl
      · intro hl
        subst hl
        constructor
    all_goals
      simp only [checkEntityAccessLevel, Bool.false_eq_true, iff_false]
      intro hc
      cases hc
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @entity_access_level_spec tx₂
    have ih₃ := @entity_access_level_spec tx₃
    simp only [checkEntityAccessLevel, Bool.and_eq_true]
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
      simp only [checkEntityAccessLevel, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]
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
    simp only [checkEntityAccessLevel]
    split
    · have ih₁ := @entity_access_level_spec tx₁
      simp only [←ih₁, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]
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
        · simpa using h₂
        · assumption
    · have ih₁ := @entity_access_level_spec tx₁
      rw [←ih₁]
      apply Iff.intro
      · intro hl
        cases hl
        · rename_i h₁ _ _ h₂ _
          simp only [h₂, CedarType.entity.injEq, imp_false, forall_eq'] at h₁
        · assumption
      · intro hl
        apply TypedExpr.EntityAccessAtLevel.getAttrRecord <;> assumption
  case record atxs _ =>
    cases path
    case nil =>
      simp only [checkEntityAccessLevel, Bool.false_eq_true, iff_false]
      intro hc
      cases hc
    case cons =>
      simp only [checkEntityAccessLevel]
      split <;> simp only [iff_false, Bool.and_eq_true, Bool.false_eq_true, List.all_eq_true, Subtype.forall, Prod.forall]
      · apply Iff.intro
        · intro hl
          cases hl
          rename_i tx h₁ tx' h₃ h₄ h₅
          replace h₄ : tx = tx' := by
            simpa [h₁] using h₄
          subst tx
          and_intros
          · have : sizeOf tx' < 1 + sizeOf atxs := by
              replace h₁ := List.sizeOf_lt_of_mem ∘ Map.make_mem_list_mem ∘ Map.find?_mem_toList $ h₁
              rw [Prod.mk.sizeOf_spec _ tx'] at h₁
              omega
            have ih := @entity_access_level_spec tx'
            exact ih.mp h₅
          · intros
            rename_i a tx _ h₂
            replace h₂ : (a, tx) ∈ atxs := by
              simpa [List.attach₂] using h₂
            have ih := @level_spec tx
            exact ih.mp (h₃ _ h₂)
        · intro ⟨ h₁, h₂ ⟩
          constructor
          · intro atx hatx
            have hSizeOf : sizeOf atx.snd < 1 + sizeOf atxs := by
              have h₄ := List.sizeOf_lt_of_mem hatx
              rw [Prod.mk.sizeOf_spec _ atx.snd] at h₄
              omega
            replace h₂ : checkLevel atx.snd env nmax = true := by
              specialize h₂ atx.fst atx.snd hSizeOf
              replace h₂ : atx ∈ atxs → checkLevel atx.snd env nmax = true := by
                simpa [List.attach₂] using h₂
              exact h₂ hatx
            have ih := @level_spec atx.snd
            exact ih.mpr h₂
          · assumption
          · rename_i a _ tx hf
            have : sizeOf tx < 1 + sizeOf atxs := by
              replace h₁ := List.sizeOf_lt_of_mem ∘ Map.make_mem_list_mem ∘ Map.find?_mem_toList $ hf
              rw [Prod.mk.sizeOf_spec _ tx] at h₁
              omega
            have ih := @entity_access_level_spec tx
            exact ih.mpr h₁
      · intro hc
        cases hc
        rename_i h₁ _  _ h₂ _
        simp [h₁] at h₂
  all_goals
    simp only [checkEntityAccessLevel, Bool.false_eq_true, iff_false]
    intro hc
    cases hc
termination_by tx

theorem level_spec {tx : TypedExpr} {env : Environment} {n : Nat}:
  (TypedExpr.AtLevel tx env n) ↔ (checkLevel tx env n = true)
:= by
  cases tx
  case lit =>
    simp only [checkLevel, iff_true]
    constructor
  case var =>
    simp only [checkLevel, iff_true]
    constructor
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @level_spec tx₂
    have ih₃ := @level_spec tx₃
    simp only [checkLevel, Bool.and_eq_true]
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
    simp only [checkLevel, Bool.and_eq_true]
    rw [←ih₁, ←ih₂]
    apply Iff.intro
    · intro h
      cases h
      constructor <;> assumption
    · intro ⟨ h₁, h₂ ⟩
      constructor <;> assumption

  case unaryApp op tx₁ _ =>
    have ih₁ := @level_spec tx₁
    simp only [checkLevel]
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
      simp only [checkLevel, gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq]
      rw [←ih₁, ←ih₂]
      apply Iff.intro
      · intro h
        cases h
        rename_i h₁ h₂ h₃
        and_intros <;> first
        | assumption
        | simp only [Nat.zero_lt_succ]
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
        | assumption
        | simp only [DereferencingBinaryOp, not_false_eq_true]

  case getAttr tx₁ a _  | hasAttr tx₁ a _  =>
    simp only [checkLevel, gt_iff_lt]
    split <;> (rename_i hety ; apply Iff.intro)
    · intro h
      cases h
      · simp only [Nat.zero_lt_succ, decide_true, Bool.true_and]
        have ih₁ := @entity_access_level_spec tx₁
        rw [←ih₁]
        assumption
      · rename_i hnety _
        simp [hety] at hnety
    · have ih₁ := @entity_access_level_spec tx₁
      simp only [Bool.and_eq_true, decide_eq_true_eq, and_imp]
      rw [←ih₁]
      intro h₁ h₂
      have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₁]
      subst n
      constructor <;> assumption
    · intro h
      cases h
      · rename_i hety' _
        simp [hety'] at hety
      · have ih₁ := @level_spec tx₁
        rw [←ih₁]
        assumption
    · intro h
      have ih₁ := @level_spec tx₁
      rw [←ih₁] at h
      constructor <;> assumption

  case call | set =>
    simp only [checkLevel, List.all_eq_true, List.mem_attach, forall_const, Subtype.forall]
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
    simp only [checkLevel, List.all_eq_true, Subtype.forall, Prod.forall]
    apply Iff.intro
    · intro h₁ a tx h₂ h₃
      replace h₃ : (a, tx) ∈ attrs :=
        by simpa [List.attach₂] using h₃
      cases h₁
      rename_i h₄
      specialize h₄ (a, tx) h₃
      have ih := @level_spec tx
      exact ih.mp h₄
    · intro h₁
      constructor
      intro atx h₂
      have hSizeOf : sizeOf atx.snd < 1 + sizeOf attrs := by
        have h₄ := List.sizeOf_lt_of_mem h₂
        rw [Prod.mk.sizeOf_spec atx.fst atx.snd] at h₄
        omega
      replace h₁ : checkLevel atx.snd env n := by
        specialize h₁ atx.fst atx.snd hSizeOf
        replace h₁ : atx ∈ attrs → checkLevel atx.snd env n= true := by
          simpa [List.attach₂] using h₁
        exact h₁ h₂
      have ih := @level_spec atx.snd
      exact ih.mpr h₁
termination_by tx

end
