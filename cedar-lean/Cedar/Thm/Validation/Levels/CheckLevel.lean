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
open Cedar.Spec

inductive EntityLit : TypedExpr → Prop where
  | entity_lit {euid : EntityUID} {ty : CedarType} :
    EntityLit (.lit (.entityUID euid) ty)
  | ite_true {x₁ x₂ x₃ : TypedExpr} {ty : CedarType}
    (hx₂ : EntityLit x₂) :
    EntityLit (.ite x₁ x₂ x₃ ty)
  | ite_false {x₁ x₂ x₃ : TypedExpr} {ty : CedarType}
    (hx₃ : EntityLit x₃) :
    EntityLit (.ite x₁ x₂ x₃ ty)
  | get_attr {x₁ : TypedExpr} {a : Attr} {ty : CedarType}
    (hx : EntityLit x₁) :
    EntityLit (.getAttr x₁ a ty)
  | get_tag {x₁ x₂ : TypedExpr} {ty : CedarType}
    (hx₁ : EntityLit x₁) :
    EntityLit (.binaryApp .getTag x₁ x₂ ty)
  | record {attrs : List (Attr × TypedExpr)} {ty : CedarType} {a : Attr} {tx : TypedExpr}
    (hx₁ : (a, tx) ∈ attrs)
    (hx₂ : EntityLit tx) :
    EntityLit (.record attrs ty)

theorem not_entity_lit_spec (tx : TypedExpr) :
  (notEntityLit tx = true) ↔ (¬ EntityLit tx)
:= by
  cases tx <;> try (
    simp only [notEntityLit, true_iff]
    intros h₁
    cases h₁
  )
  case lit p _ =>
    cases p <;> simp [notEntityLit]
    case entityUID => constructor
    all_goals {
      intro h₁
      cases h₁
    }
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := not_entity_lit_spec tx₁
    have ih₂ := not_entity_lit_spec tx₂
    have ih₃ := not_entity_lit_spec tx₃
    simp only [ih₁, ih₂, ih₃, notEntityLit, Bool.and_eq_true]
    constructor
    · intro ⟨hx₁, hx₂⟩ hite
      cases hite <;> contradiction
    · intro hite
      constructor <;> (
        intro h₁
        apply hite
      )
      case left => exact EntityLit.ite_true h₁
      case right => exact EntityLit.ite_false h₁
  case binaryApp op tx₁ tx₂ _ =>
    cases op <;> (
      simp [notEntityLit]
      try ( intro h₁ ; cases h₁ )
    )
    have ih₁ := not_entity_lit_spec tx₁
    have ih₂ := not_entity_lit_spec tx₂
    simp [ih₁, ih₂]
    constructor
    · intros h₁ h₂
      cases h₂
      contradiction
    · intros h₁ h₂
      apply h₁
      exact EntityLit.get_tag h₂

  case getAttr tx₁ _ _ =>
    simp only [notEntityLit]
    have ih₁ := not_entity_lit_spec tx₁
    simp only [ih₁]
    constructor
    · intros h₁ h₂
      cases h₂
      contradiction
    · intros h₁ h₂
      apply h₁
      exact EntityLit.get_attr h₂

  case record attrs ty =>
    simp [notEntityLit]
    constructor
    · intros h₁ h₂
      cases h₂
      rename_i a tx' hx₁ hx₂
      specialize h₁ a tx' hx₂
      have : sizeOf tx' < 1 + sizeOf attrs + sizeOf ty := by
        have h₁ := List.sizeOf_lt_of_mem hx₂
        rw [Prod.mk.sizeOf_spec] at h₁
        omega
      have ih := not_entity_lit_spec tx'
      simp only [ih] at h₁
      contradiction
    · intro h₁ _ tx' h₂
      have : sizeOf tx' < 1 + sizeOf attrs + sizeOf ty := by
        have h₁ := List.sizeOf_lt_of_mem h₂
        rw [Prod.mk.sizeOf_spec] at h₁
        omega
      have ih := not_entity_lit_spec tx'
      simp only [ih]
      intro h₃
      apply h₁
      exact EntityLit.record h₂ h₃

inductive Level : TypedExpr → Nat → Prop where
  | lit (p : Prim) (ty : CedarType) (n : Nat) :
    Level (.lit p ty) n
  | var (v : Var) (ty : CedarType) (n : Nat) :
    Level (.var v ty) n
  | ite (tx₁ tx₂ tx₃ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n)
    (hl₃ : Level tx₃ n) :
    Level (.ite tx₁ tx₂ tx₃ ty) n
  | and (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n) :
    Level (.and tx₁ tx₂ ty) n
  | or (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n) :
    Level (.or tx₁ tx₂ ty) n
  | unaryApp (op : UnaryOp) (tx₁ : TypedExpr) (ty : CedarType)
    (hl₁ : Level tx₁ n) :
    Level (.unaryApp op tx₁ ty) n
  | mem (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n.succ) :
    Level (.binaryApp .mem tx₁ tx₂ ty) n.succ
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n.succ) :
    Level (.binaryApp .getTag tx₁ tx₂ ty) n.succ
  | hasTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n.succ) :
    Level (.binaryApp .hasTag tx₁ tx₂ ty) n.succ
  | binaryApp (op : BinaryOp) (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hop :
      match op with
      | .mem | .hasTag | .getTag => False
      | _ => True)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n) :
    Level (.binaryApp op tx₁ tx₂ ty) n
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁)
    (hl₁ : Level tx₁ n) :
    Level (.getAttr tx₁ a ty) n.succ
  | hasAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁)
    (hl₁ : Level tx₁ n) :
    Level (.hasAttr tx₁ a ty) n.succ
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁)
    (hl₁ : Level tx₁ n)
    (hty :
      match tx₁.typeOf with
      | .record _ => True
      | _ => False) :
    Level (.getAttr tx₁ a ty) n.succ
  | hasAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁)
    (hl₁ : Level tx₁ n)
    (hty :
      match tx₁.typeOf with
      | .record _ => True
      | _ => False) :
    Level (.hasAttr tx₁ a ty) n.succ
  | set (txs : List TypedExpr) (ty : CedarType) (n : Nat)
    (hl : ∀ tx ∈ txs, Level tx n) :
    Level (.set txs ty) n
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType)
    (hl : ∀ atx ∈ attrs, Level atx.snd n) :
    Level (.record attrs ty) n
  | call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType)
    (hl : ∀ tx ∈ args, Level tx n) :
    Level (.call cfn args ty) n

theorem level_spec (tx : TypedExpr) (n : Nat):
  (Level tx n ) ↔ (checkLevel tx n = true)
:= by
  cases tx
  case lit =>
    simp [checkLevel]
    constructor
  case var =>
    simp [checkLevel]
    constructor
  case ite tx₁ tx₂ tx₃ _ =>
    have ih₁ := level_spec tx₁ n
    have ih₂ := level_spec tx₂ n
    have ih₃ := level_spec tx₃ n
    simp [checkLevel]
    rw [←ih₁, ←ih₂, ←ih₃]
    constructor
    · intros h
      cases h
      (constructor <;> try constructor) <;> assumption
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      constructor <;> assumption

  case or tx₁ tx₂ _ | and tx₁ tx₂ _ =>
    have ih₁ := level_spec tx₁ n
    have ih₂ := level_spec tx₂ n
    simp [checkLevel]
    rw [←ih₁, ←ih₂]
    constructor
    · intro h
      cases h
      constructor <;> assumption
    · intro ⟨ h₁, h₂ ⟩
      constructor <;> assumption

  case unaryApp op tx₁ _ =>
    have ih₁ := level_spec tx₁ n
    simp [checkLevel]
    rw [←ih₁]
    constructor
    · intro h
      cases h
      assumption
    · intro h₁
      constructor
      assumption

  case binaryApp op tx₁ tx₂ _ =>
    cases op
    case getTag | hasTag | mem =>
      have ih₁ := level_spec tx₁ (n - 1)
      have ih₂ := level_spec tx₂ n
      simp [checkLevel]
      rw [←ih₁, ←ih₂, not_entity_lit_spec]
      constructor
      · intro h
        cases h
        rename_i h₁ h₂ h₃
        (constructor <;> try constructor <;> try constructor) <;> (
          try simp
          try assumption
        )
        contradiction
      · intro ⟨ ⟨ ⟨ h₁, h₂⟩, h₃ ⟩ , h₄⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = n'.succ := by simp [h₂]
        subst n
        constructor <;> assumption
    all_goals
      have ih₁ := level_spec tx₁ n
      have ih₂ := level_spec tx₂ n
      simp [checkLevel]
      rw [←ih₁, ←ih₂]
      constructor
      · intro h
        cases h
        rename_i h₁ h₂
        simp [h₁, h₂]
      · intro ⟨ h₁, h₂ ⟩
        constructor <;> (
          try simp
          try assumption
        )

  case getAttr tx₁ a _  | hasAttr tx₁ a _  =>
    simp [checkLevel]
    split
    · constructor
      · intro h
        cases h <;> simp [*] at *
        rename_i n _ _
        have ih₁ := level_spec tx₁ n
        rw [←ih₁, not_entity_lit_spec]
        constructor <;> assumption
      · have ih₁ := level_spec tx₁ (n - 1)
        simp
        rw [←ih₁, not_entity_lit_spec]
        intro h₁ h₂ h₃
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = n'.succ := by simp [h₂]
        subst n
        constructor <;> assumption
    · sorry

  case set => sorry

  case record => sorry

  case call => sorry


theorem check_level_checked_succ {e : TypedExpr} {n : Nat}
  (h₁ : checkLevel e n)
  : checkLevel e (1 + n)
:= by
  cases e <;> try (simp [checkLevel] at h₁ ; simp [checkLevel])
  case ite | and | or | unaryApp =>
    simp [h₁, check_level_checked_succ]
  case binaryApp op e₀ _ _ =>
    cases op
    case mem | hasTag | getTag =>
      simp only [checkLevel, Bool.and_eq_true, decide_eq_true_eq] at h₁
      unfold checkLevel
      simp only [h₁, check_level_checked_succ, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, and_true]
      constructor
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_checked_succ]
    all_goals {
      simp only [checkLevel, Bool.and_eq_true] at h₁
      unfold checkLevel
      simp [h₁, check_level_checked_succ]
    }
  case hasAttr e _ _ | getAttr e _ _ =>
    split at h₁
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h₁ ⊢
      constructor <;> try constructor
      · simp [h₁]
      · omega
      · have h₂ : (1 + n - 1) = (1 + (n - 1)) := by omega
        simp [h₁, h₂, check_level_checked_succ]
    · simp [h₁, check_level_checked_succ]
  -- should be trivial
  case set | call => sorry
  case record => sorry
