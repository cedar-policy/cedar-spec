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

inductive EntityLit : TypedExpr → List Attr → Prop where
  | entity_lit {euid : EntityUID} {ty : CedarType} {path : List Attr}:
    EntityLit (.lit (.entityUID euid) ty) path
  | ite_true {x₁ x₂ x₃ : TypedExpr} {path : List Attr} {ty : CedarType}
    (hx₂ : EntityLit x₂ path) :
    EntityLit (.ite x₁ x₂ x₃ ty) path
  | ite_false {x₁ x₂ x₃ : TypedExpr} {path : List Attr} {ty : CedarType}
    (hx₃ : EntityLit x₃ path) :
    EntityLit (.ite x₁ x₂ x₃ ty) path
  | get_attr {x₁ : TypedExpr} {a : Attr} {path : List Attr} {ty : CedarType}
    (hx : EntityLit x₁ (a :: path)) :
    EntityLit (.getAttr x₁ a ty) path
  | get_tag {x₁ x₂ : TypedExpr} {path : List Attr} {ty : CedarType}
    (hx₁ : EntityLit x₁ path) :
    EntityLit (.binaryApp .getTag x₁ x₂ ty) path
  | record {attrs : List (Attr × TypedExpr)} {ty : CedarType} {a : Attr} {path : List Attr} {tx : TypedExpr}
    (hx₁ : (Map.make attrs).find? a = some tx)
    (hx₂ : EntityLit tx path) :
    EntityLit (.record attrs ty) (a :: path)


theorem not_entity_lit_spec (tx : TypedExpr) :
  (notEntityLit tx = true) ↔ (¬ EntityLit tx [])
:= not_entity_lit_spec' tx []
where
  not_entity_lit_spec' (tx : TypedExpr) (path : List Attr) :
    (notEntityLit.notEntityLit' tx path = true) ↔ (¬ EntityLit tx path)
  := by
    cases tx <;> try (
      simp [notEntityLit.notEntityLit']
      intros h₁
      cases h₁
    )
    case lit p _ =>
      cases p <;> simp [notEntityLit.notEntityLit']
      case entityUID => constructor
      all_goals {
        intro h₁
        cases h₁
      }
    case ite tx₁ tx₂ tx₃ _ =>
      have ih₁ := not_entity_lit_spec' tx₁
      have ih₂ := not_entity_lit_spec' tx₂
      have ih₃ := not_entity_lit_spec' tx₃
      simp only [ih₁, ih₂, ih₃, notEntityLit.notEntityLit', Bool.and_eq_true]
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
        simp [notEntityLit.notEntityLit']
        try ( intro h₁ ; cases h₁ )
      )
      have ih₁ := not_entity_lit_spec' tx₁
      have ih₂ := not_entity_lit_spec' tx₂
      simp [ih₁, ih₂]
      constructor
      · intros h₁ h₂
        cases h₂
        contradiction
      · intros h₁ h₂
        apply h₁
        exact EntityLit.get_tag h₂

    case getAttr tx₁ _ _ =>
      simp only [notEntityLit.notEntityLit']
      have ih₁ := not_entity_lit_spec' tx₁
      simp only [ih₁]
      constructor
      · intros h₁ h₂
        cases h₂
        contradiction
      · intros h₁ h₂
        apply h₁
        exact EntityLit.get_attr h₂

    case record attrs ty =>
      cases path <;> simp [notEntityLit.notEntityLit']
      case nil =>
        intro hel
        cases hel
      case cons a path =>
        constructor
        · intros h₁ h₂
          cases h₂
          rename_i tx hi hl
          split at h₁ <;> (
            rename_i hf
            simp only [hf, Option.some.injEq, reduceCtorEq] at hi
          )
          subst hi
          rename_i tx'
          have : sizeOf tx' < 1 + sizeOf attrs := by
            replace hf := Map.make_mem_list_mem (Map.find?_mem_toList hf)
            replace hf := List.sizeOf_lt_of_mem hf
            rw [Prod.mk.sizeOf_spec a tx'] at hf
            omega
          have ih := not_entity_lit_spec' tx'
          rw [ih] at h₁
          contradiction
        · intro h₁
          split <;> try rfl
          rename_i tx' hf
          have : sizeOf tx' < 1 + sizeOf attrs := by
            replace hf := Map.make_mem_list_mem (Map.find?_mem_toList hf)
            replace hf := List.sizeOf_lt_of_mem hf
            rw [Prod.mk.sizeOf_spec a tx'] at hf
            omega
          have ih := not_entity_lit_spec' tx'
          rw [ih]
          intros h₃
          apply h₁
          constructor <;> assumption

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
    (he : ¬ EntityLit tx₁ [])
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ (n + 1)) :
    Level (.binaryApp .mem tx₁ tx₂ ty) (n + 1)
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁ [])
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ (n + 1)) :
    Level (.binaryApp .getTag tx₁ tx₂ ty) (n + 1)
  | hasTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁ [])
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ (n + 1)) :
    Level (.binaryApp .hasTag tx₁ tx₂ ty) (n + 1)
  | binaryApp (op : BinaryOp) (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hop :
      match op with
      | .mem | .hasTag | .getTag => False
      | _ => True)
    (hl₁ : Level tx₁ n)
    (hl₂ : Level tx₂ n) :
    Level (.binaryApp op tx₁ tx₂ ty) n
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁ [])
    (hl₁ : Level tx₁ n) :
    Level (.getAttr tx₁ a ty) (n + 1)
  | hasAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁ [])
    (hl₁ : Level tx₁ n) :
    Level (.hasAttr tx₁ a ty) (n + 1)
  | getAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁ [])
    (hl₁ : Level tx₁ n)
    (hty :
      match tx₁.typeOf with
      | .record _ => True
      | _ => False) :
    Level (.getAttr tx₁ a ty) (n + 1)
  | hasAttrRecord (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLit tx₁ [])
    (hl₁ : Level tx₁ n)
    (hty :
      match tx₁.typeOf with
      | .record _ => True
      | _ => False) :
    Level (.hasAttr tx₁ a ty) (n + 1)
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
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₂]
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
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₂]
        subst n
        constructor <;> assumption
    · sorry

  case set => sorry

  case record => sorry

  case call => sorry

theorem check_level_checked_succ' {e : TypedExpr} {n : Nat}
  (h₁ : Level e n)
  : Level e (n + 1)
:= by
  cases h₁
  all_goals
    constructor <;> (
      try apply check_level_checked_succ'
      try assumption
    )
  case call htx | set htx =>
    intro tx hi
    have _ := List.sizeOf_lt_of_mem hi
    apply check_level_checked_succ'
    exact htx tx hi
  case record attrs _ ha =>
    intro atx hi
    have : sizeOf atx.snd < sizeOf attrs := by
      have h₂ := List.sizeOf_lt_of_mem hi
      rw [Prod.mk.sizeOf_spec] at h₂
      omega
    apply check_level_checked_succ'
    exact ha atx hi
termination_by e

theorem check_level_checked_succ {e : TypedExpr} {n : Nat}
  (h₁ : checkLevel e n)
  : checkLevel e (n + 1)
:= by
  rw [←level_spec] at h₁ ⊢
  exact check_level_checked_succ' h₁
