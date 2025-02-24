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

inductive TypedExpr.EntityLitViaPath : TypedExpr → List Attr → Prop where
  | entity_lit {euid : EntityUID} {ty : CedarType} {path : List Attr}:
    EntityLitViaPath (.lit (.entityUID euid) ty) path
  | ite_true {x₁ x₂ x₃ : TypedExpr} {path : List Attr} {ty : CedarType}
    (hx₂ : EntityLitViaPath x₂ path) :
    EntityLitViaPath (.ite x₁ x₂ x₃ ty) path
  | ite_false {x₁ x₂ x₃ : TypedExpr} {path : List Attr} {ty : CedarType}
    (hx₃ : EntityLitViaPath x₃ path) :
    EntityLitViaPath (.ite x₁ x₂ x₃ ty) path
  | get_attr {x₁ : TypedExpr} {a : Attr} {path : List Attr} {ty : CedarType}
    (hx : EntityLitViaPath x₁ (a :: path)) :
    EntityLitViaPath (.getAttr x₁ a ty) path
  | get_tag {x₁ x₂ : TypedExpr} {path : List Attr} {ty : CedarType}
    (hx₁ : EntityLitViaPath x₁ path) :
    EntityLitViaPath (.binaryApp .getTag x₁ x₂ ty) path
  | record {attrs : List (Attr × TypedExpr)} {ty : CedarType} {a : Attr} {path : List Attr} {tx : TypedExpr}
    (hx₁ : (Map.make attrs).find? a = some tx)
    (hx₂ : EntityLitViaPath tx path) :
    EntityLitViaPath (.record attrs ty) (a :: path)

theorem not_entity_lit_spec (tx : TypedExpr) :
  (notEntityLit tx = true) ↔ (¬ TypedExpr.EntityLitViaPath tx [])
:= not_entity_lit_spec' tx []
where
  not_entity_lit_spec' (tx : TypedExpr) (path : List Attr) :
    (notEntityLit.notEntityLit' tx path = true) ↔ (¬ TypedExpr.EntityLitViaPath tx path)
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
        case left => exact .ite_true h₁
        case right => exact .ite_false h₁
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
        exact .get_tag h₂

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
        exact .get_attr h₂

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

def DereferencingBinaryOp : BinaryOp → Prop
  | .mem | .hasTag | .getTag => True
  | _ => False

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
  | unaryApp (op : UnaryOp) (tx₁ : TypedExpr) (ty : CedarType)
    (hl₁ : AtLevel tx₁ n) :
    AtLevel (.unaryApp op tx₁ ty) n
  | mem (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLitViaPath tx₁ [])
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ (n + 1)) :
    AtLevel (.binaryApp .mem tx₁ tx₂ ty) (n + 1)
  | getTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLitViaPath tx₁ [])
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ (n + 1)) :
    AtLevel (.binaryApp .getTag tx₁ tx₂ ty) (n + 1)
  | hasTag (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (he : ¬ EntityLitViaPath tx₁ [])
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ (n + 1)) :
    AtLevel (.binaryApp .hasTag tx₁ tx₂ ty) (n + 1)
  | binaryApp (op : BinaryOp) (tx₁ tx₂ : TypedExpr) (ty : CedarType) (n : Nat)
    (hop : ¬ DereferencingBinaryOp op)
    (hl₁ : AtLevel tx₁ n)
    (hl₂ : AtLevel tx₂ n) :
    AtLevel (.binaryApp op tx₁ tx₂ ty) n
  | getAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (n : Nat)
    (he : ¬ EntityLitViaPath tx₁ [])
    (hl₁ : AtLevel tx₁ n)
    (hty : tx₁.typeOf = .entity ety) :
    AtLevel (.getAttr tx₁ a ty) (n + 1)
  | hasAttr (tx₁ : TypedExpr) (a : Attr) (ty : CedarType) {ety : EntityType} (n : Nat)
    (he : ¬ EntityLitViaPath tx₁ [])
    (hl₁ : AtLevel tx₁ n)
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
  | record (attrs : List (Attr × TypedExpr)) (ty : CedarType)
    (hl : ∀ atx ∈ attrs, AtLevel atx.snd n) :
    AtLevel (.record attrs ty) n
  | call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType)
    (hl : ∀ tx ∈ args, AtLevel tx n) :
    AtLevel (.call xfn args ty) n

theorem level_spec {tx : TypedExpr} {n : Nat}:
  (TypedExpr.AtLevel tx n ) ↔ (checkLevel tx n = true)
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
    constructor
    · intros h
      cases h
      (constructor <;> try constructor) <;> assumption
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      constructor <;> assumption

  case or tx₁ tx₂ _ | and tx₁ tx₂ _ =>
    have ih₁ := @level_spec tx₁
    have ih₂ := @level_spec tx₂
    simp [checkLevel]
    rw [←ih₁, ←ih₂]
    constructor
    · intro h
      cases h
      constructor <;> assumption
    · intro ⟨ h₁, h₂ ⟩
      constructor <;> assumption

  case unaryApp op tx₁ _ =>
    have ih₁ := @level_spec tx₁
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
      have ih₁ := @level_spec tx₁
      have ih₂ := @level_spec tx₂
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
        rename_i hop _ _
        simp [DereferencingBinaryOp] at hop
      · intro ⟨ ⟨ ⟨ h₁, h₂⟩, h₃ ⟩ , h₄⟩
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₂]
        subst n
        constructor <;> assumption
    all_goals
      have ih₁ := @level_spec tx₁
      have ih₂ := @level_spec tx₂
      simp [checkLevel]
      rw [←ih₁, ←ih₂]
      constructor
      · intro h
        cases h
        rename_i h₁ h₂
        simp [h₁, h₂]
      · intro ⟨ h₁, h₂ ⟩
        constructor <;> (
          try simp [DereferencingBinaryOp]
          try assumption
        )

  case getAttr tx₁ a _  | hasAttr tx₁ a _  =>
    simp [checkLevel]
    split
    · constructor
      · intro h
        cases h <;> simp [*] at *
        rename_i n _ _ _ _
        have ih₁ := @level_spec tx₁
        rw [←ih₁, not_entity_lit_spec]
        constructor <;> assumption
      · have ih₁ := @level_spec tx₁
        simp
        rw [←ih₁, not_entity_lit_spec]
        intro h₁ h₂ h₃
        have ⟨ n', hn ⟩  : ∃ n' : Nat , n = (n' + 1) := by simp [h₂]
        subst n
        constructor <;> assumption
    · constructor
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
    constructor
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
    constructor
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

theorem check_level_succ {tx : TypedExpr} {n : Nat}
  (h₁ : TypedExpr.AtLevel tx n) :
  TypedExpr.AtLevel tx (n + 1)
:= by
  cases h₁
  case call htx | set htx =>
    constructor
    intro tx hi
    have _ := List.sizeOf_lt_of_mem hi
    apply check_level_succ
    exact htx tx hi
  case record attrs _ ha =>
    constructor
    intro atx hi
    have : sizeOf atx.snd < sizeOf attrs := by
      have h₂ := List.sizeOf_lt_of_mem hi
      rw [Prod.mk.sizeOf_spec] at h₂
      omega
    apply check_level_succ
    exact ha atx hi
  case getAttrRecord h₁ h₂ =>
    have h₃ := check_level_succ h₂
    apply TypedExpr.AtLevel.getAttrRecord <;> assumption
  case hasAttrRecord h₁ h₂ =>
    have h₃ := check_level_succ h₂
    apply TypedExpr.AtLevel.hasAttrRecord <;> assumption
  all_goals
    constructor <;> (
      try apply check_level_succ
      try assumption
    )
