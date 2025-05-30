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

import Cedar.Spec
import Cedar.SymCC
import Cedar.Thm.Data
import Cedar.Thm.Data.LT
import Cedar.Thm.Data.Control

/-!
# Strict ordering of Cedar terms

This file contains proofs that the less-than (`<`) relation on Cedar terms is
strict.
-/

-- set_option profiler true
set_option linter.all false

namespace Cedar.Thm

open Cedar Data Spec SymCC Validation

----- General helper lemmas -----

theorem sizeOf_list_lt_sizeOf_map [SizeOf α] [SizeOf β] {m : Map α β} :
  sizeOf m.1 < 1 + sizeOf m
:= by
  simp only [sizeOf, Map._sizeOf_1]
  generalize h : List._sizeOf_1 m.1 = i
  omega

theorem lt_irrefl_implies_not_eq {α} [LT α] {a b : α} :
  (∀ (a : α), ¬ a < a) → a < b → ¬ a = b
:= by
  intro h₀ h₁
  by_contra h₂
  subst h₂
  have h₃ := h₀ a
  contradiction

theorem lt_trans_irrefl_implies_asymm {α} [LT α] {a b : α} :
  (∀ (a b c : α), a < b → b < c → a < c) →
  (∀ (a : α), ¬ a < a) → a < b → ¬ b < a
:= by
  intro h₁ h₂ h₃
  by_contra h₄
  specialize h₁ a b a h₃ h₄
  specialize h₂ a
  contradiction

local macro "simp_decide_lt" h:ident lt_fun:ident name_fun:ident : tactic => do
 `(tactic| (
    revert $h
    simp only [$lt_fun:ident, $name_fun:ident, decide_eq_true_eq]
    decide
    ))

----- `<` is strict on `ExtOp` -----

theorem ExtOp.lt_irrefl (a : ExtOp) :
  ¬ a < a
:= by
  simp only [LT.lt]
  simp only [ExtOp.lt, decide_eq_true_eq]
  exact StrictLT.irreflexive a.mkName

theorem ExtOp.lt_trans (a b c : ExtOp) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt, ExtOp.lt, decide_eq_true_eq]
  intro h₁ h₂
  exact List.slt_trans h₁ h₂

theorem ExtOp.lt_conn {a b : ExtOp} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [LT.lt]
  simp only [ExtOp.lt, decide_eq_true_eq]
  intro h₁
  cases a <;> cases b
  any_goals (simp only [ne_eq, not_true_eq_false, not_false_eq_true] at h₁ )
  all_goals (simp only [ExtOp.mkName] ; decide)

instance ExtOp.strictLT : StrictLT ExtOp where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm ExtOp.lt_trans ExtOp.lt_irrefl
  transitive a b c := by exact ExtOp.lt_trans a b c
  connected  a b   := by exact ExtOp.lt_conn

----- `<` is strict on `TermPrimType` -----

theorem TermPrimType.lt_irrefl (ty : TermPrimType) :
  ¬ TermPrimType.lt ty ty
:= by
  cases ty <;>
  simp only [TermPrimType.lt, TermPrimType.mkName, decide_eq_true_eq, String.lt_irrefl, Nat.lt_irrefl, decide_false, Bool.false_eq_true, not_false_eq_true]
  case entity ety => exact StrictLT.irreflexive ety
  case ext xty => simp only [LT.lt, ExtType.lt, Bool.false_eq_true, not_false_eq_true]

theorem TermPrimType.lt_trans (a b c : TermPrimType) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt]
  intros h₁ h₂
  by_contra h₃
  cases a <;> cases b <;> cases c
  any_goals (simp_decide_lt h₁ TermPrimType.lt TermPrimType.mkName)
  any_goals (simp_decide_lt h₂ TermPrimType.lt TermPrimType.mkName)
  any_goals (simp_decide_lt h₃ TermPrimType.lt TermPrimType.mkName)
  case bitvec | entity =>
    simp only [TermPrimType.lt, decide_eq_true_eq] at *
    have h₄ := StrictLT.transitive _ _ _ h₁ h₂
    contradiction
  case ext xty₁ xty₂ xty₃ =>
    simp only [TermPrimType.lt, LT.lt, ExtType.lt, Bool.not_eq_true] at *
    cases xty₁ <;> cases xty₂ <;> cases xty₃ <;>
    simp only [Decide.decide_eq_true_eq] at * <;>
    trivial

theorem TermPrimType.lt_conn {a b : TermPrimType} :
  a ≠ b → (a < b ∨ b < a)
:= by
  intro h
  cases a <;> cases b <;>
  simp only [LT.lt] <;>
  simp only [TermPrimType.lt, TermPrimType.mkName, decide_eq_true_eq]
  any_goals (decide)
  case bool | string =>
    simp only [ne_eq, not_true_eq_false] at h
  case bitvec =>
    simp only [ne_eq, TermPrimType.bitvec.injEq] at h
    omega
  case entity =>
    simp only [ne_eq, TermPrimType.entity.injEq] at h
    apply Name.strictLT.connected _ _ h
  case ext =>
    rename_i xty₁ xty₂
    simp only [ne_eq, TermPrimType.ext.injEq] at h
    cases xty₁ <;> cases xty₂ <;>
    simp only [LT.lt, ExtType.lt, reduceCtorEq, not_false_eq_true, not_true_eq_false, Bool.false_eq_true, or_true, or_false] at *

instance TermPrimType.strictLT : StrictLT TermPrimType where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm TermPrimType.lt_trans TermPrimType.lt_irrefl
  transitive a b c := by exact TermPrimType.lt_trans a b c
  connected  a b   := by exact TermPrimType.lt_conn

----- `<` is strict on `TermType` -----

mutual
theorem TermType.lt_irrefl (ty : TermType) :
  ¬ TermType.lt ty ty
:= by
  cases ty <;>
  simp only [TermType.lt, decide_eq_true_eq, Nat.lt_irrefl, decide_false, not_false_eq_true, Bool.not_eq_true]
  case prim =>
    apply StrictLT.irreflexive
  case option ty | set ty =>
    simp only [TermType.lt_irrefl ty]
  case record rty =>
    unfold TermType.lt
    cases rty ; rename_i rty
    simp only [TermType.ltListProd_irrefl rty]

theorem TermType.ltListProd_irrefl (rty : List (Attr × TermType)) :
  ¬ TermType.ltListProd rty rty
:= by
  cases rty
  simp only [TermType.ltListProd, Bool.false_eq_true, not_false_eq_true]
  rename_i hd tl
  cases hd
  rename_i a v
  simp only [TermType.ltListProd, decide_true, Bool.true_and, Bool.and_self, Bool.or_eq_true,
    decide_eq_true_eq, not_or, Bool.not_eq_true]
  by_contra h₁
  simp only [not_and, Bool.not_eq_false, and_imp] at h₁
  have h₂ := TermType.lt_irrefl v
  simp only [Bool.not_eq_true] at h₂
  specialize h₁ (StrictLT.irreflexive a) h₂
  have _ := TermType.ltListProd_irrefl tl
  contradiction
end

mutual
theorem TermType.lt_trans (a b c : TermType) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt]
  intro h₁ h₂
  by_contra h₃
  cases a <;> cases b <;> cases c
  any_goals (simp_decide_lt h₁ TermType.lt TermType.mkName)
  any_goals (simp_decide_lt h₂ TermType.lt TermType.mkName)
  any_goals (simp_decide_lt h₃ TermType.lt TermType.mkName)
  case prim =>
    simp only [TermType.lt, decide_eq_true_eq] at *
    have _ := TermPrimType.lt_trans _ _ _ h₁ h₂
    contradiction
  case option | set =>
    simp only [TermType.lt, decide_eq_true_eq] at *
    have _ := TermType.lt_trans _ _ _ h₁ h₂
    contradiction
  case record =>
    rename_i rty
    unfold TermType.lt at *
    have _ : sizeOf rty.1 < 1 + sizeOf rty := by -- termination
      exact sizeOf_list_lt_sizeOf_map
    have _ := TermType.ltListProd_trans h₁ h₂
    contradiction

theorem TermType.ltListProd_trans {ts₁ ts₂ ts₃: List (Attr × TermType)}
  (h₁ : TermType.ltListProd ts₁ ts₂)
  (h₂ : TermType.ltListProd ts₂ ts₃) :
  TermType.ltListProd ts₁ ts₃
:= by
  cases ts₁ <;> cases ts₂ <;> cases ts₃ <;>
  try { simp only [TermType.ltListProd, Bool.false_eq_true] at * }
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  cases hd₁ ; cases hd₂ ; cases hd₃ ;
  simp only [TermType.ltListProd, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
  rename_i a₁ ty₁ a₂ ty₂ a₃ ty₃
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
      have h₃ := TermType.lt_trans _ _ _ h₃ h₄
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
    have h₅ := TermType.ltListProd_trans h₃ h₄
    simp [h₅]
end


mutual
theorem TermType.lt_conn {a b : TermType} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [LT.lt]
  cases a <;> cases b
  any_goals (
    simp only [TermType.lt, TermType.mkName,
      TermType.prim.injEq, TermType.set.injEq,
      TermType.option.injEq, TermType.record.injEq,
      ne_eq, reduceCtorEq, not_false_eq_true,
      String.reduceLT, decide_true, decide_false,
      decide_eq_true_eq, Bool.false_eq_true,
      or_false, or_true, imp_self])
  case prim =>
    exact TermPrimType.lt_conn
  case option | set =>
    exact TermType.lt_conn
  case record rty₁ rty₂ =>
    cases rty₁ ; cases rty₂
    simp only [Map.mk.injEq, TermType.lt]
    exact TermType.ltListProd_conn

theorem TermType.ltListProd_conn {ts₁ ts₂ : List (Attr × TermType)}
  (h₁ : ¬ts₁ = ts₂) :
  TermType.ltListProd ts₁ ts₂ ∨ TermType.ltListProd ts₂ ts₁
:= by
  cases ts₁ <;> cases ts₂ <;>
  try { simp only [TermType.ltListProd, Bool.false_eq_true, or_self, or_true, or_false] } <;>
  try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂
  simp only [TermType.ltListProd, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  rename_i a₁ t₁ a₂ t₂
  simp only [List.cons.injEq, Prod.mk.injEq, not_and, and_imp] at h₁
  by_cases h₂ : (a₁ = a₂)
  case pos =>
    subst h₂ ; simp only [forall_const, true_and] at *
    by_cases h₃ : (t₁ = t₂)
    case pos =>
      subst h₃ ; simp only [forall_const, true_and] at *
      have h₂ := TermType.ltListProd_conn h₁
      rcases h₂ with h₂ | h₂ <;> simp [h₂]
    case neg =>
      have h₄ := TermType.lt_conn h₃
      simp [LT.lt] at h₄
      rcases h₄ with h₄ | h₄ <;> simp [h₄]
  case neg =>
    have h₃ := String.strictLT.connected a₁ a₂
    simp [h₂] at h₃
    rcases h₃ with h₃ | h₃ <;> simp [h₃]

end

instance TermType.strictLT : StrictLT TermType where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm TermType.lt_trans TermType.lt_irrefl
  transitive a b c := by exact TermType.lt_trans a b c
  connected  a b   := by exact TermType.lt_conn

----- `<` is strict on `UUF` -----

theorem UUF.lt_irrefl (f : UUF) :
  ¬ UUF.lt f f
:= by
  simp only [UUF.lt, decide_true, Bool.true_and, Bool.and_self, Bool.or_eq_true, decide_eq_true_eq]
  by_contra h₁
  simp only [StrictLT.irreflexive f.id, StrictLT.irreflexive f.arg, or_self,
    StrictLT.irreflexive f.out] at h₁

theorem UUF.lt_trans (a b c : UUF) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt, UUF.lt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  intro h₁ h₂
  rcases h₁ with h₁ | ⟨⟨h₁, h₃⟩, h₄⟩
  case inl =>
    rcases h₂ with h₂ | ⟨⟨h₂, h₃⟩, _⟩
    case inl =>
      rcases h₁ with h₁ | ⟨h₁, h₃⟩ <;>
      rcases h₂ with h₂ | ⟨h₂, h₄⟩
      · have h₃ := List.slt_trans h₁ h₂
        simp only [LT.lt] at h₃
        simp only [h₃, true_or]
      · simp only [h₂] at *
        simp only [h₁, true_or]
      · simp only [h₁] at *
        simp only [h₂, true_or]
      · simp only [← h₁, ← h₂, true_and] at *
        have h₅ := TermType.lt_trans _ _ _ h₃ h₄
        simp only [LT.lt] at h₅
        exact Or.inl (Or.inr h₅)
    case inr =>
      simp only [← h₂, ← h₃] at *
      exact Or.inl h₁
  case inr =>
    simp only [← h₁, ← h₃] at *
    rcases h₂ with h₂ | ⟨⟨h₁, h₂⟩, h₃⟩
    case inl =>
      exact Or.inl h₂
    case inr =>
      have h₅ := TermType.lt_trans _ _ _ h₄ h₃
      simp only [LT.lt] at h₅
      exact Or.inr (And.intro (And.intro h₁ h₂) h₅)

theorem UUF.lt_conn {a b : UUF} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [ne_eq, LT.lt]
  intro h₁
  simp only [UUF.lt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  by_cases h₂ : a.id = b.id
  case pos =>
    by_cases h₃ : a.arg = b.arg
    case pos =>
      by_cases h₄ : a.out = b.out
      case pos =>
        have h₅ : UUF.mk a.id a.arg a.out = UUF.mk b.id b.arg b.out := by
          simp only [h₂, h₃, h₄]
        have ha : a = UUF.mk a.id a.arg a.out := by simp only
        have hb : b = UUF.mk b.id b.arg b.out := by simp only
        rw [← ha, ← hb] at h₅
        contradiction
      case neg =>
        replace h₄ := TermType.lt_conn h₄
        rcases h₄ with h₄ | h₄ <;>
        simp only [h₂, h₃, true_and, and_self, h₄, or_true, true_or]
    case neg =>
      replace h₃ := TermType.lt_conn h₃
      rcases h₃ with h₃ | h₃ <;>
      simp only [h₂, h₃, and_self, or_true, true_and, true_or]
  case neg =>
    replace h₂ := String.strictLT.connected a.id b.id h₂
    rcases h₂ with h₂ | h₂ <;>
    simp only [h₂, true_or, or_true]

instance UUF.strictLT : StrictLT UUF where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm UUF.lt_trans UUF.lt_irrefl
  transitive a b c := by exact UUF.lt_trans a b c
  connected  a b   := by exact UUF.lt_conn

----- `<` is strict on `PatElem` -----

theorem PatElem.lt_irrefl (a : PatElem) :
  ¬ PatElem.lt a a
:= by
  simp only [PatElem.lt, Bool.not_eq_true]
  cases a <;>
  simp only [decide_eq_false_iff_not]
  rename_i c
  exact StrictLT.irreflexive c

theorem PatElem.lt_trans (a b c : PatElem) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt, PatElem.lt]
  cases a <;> cases b <;> cases c <;>
  simp only [Bool.false_eq_true, decide_eq_true_eq, implies_true, imp_self, false_implies, forall_const, implies_true]
  apply Char.strictLT.transitive

theorem PatElem.lt_conn {a b : PatElem} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [ne_eq, LT.lt, PatElem.lt]
  intro h
  cases a <;> cases b
  · simp only [not_true_eq_false] at h
  · simp only [Bool.false_eq_true, or_false]
  · simp only [or_true]
  · simp only [PatElem.justChar.injEq] at h
    simp only [decide_eq_true_eq]
    exact Char.strictLT.connected _ _ h

instance PatElem.strictLT : StrictLT PatElem where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm PatElem.lt_trans PatElem.lt_irrefl
  transitive a b c := by exact PatElem.lt_trans a b c
  connected  a b   := by exact PatElem.lt_conn

----- `<` is strict on `Op` -----

theorem Op.lt_irrefl (a : Op) :
  ¬ Op.lt a a
:= by
  simp only [Op.lt, Bool.not_eq_true]
  split <;> simp only [decide_eq_false_iff_not]
  case h_1 f => exact UUF.lt_irrefl f
  case h_2 => simp only [Nat.lt_irrefl, not_false_eq_true]
  case h_3 | h_4 | h_6 => apply List.slt_irrefl
  case h_5 xty => exact StrictLT.irreflexive xty

local macro "simp_lt_trans" lt:ident mkName:ident c:ident trans:term : tactic => do
 `(tactic| (
    intro h₁ h₂
    cases $c:ident <;>
    unfold $lt:ident at * <;>
    simp only [$mkName:ident, decide_eq_true_eq] at *
    any_goals (exact h₂)
    exact $trans _ _ _ h₁ h₂
    ))

private theorem Op.lt_trans_uuf {f₁ f₂ : UUF} {c : Op} :
   f₁ < f₂ → Op.lt (Op.uuf f₂) c = true → Op.lt (Op.uuf f₁) c = true
:= by simp_lt_trans Op.lt Op.mkName c UUF.lt_trans

private theorem Op.lt_trans_zero_extend {n₁ n₂ : Nat} {c : Op} :
   n₁ < n₂ → Op.lt (Op.zero_extend n₂) c = true → Op.lt (Op.zero_extend n₁) c = true
:= by simp_lt_trans Op.lt Op.mkName c Nat.strictLT.transitive

private theorem Op.lt_trans_record_get {a₁ a₂ : Attr} {c : Op} :
   a₁ < a₂ → Op.lt (Op.record.get a₂) c = true → Op.lt (Op.record.get a₁) c = true
:= by simp_lt_trans Op.lt Op.mkName c String.strictLT.transitive

private theorem Op.lt_trans_string_like {p₁ p₂ : Pattern} {c : Op} :
   p₁ < p₂ → Op.lt (Op.string.like p₂) c = true → Op.lt (Op.string.like p₁) c = true
:= by simp_lt_trans Op.lt Op.mkName c (List.strictLT PatElem).transitive

private theorem Op.lt_trans_ext {xop₁ xop₂ : ExtOp} {c : Op} :
   xop₁ < xop₂ → Op.lt (Op.ext xop₂) c = true → Op.lt (Op.ext xop₁) c = true
:= by simp_lt_trans Op.lt Op.mkName c @ExtOp.lt_trans

local macro "simp_op_lt_trans_parametric'" a:ident inj:ident : tactic => do
 `(tactic| (
    intro h₁ h₂
    cases $a:ident
    any_goals (
      simp only [Op.mkName, $inj:ident, false_implies, forall_const,
        imp_self, implies_true, Op.lt, decide_eq_true_eq] at *
      exact h₁
    )
    simp only [$inj:ident, forall_apply_eq_imp_iff, forall_eq'] at h₂
  ))

private theorem Op.lt_trans_uuf' {fb fc: UUF} {a : Op} :
  (Op.mkName a < Op.mkName (Op.uuf fb)) →
  (∀ (f₁ : UUF), a = Op.uuf f₁ → False) →
  Op.lt a (Op.uuf fc) = true
:= by simp_op_lt_trans_parametric' a Op.uuf.injEq

private theorem Op.lt_trans_zero_extend' {nb nc: Nat} {a : Op} :
  (Op.mkName a < Op.mkName (Op.zero_extend nb)) →
  (∀ (na : Nat), a = Op.zero_extend na → False) →
  Op.lt a (Op.zero_extend nc) = true
:= by simp_op_lt_trans_parametric' a Op.zero_extend.injEq

private theorem Op.lt_trans_record_get' {ab ac: Attr} {a : Op} :
  (Op.mkName a < Op.mkName (Op.record.get ab)) →
  (∀ (a' : Attr), a = Op.record.get a' → False) →
  Op.lt a (Op.record.get ac) = true
:= by simp_op_lt_trans_parametric' a Op.record.get.injEq

private theorem Op.lt_trans_string_like' {pb pc: Pattern} {a : Op} :
  (Op.mkName a < Op.mkName (Op.string.like pb)) →
  (∀ (pa : Pattern), a = Op.string.like pa → False) →
  Op.lt a (Op.string.like pc) = true
:= by simp_op_lt_trans_parametric' a Op.string.like.injEq

private theorem Op.lt_trans_ext' {xb xc: ExtOp} {a : Op} :
  (Op.mkName a < Op.mkName (Op.ext xb)) →
  (∀ (xa : ExtOp), a = Op.ext xa → False) →
  Op.lt a (Op.ext xc) = true
:= by simp_op_lt_trans_parametric' a Op.ext.injEq

private theorem Op.lt_mkName_implies_lt {a b : Op} :
  Op.mkName a < Op.mkName b → Op.lt a b
:= by
  intro h
  simp only [Op.lt]
  split
  case h_6 => simp only [decide_eq_true_eq] ; exact h
  all_goals { simp only [Op.mkName] at h ; contradiction }

private theorem Op.lt_trans_mkName_lt {a b c : Op}
  (h₁ : a.mkName < b.mkName)
  (h₂ : Op.lt b c = true)
  (h₃ : ∀ (f₁ f₂ : UUF), a = Op.uuf f₁ → b = Op.uuf f₂ → False)
  (h₄ : ∀ (n₁ n₂ : Nat), a = Op.zero_extend n₁ → b = Op.zero_extend n₂ → False)
  (h₅ : ∀ (a₁ a₂ : Attr), a = Op.record.get a₁ → b = Op.record.get a₂ → False)
  (h₆ : ∀ (p₁ p₂ : Pattern), a = Op.string.like p₁ → b = Op.string.like p₂ → False)
  (h₇ : ∀ (xty₁ xty₂ : ExtOp), a = Op.ext xty₁ → b = Op.ext xty₂ → False) :
  Op.lt a c = true
:= by
  simp only [Op.lt] at h₂
  split at h₂ <;> simp only [decide_eq_true_eq] at h₂
  case h_1 =>
    simp only [Op.uuf.injEq, forall_apply_eq_imp_iff] at h₃
    exact Op.lt_trans_uuf' h₁ h₃
  case h_2 =>
    simp only [Op.zero_extend.injEq, forall_apply_eq_imp_iff] at h₄
    exact Op.lt_trans_zero_extend' h₁ h₄
  case h_3 =>
    simp only [Op.record.get.injEq, forall_apply_eq_imp_iff] at h₅
    exact Op.lt_trans_record_get' h₁ h₅
  case h_4 =>
    simp only [Op.string.like.injEq, forall_apply_eq_imp_iff] at h₆
    exact Op.lt_trans_string_like' h₁ h₆
  case h_5 =>
    simp only [Op.ext.injEq, forall_apply_eq_imp_iff] at h₇
    exact Op.lt_trans_ext' h₁ h₇
  case h_6 =>
    have h₈ := String.strictLT.transitive a.mkName b.mkName c.mkName h₁ h₂
    exact Op.lt_mkName_implies_lt h₈

theorem Op.lt_trans (a b c : Op) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt]
  intro h₁ h₂
  simp only [Op.lt] at h₁
  split at h₁ <;> simp only [decide_eq_true_eq] at h₁
  case h_1 => exact Op.lt_trans_uuf h₁ h₂
  case h_2 => exact Op.lt_trans_zero_extend h₁ h₂
  case h_3 => exact Op.lt_trans_record_get h₁ h₂
  case h_4 => exact Op.lt_trans_string_like h₁ h₂
  case h_5 => exact Op.lt_trans_ext h₁ h₂
  case h_6 h₃ h₄ h₅ h₆ h₇ => exact Op.lt_trans_mkName_lt h₁ h₂ h₃ h₄ h₅ h₆ h₇

local macro "simp_op_mkName_neq_parametric" b:ident h:ident inj:ident : tactic => do
 `(tactic| (
    cases $b:ident
    any_goals (simp only [Op.mkName, not_true_eq_false] ; decide)
    simp only [$inj:ident, forall_apply_eq_imp_iff, forall_eq'] at $h:ident
    ))

private theorem Op.mkName.neq {a b: Op}
  (h₀ : ¬a = b)
  (h₁ : ∀ (f₁ f₂ : UUF), a = Op.uuf f₁ → b = Op.uuf f₂ → False)
  (h₂ : ∀ (n₁ n₂ : Nat), a = Op.zero_extend n₁ → b = Op.zero_extend n₂ → False)
  (h₃ : ∀ (a₁ a₂ : Attr), a = Op.record.get a₁ → b = Op.record.get a₂ → False)
  (h₄ : ∀ (p₁ p₂ : Pattern), a = Op.string.like p₁ → b = Op.string.like p₂ → False)
  (h₅ : ∀ (xty₁ xty₂ : ExtOp), a = Op.ext xty₁ → b = Op.ext xty₂ → False) :
  ¬ a.mkName = b.mkName
:= by
  cases a
  case uuf         => simp_op_mkName_neq_parametric b h₁ Op.uuf.injEq
  case zero_extend => simp_op_mkName_neq_parametric b h₂ Op.zero_extend.injEq
  case record.get  => simp_op_mkName_neq_parametric b h₃ Op.record.get.injEq
  case string.like => simp_op_mkName_neq_parametric b h₄ Op.string.like.injEq
  case ext         => simp_op_mkName_neq_parametric b h₅ Op.ext.injEq
  all_goals {
    cases b
    any_goals (simp only [Op.mkName] ; decide)
    simp only [not_true_eq_false] at h₀
  }

theorem Op.lt_conn {a b : Op} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [ne_eq, LT.lt] -- Must use 2 simps here to avoid
  simp only [Op.lt]        -- oversimplification of LT.lt.
  intro h
  split
  · simp only [Op.uuf.injEq, decide_eq_true_eq] at *
    exact UUF.lt_conn h
  · simp only [Op.zero_extend.injEq, Nat.lt_eq, decide_eq_true_eq] at *
    exact Nat.strictLT.connected _ _ h
  · simp only [Op.record.get.injEq, decide_eq_true_eq] at *
    exact String.strictLT.connected _ _ h
  · simp only [Op.string.like.injEq, decide_eq_true_eq] at *
    exact List.lt_conn h
  · simp only [Op.ext.injEq, decide_eq_true_eq] at *
    exact ExtOp.lt_conn h
  · rename_i h₁ h₂ h₃ h₄ h₅
    split <;> rename_i o₂ o₁
    · specialize h₁ o₁ o₂ rfl rfl ; contradiction
    · specialize h₂ o₁ o₂ rfl rfl ; contradiction
    · specialize h₃ o₁ o₂ rfl rfl ; contradiction
    · specialize h₄ o₁ o₂ rfl rfl ; contradiction
    · specialize h₅ o₁ o₂ rfl rfl ; contradiction
    · simp only [decide_eq_true_eq]
      replace h := Op.mkName.neq h h₁ h₂ h₃ h₄ h₅
      exact String.strictLT.connected _ _ h

instance Op.strictLT : StrictLT Op where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm Op.lt_trans Op.lt_irrefl
  transitive a b c := by exact Op.lt_trans a b c
  connected  a b   := by exact Op.lt_conn

----- `<` is strict on `TermVar` -----

theorem TermVar.lt_irrefl (a : TermVar) :
  ¬ TermVar.lt a a
:= by
  simp only [TermVar.lt, LT.lt, decide_true, Bool.true_and, Bool.or_eq_true, decide_eq_true_eq]
  intro h
  rcases h with h | h
  . have _ := List.slt_irrefl a.id.data ; contradiction
  . have _ := TermType.lt_irrefl a.ty ; contradiction

theorem TermVar.lt_trans (a b c : TermVar) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt, TermVar.lt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · exact Or.inl (List.slt_trans h₁ h₂)
  · simp only [h₂.left] at h₁
    exact Or.inl h₁
  · simp only [← h₁.left] at h₂
    exact Or.inl h₂
  · simp only [h₂.left] at h₁
    have h₃ := TermType.lt_trans _ _ _ h₁.right h₂.right
    simp only [LT.lt] at h₃
    exact Or.inr (And.intro h₁.left h₃)

theorem TermVar.lt_conn {a b : TermVar} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [ne_eq, LT.lt]
  simp only [TermVar.lt, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
  intro h₁
  cases a ; cases b ; rename_i aid aty bid bty
  by_cases h₂ : aid = bid
  case pos =>
    subst h₂
    simp only [forall_const, true_and] at *
    have h₂ := StrictLT.irreflexive aid
    simp only [h₂, false_or]
    simp only [TermVar.mk.injEq, true_and] at h₁
    exact TermType.lt_conn h₁
  case neg =>
    simp only
    have h₃ := String.strictLT.connected aid bid h₂
    rcases h₃ with h₃ | h₃ <;>
    simp only [h₃, true_or, or_true]

instance TermVar.strictLT : StrictLT TermVar where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm TermVar.lt_trans TermVar.lt_irrefl
  transitive a b c := by exact TermVar.lt_trans a b c
  connected  a b   := by exact TermVar.lt_conn

----- `<` is strict on `TermPrim` -----

theorem TermPrim.lt_irrefl (a : TermPrim) :
  ¬ TermPrim.lt a a
:= by
  simp only [TermPrim.lt, Bool.not_eq_true]
  cases a
  case bitvec =>
    simp only [Nat.lt_irrefl, decide_false, decide_true, Bool.and_false, Bool.or_self]
  all_goals {
    simp only [decide_eq_false_iff_not]
    apply StrictLT.irreflexive
  }

theorem TermPrim.lt_trans (a b c : TermPrim) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt]
  intro h₁ h₂
  cases a <;> cases b <;> cases c
  any_goals (by_contra ; simp_decide_lt h₁ TermPrim.lt TermPrim.mkName)
  any_goals (by_contra ; simp_decide_lt h₂ TermPrim.lt TermPrim.mkName)
  any_goals (by_contra h₃ ; simp_decide_lt h₃ TermPrim.lt TermPrim.mkName)
  case bitvec =>
    simp [TermPrim.lt] at *
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    · exact Or.inl (Nat.lt_trans h₁ h₂)
    · simp only [h₂.left] at h₁
      exact Or.inl h₁
    · simp only [← h₁.left] at h₂
      exact Or.inl h₂
    · simp only [h₂.left] at h₁
      have h₃ := Nat.lt_trans h₁.right h₂.right
      exact Or.inr (And.intro h₁.left h₃)
  all_goals {
    by_contra
    simp only [TermPrim.lt, decide_eq_true_eq] at *
    have _ := StrictLT.transitive _ _ _ h₁ h₂
    contradiction}

theorem TermPrim.lt_conn {a b : TermPrim} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [ne_eq, LT.lt]
  intro h₁
  cases a <;> cases b <;> simp only [TermPrim.lt, decide_eq_true_eq]
  any_goals (simp only [TermPrim.mkName] ; decide)
  case bool =>
    simp only [TermPrim.bool.injEq] at h₁
    exact StrictLT.connected _ _ h₁
  case string =>
    simp only [TermPrim.string.injEq] at h₁
    exact StrictLT.connected _ _ h₁
  case entity =>
    simp only [TermPrim.entity.injEq] at h₁
    exact StrictLT.connected _ _ h₁
  case ext =>
    simp only [TermPrim.ext.injEq] at h₁
    exact StrictLT.connected _ _ h₁
  case bitvec n₁ bv₁ n₂ bv₂ =>
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    simp only [TermPrim.bitvec.injEq, not_and] at h₁
    by_cases h₃ : n₁ = n₂
    case pos =>
      subst h₃
      simp only [heq_eq_eq, forall_const, Nat.lt_irrefl, true_and, false_or] at *
      have h₂ : ¬ bv₁.toNat = bv₂.toNat := by
        by_contra h₂
        simp [←BitVec.toNat_eq] at h₂
        contradiction
      exact Nat.strictLT.connected _ _ h₂
    case neg =>
      replace h₃ := Nat.strictLT.connected _ _ h₃
      rcases h₃ with h₃ | h₃ <;>
      simp only [h₃, true_or, or_true]

instance TermPrim.strictLT : StrictLT TermPrim where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm TermPrim.lt_trans TermPrim.lt_irrefl
  transitive a b c := by exact TermPrim.lt_trans a b c
  connected  a b   := by exact TermPrim.lt_conn

----- `<` is strict on `Term` -----

mutual
theorem Term.lt_irrefl (a : Term) :
  ¬ Term.lt a a
:= by
  cases a <;>
  simp only [Term.lt, decide_eq_true_eq, Bool.not_eq_true, decide_true, Bool.true_and, Bool.and_self, Bool.or_eq_true]
  case prim | var | none =>
    apply StrictLT.irreflexive
  case some t =>
    simp only [Term.lt_irrefl t]
  case set ts ty =>
    unfold Term.lt
    cases ts ; rename_i ts
    simp only [LT.lt, TermType.lt_irrefl, Bool.false_eq_true, decide_false, decide_true,
      Bool.true_and, Bool.false_or]
    simp only [Term.ltList_irrefl ts]
  case record r =>
    unfold Term.lt
    cases r ; rename_i r
    simp only [Term.ltListProd_irrefl r]
  case app op ts ty =>
    simp only [LT.lt, Op.lt_irrefl, Bool.false_eq_true, false_or, TermType.lt_irrefl, or_false,
      Bool.not_eq_true]
    simp only [Term.ltList_irrefl ts]

theorem Term.ltList_irrefl (ts : List Term) :
  ¬ Term.ltList ts ts
:= by
  cases ts
  simp only [Term.ltList, Bool.false_eq_true, not_false_eq_true]
  rename_i hd tl
  simp only [Term.ltList, decide_true, Bool.true_and, Bool.or_eq_true]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    have _ := Term.lt_irrefl hd
    contradiction
  case inr =>
    have _ := Term.ltList_irrefl tl
    contradiction

theorem Term.ltListProd_irrefl (ts : List (Attr × Term)) :
  ¬ Term.ltListProd ts ts
:= by
  cases ts
  simp only [Term.ltListProd, Bool.false_eq_true, not_false_eq_true]
  rename_i hd tl
  cases hd
  rename_i a t
  simp only [Term.ltListProd, decide_true, Bool.true_and, Bool.and_self, Bool.or_eq_true,
    decide_eq_true_eq]
  by_contra h₁
  rcases h₁ with h₁ | h₁
  case inl =>
    rcases h₁ with h₁ | h₁
    case inl =>
      have _ := StrictLT.irreflexive a
      contradiction
    case inr =>
      have _ := Term.lt_irrefl t
      contradiction
  case inr =>
    have _ := Term.ltListProd_irrefl tl
    contradiction

end

private theorem Term.lt_trans_prim {p₁ p₂ : TermPrim} {c : Term} :
  p₁ < p₂ → Term.lt (Term.prim p₂) c  → Term.lt (Term.prim p₁) c
:= by simp_lt_trans Term.lt Term.mkName c TermPrim.lt_trans

private theorem Term.lt_trans_var {v₁ v₂ : TermVar} {c : Term} :
  v₁ < v₂ → Term.lt (Term.var v₂) c  → Term.lt (Term.var v₁) c
:= by simp_lt_trans Term.lt Term.mkName c TermVar.lt_trans

private theorem Term.lt_trans_none {ty₁ ty₂ : TermType} {c : Term} :
  ty₁ < ty₂ → Term.lt (Term.none ty₂) c  → Term.lt (Term.none ty₁) c
:= by simp_lt_trans Term.lt Term.mkName c TermType.lt_trans

private theorem Term.lt_trans_app {o₁ o₂ o₃ : Op} {ts₁ ts₂ ts₃ : List Term} {ty₁ ty₂ ty₃ : TermType}
  (h₁ : (o₁ < o₂ ∨ o₁ = o₂ ∧ Term.ltList ts₁ ts₂ = true) ∨ (o₁ = o₂ ∧ ts₁ = ts₂) ∧ ty₁ < ty₂)
  (h₂ : (o₂ < o₃ ∨ o₂ = o₃ ∧ Term.ltList ts₂ ts₃ = true) ∨ (o₂ = o₃ ∧ ts₂ = ts₃) ∧ ty₂ < ty₃)
  (ih : Term.ltList ts₁ ts₂ = true → Term.ltList ts₂ ts₃ = true → Term.ltList ts₁ ts₃ = true) :
  (o₁ < o₃ ∨ o₁ = o₃ ∧ Term.ltList ts₁ ts₃ = true) ∨ (o₁ = o₃ ∧ ts₁ = ts₃) ∧ ty₁ < ty₃
:= by
  rcases h₁ with h₁ | ⟨⟨h₁, h₃⟩, h₄⟩
  · rcases h₁ with h₁ | ⟨h₁, h₅⟩
    · rcases h₂ with h₂ | ⟨⟨h₂, h₃⟩, _⟩
      · rcases h₂ with h₂ | ⟨h₂, _⟩
        · have h₃ := Op.lt_trans _ _ _ h₁ h₂
          exact (Or.inl (Or.inl h₃))
        · subst h₂
          exact (Or.inl (Or.inl h₁))
      · subst h₂ h₃
        exact (Or.inl (Or.inl h₁))
    · subst h₁
      rcases h₂ with h₂ | ⟨⟨h₂, h₃⟩, _⟩
      · rcases h₂ with h₂ | ⟨h₂, h₃⟩
        · exact (Or.inl (Or.inl h₂))
        · subst h₂
          specialize ih h₅ h₃
          simp only [true_and]
          exact (Or.inl (Or.inr ih))
      · subst h₂ h₃
        simp only [true_and]
        exact (Or.inl (Or.inr h₅))
  · subst h₁ h₃
    rcases h₂ with h₂ | ⟨h₂, h₃⟩
    · exact (Or.inl h₂)
    · exact (Or.inr (And.intro h₂ (TermType.lt_trans _ _ _ h₄ h₃)))

private theorem Term.lt_trans_set {ts₁ ts₂ ts₃ : List Term} {ty₁ ty₂ ty₃ : TermType}
  (h₁ : ty₁ < ty₂ ∨ ty₁ = ty₂ ∧ Term.ltList ts₁ ts₂ = true)
  (h₂ : ty₂ < ty₃ ∨ ty₂ = ty₃ ∧ Term.ltList ts₂ ts₃ = true)
  (ih : Term.ltList ts₁ ts₂ = true → Term.ltList ts₂ ts₃ = true → Term.ltList ts₁ ts₃ = true) :
  ty₁ < ty₃ ∨ ty₁ = ty₃ ∧ Term.ltList ts₁ ts₃ = true
:= by
  rcases h₁ with h₁ | ⟨h₁, h₃⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₄⟩
  · exact (Or.inl (TermType.lt_trans _ _ _ h₁ h₂))
  · subst h₂
    exact (Or.inl h₁)
  · subst h₁
    exact (Or.inl h₂)
  · subst h₁ h₂
    specialize ih h₃ h₄
    simp only [true_and]
    exact (Or.inr ih)

private theorem Term.lt_implies_mkName_le {a b : Term} :
  Term.lt a b → a.mkName = b.mkName ∨ a.mkName < b.mkName
:= by
  unfold Term.lt
  intro h
  cases a
  all_goals {
    cases b <;> simp only [decide_eq_true_eq, Term.mkName] at *
    any_goals (simp only [h, or_true])
    simp only [Term.mkName, true_or]
  }

private theorem Term.mkName_lt_implies_lt {a b : Term} :
  a.mkName < b.mkName → Term.lt a b
:= by
  intro h
  unfold Term.lt
  split
  any_goals (simp only [Term.mkName] at h ; contradiction)
  simp only [decide_eq_true_eq] ; exact h

mutual
theorem Term.lt_trans (a b c : Term) :
  a < b → b < c → a < c
:= by
  simp only [LT.lt]
  intro h₁ h₂
  unfold Term.lt at h₁
  split at h₁
  case h_1 =>
    simp only [decide_eq_true_eq] at h₁
    exact Term.lt_trans_prim h₁ h₂
  case h_2 =>
    simp only [decide_eq_true_eq] at h₁
    exact Term.lt_trans_var h₁ h₂
  case h_3 =>
    simp only [decide_eq_true_eq] at h₁
    exact Term.lt_trans_none h₁ h₂
  case h_4 =>
    cases c <;> unfold Term.lt at h₂ <;> unfold Term.lt
    case some => exact Term.lt_trans _ _ _ h₁ h₂
    all_goals {
      simp only [Term.mkName, String.reduceLT, decide_false, decide_true, Bool.false_eq_true] at *
    }
  case h_5 o₁ ts₁ ty₁ o₂ ts₂ ty₂ =>
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h₁
    cases c <;> unfold Term.lt at h₂ <;> unfold Term.lt
    case app o₃ ts₃ ty₃ =>
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
      have ih := @Term.ltList_trans ts₁ ts₂ ts₃
      exact Term.lt_trans_app h₁ h₂ ih
    all_goals {
      simp only [Term.mkName, String.reduceLT, decide_true] at *
    }
  case h_6 ts₁ ty₁ ts₂ ty₂ =>
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h₁
    cases c <;> unfold Term.lt at h₂ <;> unfold Term.lt
    case set ts₃ ty₃ =>
      simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
      cases ts₃ ; rename_i ts₃
      have ih := @Term.ltList_trans ts₁ ts₂ ts₃
      simp only at *
      exact Term.lt_trans_set h₁ h₂ ih
    all_goals {
      simp only [Term.mkName, String.reduceLT, decide_false, decide_true, Bool.false_eq_true] at *
    }
  case h_7 =>
    cases c <;> unfold Term.lt at h₂ <;> unfold Term.lt
    case record => exact Term.ltListProd_trans h₁ h₂
    all_goals {
      simp only [Term.mkName, String.reduceLT, decide_false, decide_true, Bool.false_eq_true] at *
    }
  case h_8 =>
    simp only [decide_eq_true_eq] at h₁
    replace h₂ := Term.lt_implies_mkName_le h₂
    rcases h₂ with h₂ | h₂
    · simp only [h₂] at h₁
      exact Term.mkName_lt_implies_lt h₁
    · have h₃ := String.strictLT.transitive _ _ _ h₁ h₂
      exact Term.mkName_lt_implies_lt h₃

theorem Term.ltList_trans {ts₁ ts₂ ts₃ : List Term}
  (h₁ : Term.ltList ts₁ ts₂)
  (h₂ : Term.ltList ts₂ ts₃) :
  Term.ltList ts₁ ts₃
:= by
  cases ts₁ <;> cases ts₂ <;> cases ts₃ <;>
  simp only [Term.ltList, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at *
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    have h₃ := Term.lt_trans _ _ _ h₁ h₂
    simp only [LT.lt] at h₃
    simp only [h₃, true_or]
  case inl.inr =>
    have ⟨h₂, _⟩ := h₂
    subst h₂ ; simp [h₁]
  case inr.inl =>
    have ⟨h₁, _⟩ := h₁
    subst h₁ ; simp [h₂]
  case inr.inr =>
    have ⟨hl₁, h₃⟩ := h₁ ; subst hl₁
    have ⟨hl₂, h₄⟩ := h₂ ; subst hl₂
    have h₃ := Term.ltList_trans h₃ h₄
    simp only [h₃, and_self, or_true]

theorem Term.ltListProd_trans {ts₁ ts₂ ts₃ : List (Attr × Term)}
  (h₁ : Term.ltListProd ts₁ ts₂)
  (h₂ : Term.ltListProd ts₂ ts₃) :
  Term.ltListProd ts₁ ts₃
:= by
  cases ts₁ <;> cases ts₂ <;> cases ts₃ <;>
  try { simp only [Term.ltListProd, Bool.false_eq_true] at * }
  rename_i hd₁ tl₁ hd₂ tl₂ hd₃ tl₃
  cases hd₁ ; cases hd₂ ; cases hd₃ ;
  simp only [Term.ltListProd, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at *
  rename_i a₁ t₁ a₂ t₂ a₃ t₃
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  case inl.inl =>
    rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
    case inl.inl =>
      have h₃ := String.strictLT.transitive a₁ a₂ a₃ h₁ h₂
      simp only [h₃, true_or]
    case inl.inr =>
      have ⟨h₂, _⟩ := h₂ ; subst h₂
      simp only [h₁, true_or]
    case inr.inl =>
      have ⟨h₁, _⟩ := h₁ ; subst h₁
      simp only [h₂, true_or]
    case inr.inr =>
      have ⟨hl₁, h₃⟩ := h₁ ; subst hl₁
      have ⟨hl₂, h₄⟩ := h₂ ; subst hl₂
      have h₃ := Term.lt_trans _ _ _ h₃ h₄
      simp only [LT.lt] at h₃
      simp only [h₃, and_self, or_true, true_and, true_or]
  case inl.inr =>
    have ⟨⟨hl₂, hr₂⟩, _⟩ := h₂
    subst hl₂ hr₂
    simp only [h₁, true_or]
  case inr.inl =>
    have ⟨⟨hl₁, hr₁⟩, _⟩ := h₁
    subst hl₁ hr₁
    simp only [h₂, true_or]
  case inr.inr =>
    have ⟨⟨hl₁, hr₁⟩, h₃⟩ := h₁
    subst hl₁ hr₁
    have ⟨⟨hl₂, hr₂⟩, h₄⟩ := h₂
    subst hl₂ hr₂
    have h₅ := Term.ltListProd_trans h₃ h₄
    simp only [true_and, and_self, h₅, or_true]

end

private theorem Term.lt_conn_set {ts₁ ts₂ : List Term} {ty₁ ty₂ : TermType}
  (h : ty₁ = ty₂ → ¬ts₁ = ts₂)
  (ih : ¬ts₁ = ts₂ → Term.ltList ts₁ ts₂ ∨ Term.ltList ts₂ ts₁) :
  (ty₁ < ty₂ ∨ ty₁ = ty₂ ∧ Term.ltList ts₁ ts₂ = true) ∨ ty₂ < ty₁ ∨ ty₂ = ty₁ ∧ Term.ltList ts₂ ts₁ = true
:= by
  by_cases hty : ty₁ = ty₂
  case pos =>
    subst hty
    simp only [forall_const] at h
    specialize ih h
    rcases ih with ih | ih <;>
    simp only [ih, and_self, or_true, true_and, true_or]
  case neg =>
    replace hty := TermType.lt_conn hty
    rcases hty with hty | hty <;>
    simp only [hty, true_or, or_true]

private theorem Term.lt_conn_app {o₁ o₂: Op} {ts₁ ts₂ : List Term} {ty₁ ty₂ : TermType }
  (h : ¬(o₁ = o₂ ∧ ts₁ = ts₂ ∧ ty₁ = ty₂))
  (ih : ¬ts₁ = ts₂ → Term.ltList ts₁ ts₂ = true ∨ Term.ltList ts₂ ts₁ = true) :
 ((o₁ < o₂ ∨ o₁ = o₂ ∧ Term.ltList ts₁ ts₂ = true) ∨ (o₁ = o₂ ∧ ts₁ = ts₂) ∧ ty₁ < ty₂) ∨
  (o₂ < o₁ ∨ o₂ = o₁ ∧ Term.ltList ts₂ ts₁ = true) ∨ (o₂ = o₁ ∧ ts₂ = ts₁) ∧ ty₂ < ty₁
:= by
  by_cases ho : o₁ = o₂
  · subst ho
    simp only [true_and, not_and] at *
    by_cases hts : ts₁ = ts₂
    · subst hts
      simp only [not_true_eq_false, or_self, false_implies, forall_const, true_and] at *
      replace h := TermType.lt_conn h
      rcases h with h | h <;>
      simp only [h, or_true, true_or]
    · specialize ih hts
      rcases ih with ih | ih <;>
      simp only [ih, or_true, true_or]
  · replace ho := Op.lt_conn ho
    rcases ho with ho | ho <;>
    simp only [ho, or_true, true_or]

mutual
theorem Term.lt_conn {a b : Term} :
  a ≠ b → (a < b ∨ b < a)
:= by
  simp only [ne_eq, LT.lt]
  intro h₁
  unfold Term.lt
  cases a
  case prim | var | none =>
    cases b <;> simp only [decide_eq_true_eq]
    any_goals (simp only [Term.mkName, String.reduceLT, or_false, or_true])
    simp only [Term.prim.injEq, Term.var.injEq, Term.none.injEq] at h₁
    exact StrictLT.connected _ _ h₁
  case some =>
    cases b <;> simp only [decide_eq_true_eq]
    any_goals (simp only [Term.mkName, String.reduceLT, or_false, or_true])
    simp only [Term.some.injEq] at h₁
    exact Term.lt_conn h₁
  case set ts₁ ty₁ =>
    cases b <;> simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    any_goals (simp only [Term.mkName, String.reduceLT, or_false, or_true])
    simp only [Term.set.injEq] at h₁
    rename_i ts₂ ty₂
    cases ts₁ ; cases ts₂ ; rename_i ts₁ ts₂
    simp only [Set.mk.injEq, not_and'] at *
    have ih := @Term.ltList_conn ts₁ ts₂
    exact Term.lt_conn_set h₁ ih
  case record r₁ =>
    cases b <;> simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    any_goals (simp only [Term.mkName, String.reduceLT, or_false, or_true])
    simp only [Term.record.injEq] at h₁
    rename_i r₂
    cases r₁ ; cases r₂ ; rename_i r₁ r₂
    simp only [Map.mk.injEq] at *
    exact Term.ltListProd_conn h₁
  case app o₁ ts₁ ty₁ =>
    cases b <;> simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true]
    any_goals (simp only [Term.mkName, String.reduceLT, or_false, or_true])
    simp only [Term.app.injEq] at h₁
    rename_i o₂ ts₂ ty₂
    have ih := @Term.ltList_conn ts₁ ts₂
    exact Term.lt_conn_app h₁ ih

theorem Term.ltList_conn {ts₁ ts₂ : List Term}
  (h₁ : ¬ts₁ = ts₂) :
  Term.ltList ts₁ ts₂ ∨ Term.ltList ts₂ ts₁
:= by
  cases ts₁ <;> cases ts₂ <;>
  simp only [Term.ltList, or_self, or_false, or_true, Bool.false_eq_true, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] <;>
  try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  simp only [List.cons.injEq, not_and] at h₁
  by_cases h₂ : (hd₁ = hd₂)
  case pos =>
    simp only [h₂, forall_const, true_and] at *
    have h₃ := Term.ltList_conn h₁
    rcases h₃ with h₃ | h₃ <;>
    simp only [h₃, or_true, true_or]
  case neg =>
    have h₃ := Term.lt_conn h₂
    simp only [LT.lt] at h₃
    rcases h₃ with h₃ | h₃ <;>
    simp only [h₃, true_or, or_true]

theorem Term.ltListProd_conn {ts₁ ts₂ : List (Attr × Term)}
  (h₁ : ¬ts₁ = ts₂) :
  Term.ltListProd ts₁ ts₂ ∨ Term.ltListProd ts₂ ts₁
:= by
  cases ts₁ <;> cases ts₂ <;>
  try { simp [Term.ltListProd] } <;>
  try contradiction
  rename_i hd₁ tl₁ hd₂ tl₂
  cases hd₁ ; cases hd₂ ; simp [Term.ltListProd]
  rename_i a₁ t₁ a₂ t₂
  simp only [List.cons.injEq, Prod.mk.injEq, not_and, and_imp] at h₁
  by_cases h₂ : (a₁ = a₂)
  case pos =>
    subst h₂ ; simp only [forall_const, true_and] at *
    by_cases h₃ : (t₁ = t₂)
    case pos =>
      subst h₃ ; simp only [forall_const, true_and] at *
      have h₂ := Term.ltListProd_conn h₁
      rcases h₂ with h₂ | h₂ <;>
      simp only [h₂, or_true, true_or]
    case neg =>
      have h₄ := Term.lt_conn h₃
      simp only [LT.lt] at h₄
      rcases h₄ with h₄ | h₄ <;>
      simp only [h₄, or_true, true_or]
  case neg =>
    have h₃ := String.strictLT.connected a₁ a₂
    simp only [ne_eq, h₂, not_false_eq_true, forall_const] at h₃
    rcases h₃ with h₃ | h₃ <;>
    simp only [h₃, true_or, or_true]

end

instance Term.strictLT : StrictLT Term where
  asymmetric a b   := by exact lt_trans_irrefl_implies_asymm Term.lt_trans Term.lt_irrefl
  transitive a b c := by exact Term.lt_trans a b c
  connected  a b   := by exact Term.lt_conn

end Cedar.Thm
