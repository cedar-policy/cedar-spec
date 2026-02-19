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

import Cedar.Thm.SymCC.Data.Basic
import Cedar.Thm.SymCC.Term.Lit
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Interpretation

/-!
# Basic properties of partial evaluation of terms

This file proves basic lemmas about the Factory functions on terms
when applied to literal (concrete) inputs.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

local macro "show_pe_unary_wfl" op_fun:ident ht_thm:ident : tactic => do
 `(tactic| (
    intro h₁ h₂
    have ⟨_, h₃⟩ := $ht_thm:ident h₁ h₂
    subst h₃
    simp only [$op_fun:ident, Term.isLiteral]))

local macro "show_pe_binary_wfl" op_fun:ident impl_fun:ident ht_thm:ident : tactic => do
 `(tactic| (
    intro h₁ h₂ h₃ h₄
    have ⟨_, ht₁⟩ := $ht_thm h₁ h₂
    have ⟨_, ht₂⟩ := $ht_thm h₃ h₄
    subst ht₁ ht₂
    simp only [$op_fun:ident, $impl_fun:ident, Term.isLiteral]))

/-! ### PE for Factory.not -/

theorem pe_not_true :
  Factory.not (.prim (.bool true)) = .prim (.bool false)
:= by simp [Factory.not]

theorem pe_not_false :
  Factory.not (.prim (.bool false)) = .prim (.bool true)
:= by simp [Factory.not]

theorem pe_not_lit {b : Bool} :
  Factory.not (.prim (.bool b)) = .prim (.bool (!b))
:= by simp [Factory.not]

theorem pe_not_wfl {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs → t.typeOf = .bool →
  (Factory.not t).isLiteral
:= by
  intro h₁ h₂
  replace h₁ := wfl_of_type_bool_is_true_or_false h₁ h₂
  rcases h₁ with h₁ | h₁ <;>
  simp only [h₁, pe_not_true, pe_not_false, Term.isLiteral]

/-! ### PE for Factory.and -/

theorem pe_and_wfl {εs : SymEntities} {t₁ t₂ : Term} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bool →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bool →
  Term.isLiteral (Factory.and t₁ t₂) = true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨b₁, ht₁⟩ := wfl_of_type_bool_is_bool h₁ h₂
  have ⟨b₂, ht₂⟩ := wfl_of_type_bool_is_bool h₃ h₄
  subst ht₁ ht₂
  cases b₁ <;> cases b₂ <;> simp [Factory.and, Term.isLiteral]

theorem pe_and_false_left {t : Term} :
  Factory.and false t = false
:= by
  simp only [Factory.and, Bool.or_eq_true, decide_eq_true_eq, Term.prim.injEq, TermPrim.bool.injEq,
    Bool.false_eq_true, ↓reduceIte, decide_true, Bool.true_or, ite_self]

theorem pe_and_false_right {t : Term} :
  Factory.and t false = false
:= by
  simp only [Factory.and, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true, decide_false,
    Bool.or_false, decide_eq_true_eq, decide_true, Bool.or_true, Bool.true_or, ↓reduceIte, ite_self,
    ite_eq_right_iff, imp_self]

theorem pe_and_true_left {t : Term} :
  Factory.and true t = t
:= by
  simp only [Factory.and, Bool.or_eq_true, decide_eq_true_eq, ↓reduceIte, ite_eq_right_iff]
  intro h
  rcases h with h | h <;>
  simp only [h]

theorem pe_and_true_right {t : Term} :
  Factory.and t true = t
:= by
  simp only [Factory.and, decide_true, Bool.or_true, ↓reduceIte]

theorem pe_and_true_iff_true {t₁ t₂ : Term} :
  Factory.and t₁ t₂ = true ↔ t₁ = true ∧ t₂ = true
:= by
  constructor
  · intro h₁
    simp only [Factory.and, Bool.or_eq_true, decide_eq_true_eq] at h₁
    split at h₁
    · rename_i h₂
      rcases h₂ with h₂ | h₂
      · subst h₂
        simp only [h₁, and_self]
      · simp only [h₁, h₂, and_self]
    · split at h₁
      · rename_i h₂
        simp only [h₁, h₂, and_self]
      · split at h₁ <;>
        simp only [Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true, reduceCtorEq] at h₁
  · intro ⟨ht₁, ht₂⟩
    subst ht₁ ht₂
    simp only [pe_and_true_left]

/-! ### PE for Factory.or -/

theorem pe_or_wfl {εs : SymEntities} {t₁ t₂ : Term} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bool →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bool →
  Term.isLiteral (Factory.or t₁ t₂) = true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨b₁, ht₁⟩ := wfl_of_type_bool_is_bool h₁ h₂
  have ⟨b₂, ht₂⟩ := wfl_of_type_bool_is_bool h₃ h₄
  subst ht₁ ht₂
  cases b₁ <;> cases b₂ <;> simp [Factory.or, Term.isLiteral]

theorem pe_or_true_left {t : Term} :
  Factory.or true t = true
:= by
  simp only [Factory.or, Bool.or_eq_true, decide_eq_true_eq, Term.prim.injEq, TermPrim.bool.injEq,
    Bool.true_eq_false, ↓reduceIte, decide_true, Bool.true_or, ite_self]

theorem pe_or_true_right {t : Term} :
  Factory.or t true = true
:= by
  simp only [Factory.or, Term.prim.injEq, TermPrim.bool.injEq, Bool.true_eq_false, decide_false,
    Bool.or_false, decide_eq_true_eq, decide_true, Bool.or_true, Bool.true_or, ↓reduceIte, ite_self,
    ite_eq_right_iff, imp_self]

theorem pe_or_false_left {t : Term} :
  Factory.or false t = t
:= by
  simp only [Factory.or, Bool.or_eq_true, decide_eq_true_eq, ↓reduceIte, ite_eq_right_iff]
  rw [eq_comm]
  simp only [or_self, imp_self]

theorem pe_or_false_right {t : Term} :
  Factory.or t false = t
:= by
  simp only [Factory.or, decide_true, Bool.or_true, ↓reduceIte]

/-! ### PE for Factory.implies -/

theorem pe_implies_false_left {t : Term} :
  Factory.implies false t = true
:= by
  simp only [implies, pe_not_false, pe_or_true_left]

theorem pe_implies_true_left {t : Term} :
  Factory.implies true t = t
:= by
  simp only [implies, pe_not_true, pe_or_false_left]

/-! ### PE for Factory.ite -/

theorem pe_ite_simplify_true {t₁ t₂ : Term} :
  Factory.ite.simplify (.prim (.bool true)) t₁ t₂ = t₁
:= by simp [ite.simplify]

theorem pe_ite_simplify_false {t₁ t₂ : Term} :
  Factory.ite.simplify (.prim (.bool false)) t₁ t₂ = t₂
:= by simp [ite.simplify]

theorem pe_ite_true {t₁ t₂ : Term} :
  Factory.ite (.prim (.bool true)) t₁ t₂ = t₁
:= by
  simp only [Factory.ite]
  split <;> simp [pe_ite_simplify_true]

theorem pe_ite_false {t₁ t₂ : Term} :
  Factory.ite (.prim (.bool false)) t₁ t₂ = t₂
:= by
  simp only [Factory.ite]
  split <;> simp [pe_ite_simplify_false]

theorem pe_ite_wfl {εs : SymEntities} {t₁ t₂ t₃ : Term} :
  Term.WellFormedLiteral εs t₁ →
  Term.WellFormedLiteral εs t₂ →
  Term.WellFormedLiteral εs t₃ →
  t₁.typeOf = .bool →
  Term.isLiteral (Factory.ite t₁ t₂ t₃) = true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨b₁, ht₁⟩ := wfl_of_type_bool_is_bool h₁ h₄
  subst ht₁
  cases b₁
  case false => simp only [pe_ite_false, h₃.right]
  case true  => simp only [pe_ite_true, h₂.right]

/-! ### PE for Factory.eq -/

theorem pe_eq_simplify_same {t : Term} :
  Factory.eq.simplify t t = .prim (.bool true)
:= by simp [Factory.eq.simplify]

theorem pe_eq_same {t : Term} :
  Factory.eq t t = .prim (.bool true)
:= by simp only [Factory.eq] ; split <;> simp [pe_eq_simplify_same]

theorem pe_eq_some_none {t : Term} {ty : TermType} :
  Factory.eq (Term.some t) (Term.none ty) = .prim (.bool false)
:= by simp [Factory.eq]

theorem pe_eq_none_some {t : Term} {ty : TermType} :
  Factory.eq (Term.none ty) (Term.some t) = .prim (.bool false)
:= by simp [Factory.eq]

theorem pe_eq_some_some {t₁ t₂ : Term} :
  Factory.eq (Term.some t₁) (Term.some t₂) = Factory.eq.simplify t₁ t₂
:= by simp [Factory.eq]

theorem pe_eq_simplify_lit {t₁ t₂ : Term} :
  t₁.isLiteral → t₂.isLiteral →
  Term.isLiteral (Factory.eq.simplify t₁ t₂) ∧
  Factory.eq.simplify t₁ t₂ = (t₁ == t₂)
:= by
  fun_cases Factory.eq.simplify t₁ t₂
  <;> simp_all [Term.isLiteral]

theorem pe_eq_lit {t₁ t₂ : Term} :
  t₁.isLiteral → t₂.isLiteral →
  Term.isLiteral (Factory.eq t₁ t₂) ∧
  Factory.eq t₁ t₂ = (t₁ == t₂)
:= by
  fun_cases Factory.eq t₁ t₂
  · intro h₁ h₂
    have h₃ := pe_eq_simplify_lit (lit_term_some_implies_lit h₁) (lit_term_some_implies_lit h₂)
    rw [h₃.left, h₃.right]
    simp only [Term.prim.injEq, TermPrim.bool.injEq]
    rename_i t₁ t₂
    cases h : t₁ == t₂ <;> simp_all
  · simp [Term.isLiteral]
  · simp [Term.isLiteral]
  · exact pe_eq_simplify_lit

theorem pe_eq_prim {p₁ p₂ : TermPrim} :
  Factory.eq (.prim p₁) (.prim p₂) = (p₁ == p₂)
:= by
  simp only [@pe_eq_lit (.prim p₁) (.prim p₂) term_prim_is_lit term_prim_is_lit, BEq.beq,
    Term.prim.injEq]

/-! ### PE for Factory.option.get and Factory.option.get' -/

theorem pe_option_get_some {t : Term} :
  Factory.option.get (Term.some t) = t
:= by simp only [option.get]

theorem pe_option_get'_some {I : Interpretation} {t : Term} :
  Factory.option.get' I (Term.some t) = t
:= by simp only [option.get', option.get]

theorem pe_option_get'_wfl {εs : SymEntities} {I : Interpretation} {t : Term} {ty : TermType} :
  I.WellFormed εs → t.WellFormedLiteral εs → t.typeOf = .option ty →
  (Factory.option.get' I t).isLiteral
:= by
  intro hI hwf ht
  simp only [Factory.option.get']
  rcases wfl_of_type_option_is_option hwf ht with hlit | hlit
  case inl =>
    simp only [hlit] at hwf
    replace hwf := wf_term_none_implies hwf.left
    simp only [hlit, (wf_interpretation_implies_wfp_option_get hI hwf rfl).left.right]
  case inr =>
    replace ⟨_, hlit, _⟩ := hlit
    simp only [hlit, pe_option_get_some]
    simp only [hlit] at hwf
    exact lit_term_some_implies_lit hwf.right

/-! ### PE for Factory.isNone and Factory.isSome -/

theorem pe_isNone_none {ty : TermType} :
  isNone (Term.none ty) = .prim (.bool true)
:= by simp [Factory.isNone]

theorem pe_isNone_some {t : Term} :
  isNone (Term.some t) = .prim (.bool false)
:= by simp [Factory.isNone]

theorem pe_isSome_none {ty : TermType} :
  isSome (Term.none ty) = .prim (.bool false)
:= by simp only [isSome, pe_isNone_none, pe_not_true]

theorem pe_isSome_some {t : Term} :
  isSome (Term.some t) = .prim (.bool true)
:= by simp only [isSome, pe_isNone_some, pe_not_false]

/-! ### PE for Factory.ifSome -/

theorem pe_ifSome_none {t : Term} {gty tty : TermType} :
  t.typeOf = .option tty →
  ifSome (Term.none gty) t = Term.none tty
:= by
  intro h
  simp only [ifSome, h, pe_isNone_none, pe_ite_true, noneOf]

theorem pe_ifSome_some {g t : Term} {tty : TermType} :
  t.typeOf = .option tty →
  ifSome (Term.some g) t = t
:= by
  intro h
  simp only [ifSome, h, pe_isNone_some, pe_ite_false, noneOf]

theorem pe_ifSome_get_eq_get' {εs : SymEntities} (I : Interpretation) {t : Term} {ty ty' : TermType} (f : Term → Term) :
  t.WellFormedLiteral εs →
  t.typeOf = .option ty →
  (f (option.get t)).typeOf = .option ty' →
  (f (option.get' I t)).typeOf = .option ty' →
  ifSome t (f (option.get t)) =
  ifSome t (f (option.get' I t))
:= by
  intro h₁ h₂ h₃ h₄
  simp only [ifSome, h₃, h₄]
  have h₅ := wfl_of_type_option_is_option h₁ h₂
  rcases h₅ with h₅ | h₅
  case inl =>
    subst h₅
    simp only [pe_isNone_none, pe_ite_true]
  case inr =>
    replace ⟨_, h₅, _⟩ := h₅ ; subst h₅
    simp only [pe_isNone_some, pe_ite_false, pe_option_get_some, pe_option_get'_some]

theorem pe_ifSome_get_eq_get'₂ {εs : SymEntities} (I : Interpretation) {t₁ t₂ : Term} {ty₁ ty₂ ty₃ : TermType} (f : Term → Term → Term)
  (hwφ₁ : Term.WellFormedLiteral εs t₁ ∧ Term.typeOf t₁ = TermType.option ty₁)
  (hwφ₂ : Term.WellFormedLiteral εs t₂ ∧ Term.typeOf t₂ = TermType.option ty₂)
  (hty₁ : Term.typeOf (f (option.get t₁) (option.get t₂)) = TermType.option ty₃)
  (hty₂ : Term.typeOf (f (option.get' I t₁) (option.get' I t₂)) = TermType.option ty₃) :
  ifSome t₁ (ifSome t₂ (f (option.get t₁) (option.get t₂))) =
  ifSome t₁ (ifSome t₂ (f (option.get' I t₁) (option.get' I t₂)))
:= by
  simp only [ifSome, hty₁, hty₂]
  have hwo₁ := wfl_of_type_option_is_option hwφ₁.left hwφ₁.right
  have hwo₂ := wfl_of_type_option_is_option hwφ₂.left hwφ₂.right
  rcases hwo₁ with hwo₁ | hwo₁ <;>
  rcases hwo₂ with hwo₂ | hwo₂
  case inl.inl =>
    subst hwo₁ hwo₂
    simp only [pe_isNone_none, pe_ite_true]
  case inl.inr =>
    subst hwo₁
    replace ⟨_, hwo₂, _⟩ := hwo₂ ; subst hwo₂
    simp only [pe_isNone_some, pe_ite_false, hty₁, hty₂, pe_isNone_none, pe_ite_true]
  case inr.inl =>
    subst hwo₂
    replace ⟨_, hwo₁, _⟩ := hwo₁ ; subst hwo₁
    simp only [pe_isNone_some, pe_ite_false, pe_isNone_none, pe_ite_true]
  case inr.inr =>
    replace ⟨_, hwo₁, _⟩ := hwo₁ ; subst hwo₁
    replace ⟨_, hwo₂, _⟩ := hwo₂ ; subst hwo₂
    simp only [pe_isNone_some, pe_ite_false, pe_option_get_some, pe_option_get'_some]

theorem pe_ifSome_ok_get_eq_get' {εs : SymEntities} (I : Interpretation) {t₁ t₂ t₃ : Term} {ty₁ ty₂ : TermType} (f : Term → SymCC.Result Term)
  (hwφ₁ : Term.WellFormedLiteral εs t₁ ∧ Term.typeOf t₁ = TermType.option ty₁)
  (hty₂ : Term.typeOf t₂ = TermType.option ty₂)
  (hty₃ : Term.typeOf t₃ = TermType.option ty₂)
  (hok₂ : f (option.get' I t₁) = .ok t₂)
  (hok₃ : f (option.get t₁) = .ok t₃) :
  ifSome t₁ t₃ = ifSome t₁ t₂
:= by
  simp only [ifSome, hty₂, hty₃]
  have hwo₁ := wfl_of_type_option_is_option hwφ₁.left hwφ₁.right
  rcases hwo₁ with hwo₁ | hwo₁
  case inl =>
    subst hwo₁
    simp only [pe_isNone_none, pe_ite_true]
  case inr =>
    replace ⟨_, hwo₁, _⟩ := hwo₁ ; subst hwo₁
    simp only [pe_isNone_some, pe_ite_false]
    simp only [pe_option_get'_some] at hok₂
    simp only [pe_option_get_some, hok₂, Except.ok.injEq] at hok₃
    simp only [hok₃]

theorem pe_ifSome_ok_get_eq_get'₂ {εs : SymEntities} (I : Interpretation) {t₁ t₂ t₃ t₄ : Term} {ty₁ ty₂ ty₃ : TermType} (f : Term → Term → SymCC.Result Term)
  (hwφ₁ : Term.WellFormedLiteral εs t₁ ∧ Term.typeOf t₁ = TermType.option ty₁)
  (hwφ₂ : Term.WellFormedLiteral εs t₂ ∧ Term.typeOf t₂ = TermType.option ty₂)
  (hty₃ : Term.typeOf t₃ = TermType.option ty₃)
  (hty₄ : Term.typeOf t₄ = TermType.option ty₃)
  (hok₃ : f (option.get' I t₁) (option.get' I t₂) = .ok t₃)
  (hok₄ : f (option.get t₁) (option.get t₂) = .ok t₄) :
  ifSome t₁ (ifSome t₂ t₄) = ifSome t₁ (ifSome t₂ t₃)
:= by
  simp only [ifSome, hty₃, hty₄]
  have hwo₁ := wfl_of_type_option_is_option hwφ₁.left hwφ₁.right
  have hwo₂ := wfl_of_type_option_is_option hwφ₂.left hwφ₂.right
  rcases hwo₁ with hwo₁ | hwo₁ <;>
  rcases hwo₂ with hwo₂ | hwo₂
  case inl.inl =>
    subst hwo₁ hwo₂
    simp only [pe_isNone_none, pe_ite_true]
  case inl.inr =>
    subst hwo₁
    replace ⟨_, hwo₂, _⟩ := hwo₂ ; subst hwo₂
    simp only [pe_isNone_some, pe_ite_false, hty₃, hty₄, pe_isNone_none, pe_ite_true]
  case inr.inl =>
    subst hwo₂
    replace ⟨_, hwo₁, _⟩ := hwo₁ ; subst hwo₁
    simp only [pe_isNone_some, pe_ite_false, pe_isNone_none, pe_ite_true]
  case inr.inr =>
    replace ⟨_, hwo₁, _⟩ := hwo₁ ; subst hwo₁
    replace ⟨_, hwo₂, _⟩ := hwo₂ ; subst hwo₂
    simp only [pe_isNone_some, pe_ite_false]
    simp only [pe_option_get'_some] at hok₃
    simp only [pe_option_get_some, hok₃, Except.ok.injEq] at hok₄
    simp only [hok₄]

/-! ### PE for Factory.anyNone and Factory.ifAllSome -/

private theorem pe_foldl_or_right_true {ts : List Term} {f : Term → Term} :
  ts.foldl (λ acc t => Factory.or (f t) acc) true = true
:= by
  induction ts
  case nil =>
    simp only [List.foldl_nil]
  case cons hd tl ih =>
    simp only [List.foldl_cons, pe_or_true_right, ih]

theorem pe_wfls_of_type_option {εs : SymEntities} {ts : List Term}
  (hwφ : ∀ t ∈ ts, t.WellFormedLiteral εs ∧ ∃ ty, t.typeOf = .option ty) :
  (∃ ty, .none ty ∈ ts) ∨
  (∃ ts', ts = List.map Term.some ts')
:= by
  induction ts
  case nil =>
    simp only [List.not_mem_nil, exists_const, false_or]
    exists []
  case cons hd tl ih =>
    have hwt : ∀ (t : Term), t ∈ tl → Term.WellFormedLiteral εs t ∧ ∃ ty, Term.typeOf t = TermType.option ty := by
      intro t ht
      exact hwφ t (by simp only [List.mem_cons, ht, or_true])
    replace ih := ih hwt
    simp only [List.mem_cons, forall_eq_or_imp] at *
    replace ⟨⟨hw, _, hty⟩, _⟩ := hwφ
    replace hw := wfl_of_type_option_is_option hw hty
    rcases hw with hw | ⟨hd', hw, _⟩ <;> subst hw
    case inl ty _ =>
      apply Or.inl
      simp only [Term.none.injEq]
      exists ty
      exact Or.inl rfl
    case inr =>
      rcases ih with ih | ⟨tl', ih⟩ <;>
      simp only [false_or, ih, true_or, reduceCtorEq]
      subst ih
      simp only [List.mem_map, and_false, exists_const, false_or, reduceCtorEq]
      exists (hd' :: tl')

theorem pe_anyTrue_true {f : Term → Term} {ts : List Term} {t : Term} :
  t ∈ ts → f t = true →
  anyTrue f ts = true
:= by
  intro hin ht
  unfold anyTrue
  generalize hf : Term.prim (TermPrim.bool false) = init
  clear hf
  induction ts generalizing init
  case nil =>
    simp only [List.not_mem_nil] at hin
  case cons hd tl ih =>
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hin
    rcases hin with hin | hin
    case inl =>
      subst hin
      simp only [ht, pe_or_true_left, pe_foldl_or_right_true]
    case inr =>
      exact ih hin _

theorem pe_anyTrue_false {f : Term → Term} {ts : List Term} :
  (∀ t ∈ ts, f t = false) →
  anyTrue f ts = false
:= by
  intro hf
  unfold anyTrue
  generalize hf : Term.prim (TermPrim.bool false) = init
  clear hf
  induction ts generalizing init
  case nil =>
    simp only [List.foldl_nil]
  case cons hd tl ih =>
    simp only [List.foldl_cons]
    have hdf := hf hd
    simp only [List.mem_cons, true_or, forall_const] at hdf
    simp only [hdf, pe_or_false_left]
    apply ih
    intro _ hin
    apply hf
    simp only [List.mem_cons, hin, or_true]

theorem pe_anyNone_true {ts : List Term} {ty : TermType} :
  Term.none ty ∈ ts →
  anyNone ts = true
:= by
  unfold anyNone
  intro hin
  exact pe_anyTrue_true hin pe_isNone_none

theorem pe_anyNone_false {ts : List Term} :
  anyNone (ts.map Term.some) = false
:= by
  apply pe_anyTrue_false
  intro t hin
  simp only [List.mem_map] at hin
  replace ⟨_, _, hin⟩ := hin
  simp only [← hin, pe_isNone_some]

theorem pe_ifAllSome_none {ts : List Term} {t : Term} {ty₁ ty₂ : TermType} :
  Term.none ty₁ ∈ ts →
  t.typeOf = .option ty₂ →
  ifAllSome ts t = .none ty₂
:= by
  intro hn hty
  simp only [ifAllSome, hty, pe_anyNone_true hn, noneOf, pe_ite_true]

theorem pe_ifAllSome_some {ts : List Term} {t : Term} {ty : TermType} :
  t.typeOf = .option ty →
  ifAllSome (ts.map Term.some) t = t
:= by
  intro hty
  simp only [ifAllSome, hty, pe_anyNone_false, pe_ite_false]

/-! ### PE for Factory.ifFalse and Factory.ifTrue -/

theorem pe_ifFalse_true {t : Term} :
  ifFalse (.prim (.bool true)) t = .none t.typeOf
:= by simp only [ifFalse, pe_ite_true, noneOf]

theorem pe_ifFalse_false {t : Term} :
  ifFalse (.prim (.bool false)) t = .some t
:= by simp only [ifFalse, pe_ite_false, someOf]

theorem pe_ifTrue_true {t : Term} :
  ifTrue (.prim (.bool true)) t = .some t
:= by simp only [ifTrue, pe_ite_true, someOf]

theorem pe_ifTrue_false {t : Term} :
  ifTrue (.prim (.bool false)) t = .none t.typeOf
:= by simp only [ifTrue, pe_ite_false, noneOf]

/-! ### PE for Factory.app -/

theorem pe_app_wfl {εs : SymEntities} {f : UDF} {t : Term} :
  Term.WellFormedLiteral εs t →
  UDF.WellFormed εs f →
  Term.isLiteral (app (UnaryFunction.udf f) t) = true
:= by
  intros h₁ h₂
  have h₃ := h₂.left
  replace h₂ := h₂.right.right.right
  simp only [app, h₁.right, ite_true]
  split
  case h_1 t' h₄ =>
    specialize h₂ t t' (Map.find?_mem_toList h₄)
    exact h₂.right.right.left.right
  case h_2 => exact h₃.right

/-! ### PE for Factory bitvector operators -/

theorem pe_bvneg_wfl {εs : SymEntities} {t : Term} {n : Nat} :
  t.WellFormedLiteral εs → t.typeOf = .bitvec n →
  (Factory.bvneg t).isLiteral
:= by show_pe_unary_wfl bvneg wfl_of_type_bitvec_is_bitvec

theorem pe_bvnego_wfl {εs : SymEntities} {t : Term} {n : Nat} :
  t.WellFormedLiteral εs → t.typeOf = .bitvec n →
  (Factory.bvnego t).isLiteral
:= by show_pe_unary_wfl bvnego wfl_of_type_bitvec_is_bitvec

theorem pe_zero_extend_wfl {εs : SymEntities} {t : Term} {n m : Nat} :
  t.WellFormedLiteral εs → t.typeOf = .bitvec m →
  (Factory.zero_extend n t).isLiteral
:= by show_pe_unary_wfl zero_extend wfl_of_type_bitvec_is_bitvec

theorem pe_bvadd_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvadd t₁ t₂) = true
:= by show_pe_binary_wfl bvadd bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvsub_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsub t₁ t₂) = true
:= by show_pe_binary_wfl bvsub bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvmul_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvmul t₁ t₂) = true
:= by show_pe_binary_wfl bvmul bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvsdiv_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsdiv t₁ t₂) = true
:= by show_pe_binary_wfl bvsdiv bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvudiv_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvudiv t₁ t₂) = true
:= by show_pe_binary_wfl bvudiv bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvsrem_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsrem t₁ t₂) = true
:= by show_pe_binary_wfl bvsrem bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvsmod_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsmod t₁ t₂) = true
:= by show_pe_binary_wfl bvsmod bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvumod_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvumod t₁ t₂) = true
:= by show_pe_binary_wfl bvumod bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvshl_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvshl t₁ t₂) = true
:= by show_pe_binary_wfl bvshl bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvlshr_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvlshr t₁ t₂) = true
:= by show_pe_binary_wfl bvlshr bvapp wfl_of_type_bitvec_is_bitvec

theorem pe_bvslt_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvslt t₁ t₂) = true
:= by show_pe_binary_wfl bvslt bvcmp wfl_of_type_bitvec_is_bitvec

theorem pe_bvsle_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsle t₁ t₂) = true
:= by show_pe_binary_wfl bvsle bvcmp wfl_of_type_bitvec_is_bitvec

theorem pe_bvult_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvult t₁ t₂) = true
:= by show_pe_binary_wfl bvult bvcmp wfl_of_type_bitvec_is_bitvec

theorem pe_bvule_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvule t₁ t₂) = true
:= by show_pe_binary_wfl bvule bvcmp wfl_of_type_bitvec_is_bitvec

theorem pe_bvsaddo_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsaddo t₁ t₂) = true
:= by show_pe_binary_wfl bvsaddo bvso wfl_of_type_bitvec_is_bitvec

theorem pe_bvssubo_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvssubo t₁ t₂) = true
:= by show_pe_binary_wfl bvssubo bvso wfl_of_type_bitvec_is_bitvec

theorem pe_bvsmulo_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsmulo t₁ t₂) = true
:= by show_pe_binary_wfl bvsmulo bvso wfl_of_type_bitvec_is_bitvec

theorem pe_bvadd {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvadd
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.add bv₁ bv₂))
:= by simp only [bvadd, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvsub {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsub
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.sub bv₁ bv₂))
:= by simp only [bvsub, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvmul {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvmul
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.mul bv₁ bv₂))
:= by simp only [bvmul, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvsdiv {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsdiv
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.smtSDiv bv₁ bv₂))
:= by simp only [bvsdiv, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvudiv {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvudiv
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.smtUDiv bv₁ bv₂))
:= by simp only [bvudiv, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvsrem {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsrem
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.srem bv₁ bv₂))
:= by simp only [bvsrem, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvsmod {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsmod
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.smod bv₁ bv₂))
:= by simp only [bvsmod, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvumod {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvumod
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (BitVec.umod bv₁ bv₂))
:= by simp only [bvumod, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvlshr {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvlshr
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (bv₁ >>> bv₂))
:= by simp only [bvlshr, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvshl {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvshl
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bitvec (bv₁ <<< bv₂))
:= by simp only [bvshl, bvapp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvsaddo {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsaddo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bool (BitVec.overflows n (bv₁.toInt + bv₂.toInt)))
:= by simp only [bvsaddo, bvso]

theorem pe_bvssubo {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvssubo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bool (BitVec.overflows n (bv₁.toInt - bv₂.toInt)))
:= by simp only [bvssubo, bvso]

theorem pe_bvsmulo {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsmulo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bool (BitVec.overflows n (bv₁.toInt * bv₂.toInt)))
:= by simp only [bvsmulo, bvso]

theorem pe_zero_extend {k n : Nat} {bv : BitVec k} :
  k ≤ n →
  Factory.zero_extend (n - k) bv =
  Term.prim (TermPrim.bitvec (BitVec.zeroExtend n bv))
:= by
  intro h₁
  have h₂ : (n - k) + k = n := by omega
  simp only [zero_extend, Term.prim.injEq, TermPrim.bitvec.injEq, h₂, true_and]
  rw [h₂]

theorem pe_bvslt {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvslt
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bool (BitVec.slt bv₁ bv₂))
:= by simp only [bvslt, bvcmp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvsle {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsle
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bool (BitVec.sle bv₁ bv₂))
:= by simp only [bvsle, bvcmp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvule {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvule
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  Term.prim (TermPrim.bool (BitVec.ule bv₁ bv₂))
:= by simp only [bvule, bvcmp, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem pe_bvaddChecked_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvaddChecked t₁ t₂) = true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨bv₁, ht₁⟩ := wfl_of_type_bitvec_is_bitvec h₁ h₂
  have ⟨bv₂, ht₂⟩ := wfl_of_type_bitvec_is_bitvec h₃ h₄
  subst ht₁ ht₂
  have h := @pe_bvsaddo _ bv₁ bv₂
  cases h' : BitVec.overflows n (bv₁.toInt + bv₂.toInt)
  case false =>
    simp only [bvaddChecked, h, h', pe_ifFalse_false, pe_bvadd, Term.isLiteral]
  case true =>
    simp only [bvaddChecked, h, h', pe_ifFalse_true, Term.isLiteral]

theorem pe_bvsubChecked_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvsubChecked t₁ t₂) = true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨bv₁, ht₁⟩ := wfl_of_type_bitvec_is_bitvec h₁ h₂
  have ⟨bv₂, ht₂⟩ := wfl_of_type_bitvec_is_bitvec h₃ h₄
  subst ht₁ ht₂
  have h := @pe_bvssubo _ bv₁ bv₂
  cases h' : BitVec.overflows n (bv₁.toInt - bv₂.toInt)
  case false =>
    simp only [bvsubChecked, h, h', pe_ifFalse_false, pe_bvsub, Term.isLiteral]
  case true =>
    simp only [bvsubChecked, h, h', pe_ifFalse_true, Term.isLiteral]

theorem pe_bvmulChecked_wfl {εs : SymEntities} {t₁ t₂ : Term} {n : Nat} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.bitvec n →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.bitvec n →
  Term.isLiteral (Factory.bvmulChecked t₁ t₂) = true
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨bv₁, ht₁⟩ := wfl_of_type_bitvec_is_bitvec h₁ h₂
  have ⟨bv₂, ht₂⟩ := wfl_of_type_bitvec_is_bitvec h₃ h₄
  subst ht₁ ht₂
  have h := @pe_bvsmulo _ bv₁ bv₂
  cases h' : BitVec.overflows n (bv₁.toInt * bv₂.toInt)
  case false =>
    simp only [bvmulChecked, h, h', pe_ifFalse_false, pe_bvmul, Term.isLiteral]
  case true =>
    simp only [bvmulChecked, h, h', pe_ifFalse_true, Term.isLiteral]

theorem pe_bvaddChecked_overflow {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsaddo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  (Term.prim (TermPrim.bool true)) ->
  Factory.bvaddChecked
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  .none (.prim (.bitvec n))
:= by intro h; simp only [bvaddChecked, h, pe_ifFalse_true, pe_bvadd, typeOf_bv]

theorem pe_bvaddChecked_no_overflow {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsaddo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  (Term.prim (TermPrim.bool false)) ->
  Factory.bvaddChecked
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  .some (Term.prim (TermPrim.bitvec (BitVec.add bv₁ bv₂)))
:= by intro h; simp only [bvaddChecked, h, pe_ifFalse_false, pe_bvadd]

theorem pe_bvsubChecked_overflow {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvssubo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  (Term.prim (TermPrim.bool true)) ->
  Factory.bvsubChecked
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  .none (.prim (.bitvec n))
:= by intro h; simp only [bvsubChecked, h, pe_ifFalse_true, pe_bvsub, typeOf_bv]

theorem pe_bvsubChecked_no_overflow {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvssubo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  (Term.prim (TermPrim.bool false)) ->
  Factory.bvsubChecked
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  .some (Term.prim (TermPrim.bitvec (BitVec.sub bv₁ bv₂)))
:= by intro h; simp only [bvsubChecked, h, pe_ifFalse_false, pe_bvsub]

theorem pe_bvmulChecked_overflow {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsmulo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  (Term.prim (TermPrim.bool true)) ->
  Factory.bvmulChecked
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  .none (.prim (.bitvec n))
:= by intro h; simp only [bvmulChecked, h, pe_ifFalse_true, pe_bvmul, typeOf_bv]

theorem pe_bvmulChecked_no_overflow {n : Nat} {bv₁ bv₂ : BitVec n} :
  Factory.bvsmulo
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  (Term.prim (TermPrim.bool false)) ->
  Factory.bvmulChecked
    (Term.prim (TermPrim.bitvec bv₁))
    (Term.prim (TermPrim.bitvec bv₂)) =
  .some (Term.prim (TermPrim.bitvec (BitVec.mul bv₁ bv₂)))
:= by intro h; simp only [bvmulChecked, h, pe_ifFalse_false, pe_bvmul]

/-! ### PE for Factory string, set, and record operators -/

theorem pe_string_like_wfl {εs : SymEntities} {t : Term} {p : Pattern} :
  t.WellFormedLiteral εs → t.typeOf = .string →
  (Factory.string.like t p).isLiteral
:= by show_pe_unary_wfl string.like wfl_of_type_string_is_string

theorem pe_set_isEmpty {s : Set Term} {ty : TermType} :
  Factory.set.isEmpty (Term.set s ty) = s.isEmpty
:= by
  cases s ; rename_i ts
  cases ts
  case nil =>
    simp only [set.isEmpty, Set.isEmpty, Set.empty, beq_self_eq_true]
  case cons =>
    simp only [set.isEmpty, Set.isEmpty, Set.empty, Term.prim.injEq, TermPrim.bool.injEq,
      Bool.false_eq, beq_eq_false_iff_ne, ne_eq, Set.mk.injEq, reduceCtorEq, not_false_eq_true]

theorem pe_set_member {t : Term} {s : Set Term} {ty : TermType} :
  (Term.set s ty).isLiteral →
  t.isLiteral →
  (Factory.set.member t (Term.set s ty)) = s.contains t
:= by
  intro h₁ h₂
  simp only [set.member]
  split
  case h_1 heq =>
    simp only [Term.set.injEq] at heq
    replace ⟨heq, _⟩ := heq
    subst heq
    simp only [Set.contains, Set.elts, List.elem_eq_mem, List.not_mem_nil, decide_false]
  case h_2 heq =>
    simp only [Term.set.injEq] at heq
    replace ⟨heq, _⟩ := heq
    subst heq
    simp only [h₂, h₁, Bool.and_self, ↓reduceIte]
  case h_3 h =>
    specialize h s ty
    simp only [forall_const] at h

theorem pe_set_member_wfl {εs : SymEntities} {t₁ t₂ : Term} {ty : TermType} :
  Term.WellFormedLiteral εs t₁ →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.set ty →
  (Factory.set.member t₁ t₂).isLiteral
:= by
  intro h₁ h₃ h₄
  have ⟨s₂, ht₂⟩ := wfl_of_type_set_is_set h₃ h₄
  subst ht₂
  simp only [set.member]
  split
  case h_1 => simp only [Term.isLiteral]
  case h_2 =>
    simp only [h₁.right, h₃.right, Bool.and_self, ite_true, Term.isLiteral]
  case h_3 h =>
    specialize h s₂ ty
    simp only [forall_const] at h

theorem pe_set_subset {s₁ s₂ : Set Term} {ty : TermType} :
  (Term.set s₁ ty).isLiteral →
  (Term.set s₂ ty).isLiteral →
  (Factory.set.subset (Term.set s₁ ty) (Term.set s₂ ty)) = s₁.subset s₂
:= by
  intro h₁ h₂
  simp only [set.subset, Term.set.injEq, and_true, Bool.and_eq_true]
  split
  case isTrue h =>
    subst h
    have h := (@Set.subset_iff_subset_elts _ _ s₁ s₁).mpr (List.Subset.refl (s₁.elts))
    simp only [Subset] at h
    simp only [h]
  case isFalse =>
    split
    case h_1 h =>
      simp only [Term.set.injEq] at h
      simp only [Set.subset, Set.elts, h, List.all_nil]
    case h_2 heq₁ heq₂ =>
      simp only [Term.set.injEq] at heq₁ heq₂
      simp only [h₁, h₂, and_self, ↓reduceIte, ← heq₁.left, ← heq₂.left]
    case h_3 h =>
      specialize h s₁ ty s₂ ty
      simp only [forall_const] at h

theorem pe_set_subset_wfl {εs : SymEntities} {t₁ t₂ : Term} {ty : TermType} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.set ty →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.set ty →
  (Factory.set.subset t₁ t₂).isLiteral
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨s₁, ht₁⟩ := wfl_of_type_set_is_set h₁ h₂
  have ⟨s₂, ht₂⟩ := wfl_of_type_set_is_set h₃ h₄
  subst ht₁ ht₂
  simp only [set.subset, Term.set.injEq, and_true, Bool.and_eq_true]
  split
  case isTrue => simp only [Term.isLiteral]
  case isFalse =>
    split
    case h_1 => simp only [Term.isLiteral]
    case h_2 =>
      simp only [h₁.right, h₃.right, Term.isLiteral, and_self, ite_true]
    case h_3 h =>
      specialize h s₁ ty s₂ ty
      simp only [forall_const] at h

theorem pe_set_inter_wfl {εs : SymEntities} {t₁ t₂ : Term} {ty : TermType} :
  Term.WellFormedLiteral εs t₁ → Term.typeOf t₁ = TermType.set ty →
  Term.WellFormedLiteral εs t₂ → Term.typeOf t₂ = TermType.set ty →
  (Factory.set.inter t₁ t₂).isLiteral
:= by
  intro h₁ h₂ h₃ h₄
  have ⟨s₁, ht₁⟩ := wfl_of_type_set_is_set h₁ h₂
  have ⟨s₂, ht₂⟩ := wfl_of_type_set_is_set h₃ h₄
  subst ht₁ ht₂
  simp only [set.inter, Term.set.injEq, and_true, Bool.and_eq_true]
  split
  case isTrue => simp only [h₁.right]
  case isFalse =>
    split
    case h_1 => simp only [h₁.right]
    case h_2 => simp only [h₃.right]
    case h_3 h₅ h₆ =>
      simp only [Term.set.injEq] at h₅ h₆
      simp [←h₅, ←h₆, h₁.right, h₃.right]
      unfold Term.isLiteral
      simp [List.attach_def, List.all_pmap_subtype Term.isLiteral]
      intro t h₇
      replace h₇ : t ∈ s₁ ∩ s₂ := by
        simp only [Inter.inter]
        rw [← Set.in_list_iff_in_set]
        simp only [Set.elts, h₇]
      rw [Set.mem_inter_iff] at h₇
      apply lit_term_set_implies_lit_elt h₃.right h₇.right
    case h_4 h =>
      specialize h s₁ ty s₂ ty
      simp only [forall_const] at h

theorem pe_set_inter {s₁ s₂ : Set Term} {ty : TermType} :
  (Term.set s₁ ty).isLiteral →
  (Term.set s₂ ty).isLiteral →
  (Factory.set.inter (Term.set s₁ ty) (Term.set s₂ ty)) = Term.set (Set.intersect s₁ s₂) ty
:= by
  intro h₁ h₂
  simp only [set.inter]
  split
  case isTrue h₃ =>
    have h₄ := Set.inter_self_eq s₂
    simp only [Inter.inter] at h₄
    simp only [Term.set.injEq, and_true] at h₃
    simp only [h₃, h₄]
  case isFalse =>
    split
    case h_1 heq | h_2 heq _ =>
      simp only [Term.set.injEq, ← Set.empty_eq_mk_empty] at heq
      simp only [heq, ← Set.inter_def, Set.inter_empty_left, Set.inter_empty_right]
    case h_3 heq₁ heq₂ =>
      simp only [Term.set.injEq] at heq₁ heq₂
      simp only [h₁, h₂, Bool.and_self, ↓reduceIte, Term.set.injEq]
      simp only [heq₁, heq₂, and_self]
    case h_4 h =>
      specialize h s₁ ty s₂ ty
      simp only [forall_const] at h

theorem pe_set_intersects {s₁ s₂ : Set Term} {ty : TermType} :
  (Term.set s₁ ty).isLiteral →
  (Term.set s₂ ty).isLiteral →
  (Factory.set.intersects (Term.set s₁ ty) (Term.set s₂ ty)) = s₁.intersects s₂
:= by
  intro h₁ h₂
  simp only [set.intersects, pe_set_inter h₁ h₂, set.isEmpty]
  split
  case h_1 h₃ =>
    simp only [Term.set.injEq] at h₃
    simp only [pe_not_true, Term.prim.injEq, TermPrim.bool.injEq]
    by_contra hc
    rw [eq_comm, Bool.not_eq_false, Set.intersects_def] at hc
    simp only [Set.isEmpty, Inter.inter, Set.empty, beq_iff_eq] at hc
    simp only [h₃.left, not_true_eq_false] at hc
  case h_2 h₃ =>
    simp only [Term.set.injEq] at h₃
    simp only [pe_not_false, Term.prim.injEq, TermPrim.bool.injEq]
    rw [eq_comm, Set.intersects_def]
    simp only [Set.isEmpty, Inter.inter, h₃.left, Set.empty, beq_iff_eq, Set.mk.injEq, reduceCtorEq,
      not_false_eq_true]
  case h_3 h₃ h₄ =>
    cases h₅ : (Set.intersect s₁ s₂).1
    case nil =>
      specialize h₃ ty
      simp only [← h₅, forall_const] at h₃
    case cons hd tl =>
      specialize h₄ hd tl ty
      simp only [← h₅, forall_const] at h₄

theorem pe_record_get_wfl {εs : SymEntities} {a : Attr} {t : Term} {ty : TermType} {rty:  Map Attr TermType} :
  Term.WellFormedLiteral εs t →
  Term.typeOf t = TermType.record rty →
  Map.find? rty a = some ty →
  Term.isLiteral (record.get t a) = true
:= by
  intro h₁ h₂ h₃
  have ⟨r, h₄⟩ := wfl_of_type_record_is_record h₁ h₂
  subst h₄
  have ⟨t', h₄⟩ := typeOf_term_record_attr_value h₂ h₃
  have h₅ := Map.find?_mem_toList h₄.left
  simp only [record.get, h₄.left]
  exact lit_term_record_implies_lit_value h₁.right h₅

theorem pe_record_get {rt : Map Attr Term} {a : Attr} {tₐ : Term} :
  Map.find? rt a = some tₐ →
  record.get (Term.record rt) a = tₐ
:= by
  intro h
  simp only [record.get, h]

/-! ### PE for Factory extension operators -/

theorem pe_ext_decimal_val_wfl {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs → t.typeOf = .ext .decimal →
  (Factory.ext.decimal.val t).isLiteral
:= by show_pe_unary_wfl ext.decimal.val wfl_of_type_ext_decimal_is_ext_decimal

theorem pe_ext_ipaddr_isV4_wfl {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs → t.typeOf = .ext .ipAddr →
  (Factory.ext.ipaddr.isV4 t).isLiteral
:= by show_pe_unary_wfl ext.ipaddr.isV4 wfl_of_type_ext_ipaddr_is_ext_ipaddr

theorem pe_ext_ipaddr_addrV4'_wfl {εs : SymEntities} {I : Interpretation} {t : Term} :
  I.WellFormed εs → t.WellFormedLiteral εs → t.typeOf = .ext .ipAddr →
  (Factory.ext.ipaddr.addrV4' I t).isLiteral
:= by
  intro h₀ h₁ h₂
  have ⟨ip, h₃⟩ := wfl_of_type_ext_ipaddr_is_ext_ipaddr h₁ h₂
  subst h₃
  simp only [ext.ipaddr.addrV4']
  cases ip <;> simp only
  case V4 =>
    simp only [ext.ipaddr.addrV4, Term.isLiteral]
  case V6 c6 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_addrV4 c6.addr c6.pre h₀ rfl
    exact h₃.left.right

theorem pe_ext_ipaddr_prefixV4'_wfl {εs : SymEntities} {I : Interpretation} {t : Term} :
  I.WellFormed εs → t.WellFormedLiteral εs → t.typeOf = .ext .ipAddr →
  (Factory.ext.ipaddr.prefixV4' I t).isLiteral
:= by
  intro h₀ h₁ h₂
  have ⟨ip, h₃⟩ := wfl_of_type_ext_ipaddr_is_ext_ipaddr h₁ h₂
  subst h₃
  simp only [ext.ipaddr.prefixV4']
  cases ip <;> simp only
  case V4 =>
    simp only [ext.ipaddr.prefixV4]
    split <;>
    simp only [noneOf, someOf, Term.isLiteral]
  case V6 c6 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_prefixV4 c6.addr c6.pre h₀ rfl
    exact h₃.left.right

theorem pe_ext_ipaddr_addrV6'_wfl {εs : SymEntities} {I : Interpretation} {t : Term} :
  I.WellFormed εs → t.WellFormedLiteral εs → t.typeOf = .ext .ipAddr →
  (Factory.ext.ipaddr.addrV6' I t).isLiteral
:= by
  intro h₀ h₁ h₂
  have ⟨ip, h₃⟩ := wfl_of_type_ext_ipaddr_is_ext_ipaddr h₁ h₂
  subst h₃
  simp only [ext.ipaddr.addrV6']
  cases ip <;> simp only
  case V4 c4 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_addrV6 c4.addr c4.pre h₀ rfl
    exact h₃.left.right
  case V6 =>
    simp only [ext.ipaddr.addrV6, Term.isLiteral]

theorem pe_ext_ipaddr_prefixV6'_wfl {εs : SymEntities} {I : Interpretation} {t : Term} :
  I.WellFormed εs → t.WellFormedLiteral εs → t.typeOf = .ext .ipAddr →
  (Factory.ext.ipaddr.prefixV6' I t).isLiteral
:= by
  intro h₀ h₁ h₂
  have ⟨ip, h₃⟩ := wfl_of_type_ext_ipaddr_is_ext_ipaddr h₁ h₂
  subst h₃
  simp only [ext.ipaddr.prefixV6']
  cases ip <;> simp only
  case V4 c4 =>
    have h₃ := wf_interpretation_implies_wfp_ext_ipaddr_prefixV6 c4.addr c4.pre h₀ rfl
    exact h₃.left.right
  case V6 =>
    simp only [ext.ipaddr.prefixV6]
    split <;>
    simp only [noneOf, someOf, Term.isLiteral]

theorem pe_ext_datetime_val_wfl {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs → t.typeOf = .ext .datetime →
  (Factory.ext.datetime.val t).isLiteral
:= by show_pe_unary_wfl ext.datetime.val wfl_of_type_ext_datetime_is_ext_datetime

theorem pe_ext_datetime_ofBitVec_wfl {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs → t.typeOf = .prim (.bitvec 64) →
  (Factory.ext.datetime.ofBitVec t).isLiteral
:= by show_pe_unary_wfl ext.datetime.ofBitVec wfl_of_type_bitvec_is_bitvec

theorem pe_ext_duration_val_wfl {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs → t.typeOf = .ext .duration →
  (Factory.ext.duration.val t).isLiteral
:= by show_pe_unary_wfl ext.duration.val wfl_of_type_ext_duration_is_ext_duration

theorem pe_ext_duration_ofBitVec_wfl {εs : SymEntities} {t : Term} :
  t.WellFormedLiteral εs → t.typeOf = .prim (.bitvec 64) →
  (Factory.ext.duration.ofBitVec t).isLiteral
:= by show_pe_unary_wfl ext.duration.ofBitVec wfl_of_type_bitvec_is_bitvec

theorem pe_ext_decimal_val {d : Ext.Decimal} :
  ext.decimal.val (Term.prim (TermPrim.ext (Ext.decimal d))) =
  Term.prim (.bitvec d.toBitVec)
:= by simp only [ext.decimal.val]

theorem pe_ext_ipaddr_isV4_V4 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  Factory.ext.ipaddr.isV4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) = true
:= by
  simp only [ext.ipaddr.isV4, Ext.IPAddr.IPNet.isV4]

theorem pe_ext_ipaddr_isV4_V6 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  Factory.ext.ipaddr.isV4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) = false
:= by
  simp only [ext.ipaddr.isV4, Ext.IPAddr.IPNet.isV4]

theorem pe_ext_ipaddr_addrV4_V4 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  Factory.ext.ipaddr.addrV4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) = cidr.addr
:= by
  simp only [ext.ipaddr.addrV4]

theorem pe_ext_ipaddr_addrV4'_V4 {I : Interpretation} {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  Factory.ext.ipaddr.addrV4' I (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) =
  Factory.ext.ipaddr.addrV4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr))))
:= by
  simp only [ext.ipaddr.addrV4']

def cidrPrefixTerm {w} (cidr : Ext.IPAddr.CIDR w) : Term :=
  match cidr.pre with
  | none => Term.none (TermType.bitvec w)
  | some pre => Term.some (Term.prim (TermPrim.bitvec pre))

theorem pe_ext_ipaddr_prefixV4_V4 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  Factory.ext.ipaddr.prefixV4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) =
  cidrPrefixTerm cidr
:= by
  simp only [Factory.ext.ipaddr.prefixV4, noneOf, someOf, cidrPrefixTerm]
  split <;> rename_i heq <;> simp only [heq]

theorem pe_ext_ipaddr_prefixV4'_V4 {I : Interpretation} {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH} :
  Factory.ext.ipaddr.prefixV4' I (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr)))) =
  Factory.ext.ipaddr.prefixV4 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V4 cidr))))
:= by
  simp only [ext.ipaddr.prefixV4']

theorem pe_ext_ipaddr_addrV6_V6 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  Factory.ext.ipaddr.addrV6 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) = cidr.addr
:= by
  simp only [ext.ipaddr.addrV6]

theorem pe_ext_ipaddr_addrV6'_V6 {I : Interpretation} {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  Factory.ext.ipaddr.addrV6' I (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) =
  Factory.ext.ipaddr.addrV6 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr))))
:= by
  simp only [ext.ipaddr.addrV6']

theorem pe_ext_ipaddr_prefixV6_V6 {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  Factory.ext.ipaddr.prefixV6 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) =
  cidrPrefixTerm cidr
:= by
  simp only [Factory.ext.ipaddr.prefixV6, noneOf, someOf, cidrPrefixTerm]
  split <;> rename_i heq <;> simp only [heq]

theorem pe_ext_ipaddr_prefixV6'_V6 {I : Interpretation} {cidr : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH} :
  Factory.ext.ipaddr.prefixV6' I (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr)))) =
  Factory.ext.ipaddr.prefixV6 (Term.prim (TermPrim.ext (Ext.ipaddr (Ext.IPAddr.IPNet.V6 cidr))))
:= by
  simp only [Factory.ext.ipaddr.prefixV6']

theorem pe_ext_datetime_val {d : Ext.Datetime} :
  ext.datetime.val (Term.prim (TermPrim.ext (Ext.datetime d))) =
    Term.prim (.bitvec d.val.toBitVec)
:= by simp only [ext.datetime.val]

theorem pe_ext_datetime_ofBitVec {bv : BitVec 64} :
  ext.datetime.ofBitVec (Term.prim (TermPrim.bitvec bv)) =
  Term.prim (TermPrim.ext (Ext.datetime ( Int64.ofInt bv.toInt)))
:= by simp only [ext.datetime.ofBitVec]

theorem pe_ext_duration_val {d : Ext.Datetime.Duration} :
  ext.duration.val (Term.prim (TermPrim.ext (Ext.duration d))) =
    Term.prim (.bitvec d.val.toBitVec)
:= by simp only [ext.duration.val]

theorem pe_ext_duration_ofBitVec {bv : BitVec 64} :
  ext.duration.ofBitVec (Term.prim (TermPrim.bitvec bv)) =
  Term.prim (TermPrim.ext (Ext.duration ( Int64.ofInt bv.toInt)))
:= by simp only [ext.duration.ofBitVec]


end Cedar.Thm
