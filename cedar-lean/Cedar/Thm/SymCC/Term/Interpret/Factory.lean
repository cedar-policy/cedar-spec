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

import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Term.Interpret.Basic
import Cedar.Thm.SymCC.Term.Interpret.Lit
import Cedar.Thm.SymCC.Term.PE
import Cedar.Thm.SymCC.Term.TypeOf
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Interpretation

/-!
# Interpretation of Factory functions

This file basic lemmas about the interpretation of Factory functions.
--/


namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem interpret_not {I : Interpretation} {t : Term} :
  I.WellFormed εs → t.WellFormed εs →
  (Factory.not t).interpret I = Factory.not (t.interpret I)
:= by
  intro h₁ h₂
  rw [Factory.not.eq_def]
  split
  case h_1 b =>
    cases b <;>
    simp only [interpret_term_prim, pe_not_true, pe_not_false,
      Bool.not_true, Bool.not_false]
  case h_2 t ty =>
    simp only [interpret_term_app_not]
    replace ⟨h₂, h₃⟩ := (wf_term_app_not_exact h₂).right
    replace h₂ := interpret_term_wfl h₁ h₂
    simp only [h₃] at h₂
    replace h₂ := wfl_of_type_bool_is_true_or_false h₂.left h₂.right
    rcases h₂ with h₂ | h₂ <;>
    simp only [h₂, pe_not_true, pe_not_false]
  case h_3 =>
    simp only [interpret_term_app_not]

theorem interpret_opposites_neq {I : Interpretation} {t₁ t₂ : Term} {b₁ b₂ : Bool} :
  t₁.interpret I = b₁ → t₂.interpret I = b₂ →
  opposites t₁ t₂ → ¬ b₁ = b₂
:= by
  intro h₁ h₂ h₃
  simp only [opposites] at h₃
  by_contra h
  subst h
  split at h₃ <;>
  simp only [decide_eq_true_eq, Bool.false_eq_true] at h₃
  case h_1 =>
    subst h₃
    cases b₁ <;>
    simp only [interpret_term_app_not, h₁, pe_not_true, pe_not_false, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true, Bool.true_eq_false] at h₂
  case h_2 =>
    rw [eq_comm] at h₃ ; subst h₃
    cases b₁ <;>
    simp only [interpret_term_app_not, h₂, pe_not_true, pe_not_false, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true, Bool.true_eq_false] at h₁


theorem interpret_and {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs →
  t₁.typeOf = .bool → t₂.typeOf = .bool →
  (Factory.and t₁ t₂).interpret I = Factory.and (t₁.interpret I) (t₂.interpret I)
:= by
  intro hI hw₁ hw₂ hty₁ hty₂
  simp only [Factory.and, Bool.or_eq_true, decide_eq_true_eq]
  split
  case isTrue hor =>
    rcases hor with hor | hor <;> subst hor <;>
    simp only [interpret_term_prim, ↓reduceIte, true_or, or_true]
  case isFalse =>
    split
    case isTrue heq =>
      subst heq
      simp only [interpret_term_prim, ↓reduceIte]
      split <;> try rfl
      rename_i heq
      rw [eq_comm] at heq
      simp only [or_self] at heq
      exact heq
    case isFalse =>
      split
      case isTrue hor =>
        simp only [interpret_term_prim]
        rcases hor with hor | hor
        case inl =>
          rcases hor with hor | hor <;> subst hor <;>
          simp [interpret_term_prim, Term.prim.injEq, TermPrim.bool.injEq, or_false, or_true,
            true_or, ↓reduceIte, ite_self, Bool.false_eq_true]
          split <;> try rfl
          rw [eq_comm]
          assumption
        case inr =>
          have hb₁ := interpret_term_wfl hI hw₁
          have hb₂ := interpret_term_wfl hI hw₂
          rw [hty₁] at hb₁ ; rw [hty₂] at hb₂
          replace ⟨b₁, hb₁⟩ := wfl_of_type_bool_is_bool hb₁.left hb₁.right
          replace ⟨b₂, hb₂⟩ := wfl_of_type_bool_is_bool hb₂.left hb₂.right
          replace hor := interpret_opposites_neq hb₁ hb₂ hor
          simp only [hb₁, hb₂, Term.prim.injEq, TermPrim.bool.injEq, hor, false_or]
          cases b₂ <;>
          simp only [↓reduceIte, or_true, true_or, ite_self, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true]
          simp only [Bool.not_eq_true] at hor
          simp only [hor]
      case isFalse =>
        simp only [interpret_term_app_and, Factory.and, Bool.or_eq_true, decide_eq_true_eq]

theorem interpret_or {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs →
  t₁.typeOf = .bool → t₂.typeOf = .bool →
  (Factory.or t₁ t₂).interpret I = Factory.or (t₁.interpret I) (t₂.interpret I)
:= by
  intro hI hw₁ hw₂ hty₁ hty₂
  simp only [Factory.or, Bool.or_eq_true, decide_eq_true_eq]
  split
  case isTrue heq =>
    rcases heq with heq | heq <;>
    simp [heq, interpret_term_prim, true_or, or_true, ite_true]
  case isFalse =>
    split
    case isTrue heq =>
      simp only [heq, interpret_term_prim, ite_true]
      split
      case isTrue h => rcases h with h | h <;> simp only [h]
      case isFalse  => rfl
    case isFalse =>
      split
      case isTrue heq =>
        simp only [interpret_term_prim]
        rcases heq with heq | heq
        case inl =>
          rcases heq with heq | heq
          case inl =>
            simp only [heq, interpret_term_prim, Term.prim.injEq, TermPrim.bool.injEq,
              Bool.true_eq_false, ↓reduceIte, true_or, ite_self]
          case inr =>
            simp only [heq, interpret_term_prim, Term.prim.injEq, TermPrim.bool.injEq,
              Bool.true_eq_false, or_false, or_true, true_or, ↓reduceIte, ite_self]
            split
            case isTrue h => simp only [h]
            case isFalse  => rfl
        case inr =>
          have hb₁ := interpret_term_wfl hI hw₁
          have hb₂ := interpret_term_wfl hI hw₂
          simp only [hty₁, hty₂] at hb₁ hb₂
          replace ⟨b₁, hb₁⟩ := wfl_of_type_bool_is_bool hb₁.left hb₁.right
          replace ⟨b₂, hb₂⟩ := wfl_of_type_bool_is_bool hb₂.left hb₂.right
          simp only [hb₁, hb₂, Term.prim.injEq, TermPrim.bool.injEq]
          replace heq := interpret_opposites_neq hb₁ hb₂ heq
          cases b₁ <;> cases b₂ <;>
          simp only [heq, Bool.false_eq_true, Bool.true_eq_false, or_self, or_true, ite_true, ite_false]
      case isFalse =>
        simp only [interpret_term_app_or, Factory.or, Bool.or_eq_true, decide_eq_true_eq]


theorem interpret_ite_simplify {εs : SymEntities} {I : Interpretation} {t₁ t₂ t₃ : Term} :
  I.WellFormed εs → t₁.WellFormed εs →
  t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .bool → t₂.typeOf = t₃.typeOf →
  (Factory.ite.simplify t₁ t₂ t₃).interpret I =
  Factory.ite.simplify (t₁.interpret I) (t₂.interpret I) (t₃.interpret I)
:= by
  intro hI hw₁ hw₂ hw₃ hty₁ hty
  rw [Factory.ite.simplify.eq_def]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  split
  case isTrue h₃ =>
    cases h₃ <;> rename_i h₃ <;> subst h₃
    · simp [interpret_term_prim, pe_ite_simplify_true]
    · simp [ite.simplify]
  case isFalse =>
    split
    case isTrue h₃ =>
      subst h₃
      simp [interpret_term_prim, pe_ite_simplify_false]
    case isFalse =>
      have h₃ := interpret_term_wfl hI hw₁
      simp only [hty₁] at h₃
      replace h₃ := wfl_of_type_bool_is_true_or_false h₃.left h₃.right
      split
      · cases h₃ <;> rename_i h₃ <;>
        simp only [h₃, interpret_term_prim,
          pe_ite_simplify_true, pe_ite_simplify_false]
      · simp only [interpret_not hI hw₁]
        cases h₃ <;> rename_i h₃ <;>
        simp only [h₃, interpret_term_prim,
          pe_not_true, pe_ite_simplify_true,
          pe_not_false, pe_ite_simplify_false]
      · rw [typeOf_bool] at hty
        rw [interpret_and hI hw₁ hw₂ hty₁ hty]
        cases h₃ <;> rename_i h₃ <;>
        simp only [h₃, pe_ite_simplify_true, pe_ite_simplify_false,
          pe_and_true_left, pe_and_false_left, interpret_term_prim]
      · rw [typeOf_bool, eq_comm] at hty
        rw [interpret_or hI hw₁ hw₃ hty₁ hty]
        cases h₃ <;> rename_i h₃ <;>
        simp only [h₃, pe_ite_simplify_true, pe_ite_simplify_false,
          pe_or_true_left, pe_or_false_left, interpret_term_prim]
      · simp only [interpret_term_app_ite]
        cases h₃ <;> rename_i h₃ <;>
        simp only [h₃, pe_ite_true, pe_ite_false,
          pe_ite_simplify_true, pe_ite_simplify_false]

theorem interpret_ite {εs : SymEntities} {I : Interpretation} {t₁ t₂ t₃ : Term} :
  I.WellFormed εs → t₁.WellFormed εs →
  t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .bool → t₂.typeOf = t₃.typeOf →
  (Factory.ite t₁ t₂ t₃).interpret I =
  Factory.ite (t₁.interpret I) (t₂.interpret I) (t₃.interpret I)
:= by
  intro hI hw₁ hw₂ hw₃ hty₁ hty
  simp only [Factory.ite.eq_def]
  have hlit := interpret_term_wfl hI hw₁
  simp only [hty₁] at hlit
  replace hlit := wfl_of_type_bool_is_true_or_false hlit.left hlit.right
  split <;> split <;>
  simp only [interpret_term_some, interpret_ite_simplify hI hw₁ hw₂ hw₃ hty₁ hty]
  · simp only [typeOf_term_some, TermType.option.injEq] at hty
    rw [interpret_ite_simplify hI hw₁ (wf_term_some_implies hw₂) (wf_term_some_implies hw₃) hty₁ hty]
    rename_i h₁ h₂
    simp only [interpret_term_some, Term.some.injEq] at h₁ h₂
    simp only [h₁, h₂]
  · simp only [typeOf_term_some, TermType.option.injEq] at hty
    rw [interpret_ite_simplify hI hw₁ (wf_term_some_implies hw₂) (wf_term_some_implies hw₃) hty₁ hty]
    cases hlit <;> rename_i hlit <;>
    simp only [hlit, pe_ite_simplify_true, pe_ite_simplify_false]
  · rename_i h₁ h₂
    simp only [h₁, h₂]
    cases hlit <;> rename_i hlit <;>
    simp only [hlit, pe_ite_simplify_true, pe_ite_simplify_false]

theorem interpret_implies {I : Interpretation} {t₁ t₂ : Term} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs →
  t₁.typeOf = .bool → t₂.typeOf = .bool →
  (Factory.implies t₁ t₂).interpret I = Factory.implies (t₁.interpret I) (t₂.interpret I)
:= by
  intro hI hwt₁ hwt₂ hty₁ hty₂
  have hwt₃ := wf_not hwt₁ hty₁
  simp only [implies, interpret_or hI hwt₃.left hwt₂ hwt₃.right hty₂, interpret_not hI hwt₁]

theorem interpret_eq_simplify {I : Interpretation} {t₁ t₂ : Term} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs →
  (Factory.eq.simplify t₁ t₂).interpret I = Factory.eq.simplify (t₁.interpret I) (t₂.interpret I)
:= by
  cases t₁, t₂ using Factory.eq.simplify.fun_cases
  <;> simp_all only [Factory.eq.simplify, interpret_term_prim, reduceIte, forall_self_imp,
    Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq, implies_true, true_and]
  case case2 =>
    split <;> rename_i h₁ h₂ h₃ <;> intro h₄ h₅ h₆
    · rw [interpret_term_lit_id I (And.intro h₅ h₂.left)] at h₃
      rw [interpret_term_lit_id I (And.intro h₆ h₂.right)] at h₃
      contradiction
    · have h₇ := interpret_term_wfl h₄ h₅
      have h₈ := interpret_term_wfl h₄ h₆
      simp_all [Term.WellFormedLiteral]
  case case3 =>
    rename_i h₁ ; replace ⟨h₁', h₁⟩ := h₁ ; subst t₁
    split <;> simp only [typeOf_bool, Term.isLiteral, implies_true, true_and, and_true,
      Term.prim.injEq, TermPrim.bool.injEq, Bool.true_eq_false, and_self, reduceIte]
    · intro h₂ h₃ h₄
      have h₅ := interpret_term_wfl h₂ h₄
      rw [h₁] at h₅
      have h₆ := wfl_of_type_bool_is_true_or_false h₅.left h₅.right
      simp_all only [Term.WellFormedLiteral, Bool.not_eq_true, ite_false, ite_true]
      rcases h₆ with h₆ | h₆
      · symm at h₆ ; contradiction
      · exact h₆
  case case4 =>
    rename_i h₁ ; replace ⟨h₁', h₁⟩ := h₁ ; subst t₂
    split <;> simp_all only [typeOf_bool, Term.isLiteral, Bool.not_eq_true, Bool.true_eq_false,
      Term.prim.injEq, TermPrim.bool.injEq, not_false_eq_true,
      implies_true, true_and, and_true, and_self, ite_false]
    · intro h₂ h₃ h₄
      have h₅ := interpret_term_wfl h₂ h₃
      rw [h₁] at h₅
      have h₆ := wfl_of_type_bool_is_true_or_false h₅.left h₅.right
      simp_all [Term.WellFormedLiteral]
  case case5 =>
    rename_i h₁ ; replace ⟨h₁', h₁⟩ := h₁ ; subst t₁
    intro h₂ h₃ h₄
    split <;> simp_all only [interpret_not h₂ h₄, Bool.not_eq_true, Term.prim.injEq, TermPrim.bool.injEq,
      Bool.false_eq_true, and_true, not_false_eq_true, false_and, ite_false]
    · rename_i h ; simp [← h, Factory.not]
    · have h₅ := interpret_term_wfl h₂ h₄
      rw [h₁] at h₅
      have h₆ := wfl_of_type_bool_is_true_or_false h₅.left h₅.right
      simp_all only [Term.isLiteral, Term.WellFormedLiteral,
        true_and, Bool.not_eq_true, and_self, ite_false, ite_true]
      rcases h₆ with h₆ | h₆
      · simp [h₆, Factory.not]
      · symm at h₆ ; contradiction
  case case6 =>
    rename_i h₁ ; replace ⟨h₁', h₁⟩ := h₁ ; subst t₂
    intro h₂ h₃ h₄
    split <;> simp_all only [interpret_not h₂ h₃, Bool.not_eq_true, Term.prim.injEq, TermPrim.bool.injEq,
      Bool.false_eq_true, and_true, not_false_eq_true, false_and, ite_false]
    · simp [Factory.not]
    · have h₅ := interpret_term_wfl h₂ h₃
      rw [h₁] at h₅
      have h₆ := wfl_of_type_bool_is_true_or_false h₅.left h₅.right
      simp_all [Term.isLiteral, Term.WellFormedLiteral, Factory.not]
  case case7 =>
    intro h₂ h₃ h₄
    have h₅ := interpret_term_wfl h₂ h₃
    have h₆ := interpret_term_wfl h₂ h₄
    simp_all only [Bool.not_eq_true, Term.WellFormedLiteral, interpret_term_app_eq, Factory.eq,
      and_self, ite_true]
    split <;> rename_i h₇ h₈
    <;> simp only [h₇, h₈, Bool.not_eq_true, reduceCtorEq, reduceIte, Term.some.injEq, imp_false] at *
    · simp only [Term.isLiteral] at h₅ h₆
      split <;> rename_i h₉
      · simp [h₉, pe_eq_simplify_same]
      · simp [h₉, pe_eq_simplify_lit h₅.left.right h₆.left.right]
    · split <;> rename_i h₉
      · simp [h₉, pe_eq_simplify_same]
      · simp [h₉, pe_eq_simplify_lit h₅.left.right h₆.left.right]

theorem interpret_eq {I : Interpretation} {t₁ t₂ : Term} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs →
  (Factory.eq t₁ t₂).interpret I = Factory.eq (t₁.interpret I) (t₂.interpret I)
:= by
  intro h₁ h₂ h₃
  cases t₁, t₂ using Factory.eq.fun_cases
  · simp only [Factory.eq, interpret_term_some]
    exact interpret_eq_simplify h₁ (wf_term_some_implies h₂) (wf_term_some_implies h₃)
  · simp [pe_eq_some_none, interpret_term_prim, interpret_term_some, interpret_term_none]
  · simp [pe_eq_none_some, interpret_term_prim, interpret_term_some, interpret_term_none]
  · simp only [Factory.eq]
    rw [interpret_eq_simplify h₁ h₂ h₃]
    have h₄ := interpret_term_wfl h₁ h₂
    have h₅ := interpret_term_wfl h₁ h₃
    split <;> rename_i h₇ h₈ <;> simp only [h₇, h₈, imp_false] at *
    <;> simp only [Term.WellFormedLiteral, Term.isLiteral] at h₄ h₅
    · simp only [pe_eq_simplify_lit h₄.left.right h₅.left.right]
      simp only [Factory.eq.simplify, Term.some.injEq, Bool.and_eq_true, reduceCtorEq,
        decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      split <;> rename_i h₉
      · simp [h₉, pe_eq_simplify_same]
      · simp [h₄, h₅, h₉, Term.isLiteral]
    · simp [h₄, Factory.eq.simplify, Term.isLiteral]
    · rw [(pe_eq_simplify_lit (by simp [Term.isLiteral]) (by simp_all [Term.isLiteral])).right]
      simp

theorem interpret_isNone {I : Interpretation} {t : Term} :
  I.WellFormed εs → t.WellFormed εs →
  (isNone t).interpret I = isNone (t.interpret I)
:= by
  intro h₁ h₂
  rw [isNone.eq_def]
  split
  case h_1 | h_2 =>
    simp only [isNone, interpret_term_none, interpret_term_some, interpret_term_prim]
  case h_3 | h_4 | h_5 =>
    simp [interpret_term_prim, interpret_term_app_ite]
    replace ⟨h₂, h₃⟩ := (wf_term_app_ite_exact h₂).left
    have h₄ := interpret_term_wfl h₁ h₂
    simp only [h₃] at h₄
    replace h₄ := wfl_of_type_bool_is_true_or_false h₄.left h₄.right
    rcases h₄ with h₄ | h₄ <;>
    simp only [h₄, pe_ite_true, pe_ite_false,
      interpret_term_some, interpret_term_none,
      pe_isNone_some, pe_isNone_none,
      interpret_not h₁ h₂, pe_not_true,
      pe_not_false]
  case h_6 =>
    split
    case h_1 ty heq =>
      have h₃ := typeOf_wf_term_is_wf h₂
      simp only [heq] at h₃
      cases h₃ ; rename_i h₃
      replace h₃ := Term.WellFormed.none_wf h₃
      simp only [interpret_eq h₁ h₂ h₃]
      have h₄ := interpret_term_wfl h₁ h₂
      simp only [heq] at h₄
      replace h₄ := wfl_of_type_option_is_option h₄.left h₄.right
      rcases h₄ with h₄ | h₄
      case inl =>
        simp only [h₄, interpret_term_none, pe_eq_same, pe_isNone_none]
      case inr =>
        replace ⟨_, h₄⟩ := h₄
        simp [h₄.left, interpret_term_none, pe_isNone_some, pe_eq_some_none]
    case h_2 h₃ =>
      simp only [isNone, interpret_term_prim]
      split <;> try {rfl}
      case h_1 heq =>
        have ⟨_, h₄⟩  : ∃ ty, (Term.interpret I t).typeOf = .option ty := by
          simp only [heq, Term.typeOf, TermType.option.injEq, exists_eq']
        simp only [(interpret_term_wfl h₁ h₂).right] at h₄
        simp only [h₄, TermType.option.injEq, forall_eq'] at h₃
      case h_4 heq | h_5 heq =>
        have h₄ := (interpret_term_wfl h₁ h₂).left.right
        simp only [heq, Term.isLiteral, reduceCtorEq] at h₄
      case h_6 =>
        split
        case h_1 heq =>
          simp only [(interpret_term_wfl h₁ h₂).right] at heq
          simp only [heq, TermType.option.injEq, forall_eq'] at h₃
        case h_2 => rfl

theorem interpret_isSome {I : Interpretation} {t : Term} :
  I.WellFormed εs → t.WellFormed εs →
  (isSome t).interpret I = isSome (t.interpret I)
:= by
  intro h₁ h₂
  have h₃ := (wf_isNone h₂).left
  simp only [isSome, interpret_not h₁ h₃, interpret_isNone h₁ h₂]

theorem interpret_noneOf {I : Interpretation} {ty : TermType} :
  (noneOf ty).interpret I = Term.none ty
:= by simp [noneOf, Term.interpret]

theorem interpret_someOf {I : Interpretation} {t : Term} :
  (someOf t).interpret I = Term.some (t.interpret I)
:= by simp [someOf, Term.interpret]

theorem interpret_option_get {εs : SymEntities} (I : Interpretation) {t : Term} {ty : TermType} :
  t.WellFormed εs → t.typeOf = .option ty →
  (Factory.option.get t).interpret I = Factory.option.get' I (t.interpret I)
:= by
  intro h₂ h₃
  rw [option.get.eq_def]
  split
  case h_1 =>
    simp only [interpret_term_some, option.get, option.get']
  case h_2 =>
    split
    case h_1 =>
      simp only [interpret_term_app_option_get]
    case h_2 h =>
      simp only [h₃, TermType.option.injEq, forall_eq'] at h

theorem interpret_option_get' {εs : SymEntities} {I : Interpretation} {t : Term} {ty : TermType} :
  I.WellFormed εs → t.WellFormed εs → t.typeOf = .option ty →
  (Factory.option.get' I t).interpret I = Factory.option.get' I (t.interpret I)
:= by
  intro h₁ h₂ h₃
  rw [option.get'.eq_def]
  split
  case h_1 =>
    simp only [interpret_term_none, option.get']
    have h₄ := wf_interpretation_implies_wfp_option_get h₁ (wf_term_none_implies h₂) rfl
    exact interpret_term_lit_id I h₄.left
  case h_2 => exact interpret_option_get I h₂ h₃

theorem interpret_record_get {εs : SymEntities} (I : Interpretation) {t : Term} {a : Attr} {rty : Map Attr TermType} {ty : TermType} :
  t.WellFormed εs → t.typeOf = .record rty → rty.find? a = .some ty →
  (Factory.record.get t a).interpret I = Factory.record.get (t.interpret I) a
:= by
  intro h₂ h₃ h₄
  rw [record.get.eq_def]
  split
  case h_1 r =>
    have ⟨tₐ, h₅⟩ := typeOf_term_record_attr_value h₃ h₄
    simp only [h₅.left, record.get, interpret_term_record]
    have h₆ := wf_term_record_implies_wf_map h₂
    have h₇ := Map.mapOnValues_eq_make_map (Term.interpret I) h₆
    unfold Map.toList at h₇
    rw [← h₇, Map.find?_mapOnValues_some (Term.interpret I) h₅.left]
  case h_2 =>
    split
    case h_1 h =>
      simp only [h₃, TermType.record.injEq] at h
      subst h
      simp only [h₄, interpret_term_app_record_get]
    case h_2 h =>
      simp only [h₃, TermType.record.injEq, forall_eq'] at h

private theorem interpret_app_foldr' {εs : SymEntities} {I : Interpretation} {t : Term} {table : List (Term × Term)} {init : Term}
  (h₀ : Interpretation.WellFormed I εs)
  (h₁ : Term.WellFormed εs t)
  (h₂ : Term.WellFormedLiteral εs init)
  (h₃ : ∀ (tᵢ tₒ : Term), (tᵢ, tₒ) ∈ table →
    Term.WellFormedLiteral εs tᵢ ∧
    Term.WellFormedLiteral εs tₒ ∧
    tᵢ.typeOf = t.typeOf ∧
    tₒ.typeOf = init.typeOf):
  Term.interpret I (List.foldr (fun x acc => Factory.ite (eq t x.fst) x.snd acc) init table) =
  match Option.map Prod.snd (List.find? (fun x => x.fst == Term.interpret I t) table) with
  | some t' => t'
  | none => init
:= by
  induction table
  case nil =>
    simp only [List.foldr_nil, List.find?_nil, Option.map_none']
    exact interpret_term_lit_id I h₂
  case cons hd tl ih =>
    simp only [List.foldr_cons]
    have h₄ := h₃ hd.fst hd.snd
    simp only [List.mem_cons, true_or, forall_const] at h₄
    rw [eq_comm] at h₄
    have h₅ := wf_eq h₁ h₄.left.left h₄.right.right.left
    have h₆ : Term.WellFormed εs (List.foldr (fun x acc => Factory.ite (eq t x.fst) x.snd acc) init tl) ∧
      (List.foldr (fun x acc => Factory.ite (eq t x.fst) x.snd acc) init tl).typeOf = init.typeOf := by
      apply wf_foldr h₂.left
      intro (tᵢ, tₒ) t' h₆ h₇ h₈
      simp only
      specialize h₃ tᵢ tₒ (by simp only [List.mem_cons, h₆, or_true])
      rw [← h₃.right.right.right]
      have h₉ := wf_eq h₁ h₃.left.left (by simp only [h₃])
      rw [← h₈] at h₃
      apply wf_ite h₉.left h₃.right.left.left h₇ h₉.right (by simp only [h₃])
    rw [
      interpret_ite h₀ h₅.left h₄.right.left.left h₆.left h₅.right (by rw [h₆.right, h₄.right.right.right]),
      interpret_eq h₀ h₁ h₄.left.left,
      interpret_term_lit_id I h₄.left,
      (pe_eq_lit (interpret_term_lit h₀ h₁) h₄.left.right).right,
      interpret_term_lit_id I h₄.right.left,
      List.find?_cons]
    cases heq : hd.fst == Term.interpret I t <;>
    simp only [beq_eq_false_iff_ne, ne_eq, beq_iff_eq] at heq  <;>
    simp only
    case false =>
      rw [eq_comm, ← beq_iff_eq] at heq
      simp only [heq, pe_ite_false]
      apply ih
      intro tᵢ tₒ hin
      apply h₃
      simp only [List.mem_cons, hin, or_true]
    case true =>
      simp only [Option.map, heq, beq_self_eq_true, pe_ite_true]

private theorem interpret_app_foldr {εs : SymEntities} {I : Interpretation} {t : Term} {f : UDF}
  (h₀ : Interpretation.WellFormed I εs)
  (h₁ : Term.WellFormed εs t)
  (h₂ : UnaryFunction.WellFormed εs (UnaryFunction.udf f))
  (h₃ : Term.typeOf t = UnaryFunction.argType (UnaryFunction.udf f)):
  Term.interpret I (List.foldr (fun x acc => Factory.ite (Factory.eq t x.fst) x.snd acc) f.default (Map.toList f.table)) =
  match Map.find? f.table (Term.interpret I t) with
  | some t' => t'
  | none => f.default
:= by
  have h₄ :
    (List.find? (fun x => x.fst == Term.interpret I t) f.table.1).map Prod.snd =
    Map.find? f.table (Term.interpret I t)
  := by
    simp only [Option.map, Map.find?, Map.kvs]
    split <;> rename_i heq <;> simp only [heq]
  rw [← h₄]
  simp only [Map.toList, Map.kvs]
  simp only [UnaryFunction.WellFormed, UDF.WellFormed, Map.toList, Map.kvs] at h₂
  apply interpret_app_foldr' h₀ h₁ h₂.left
  intro tᵢ tₒ hin
  have h₅ := h₂.right.right.right tᵢ tₒ hin
  simp only [UnaryFunction.argType] at h₃
  rw [← h₃] at h₅
  simp only [h₅, h₂, and_self]

theorem interpret_app {εs : SymEntities} {I : Interpretation} {t : Term} {f : UnaryFunction} :
  I.WellFormed εs → t.WellFormed εs → f.WellFormed εs → t.typeOf = f.argType →
  (Factory.app f t).interpret I = Factory.app (f.interpret I) (t.interpret I)
:= by
  intro h₀ h₁ h₂ h₃
  rw [Factory.app.eq_def]
  split
  case h_1 f =>
    simp only [interpret_term_app_uuf, UnaryFunction.interpret]
  case h_2 f =>
    simp only [UnaryFunction.interpret]
    split
    case isTrue h₄ =>
      have h₅ := interpret_term_lit_id I (And.intro h₁ h₄)
      simp only [h₅, Factory.app, h₄, ite_true]
      simp only [UnaryFunction.WellFormed, UDF.WellFormed] at h₂
      split
      case h_1 t' heq =>
        replace h₂ := h₂.right.right.right t t' (Map.find?_mem_toList heq)
        exact interpret_term_lit_id I h₂.right.right.left
      case h_2 =>
        exact interpret_term_lit_id I h₂.left
    case isFalse h₄ =>
      have h₅ := interpret_term_wfl h₀ h₁
      simp only [Factory.app, h₅.left.right, ite_true]
      exact interpret_app_foldr h₀ h₁ h₂ h₃

theorem interpret_ifFalse {εs : SymEntities} {I : Interpretation} {g t : Term} :
  I.WellFormed εs → g.WellFormed εs → g.typeOf = .bool → t.WellFormed εs →
  (ifFalse g t).interpret I = ifFalse (g.interpret I) (t.interpret I)
:= by
  intro h₁ h₂ h₃ h₄
  simp only [ifFalse, noneOf, someOf,
    interpret_ite h₁ h₂ (Term.WellFormed.none_wf (typeOf_wf_term_is_wf h₄)) (wf_term_some h₄ rfl).left
      h₃ (by simp only [typeOf_term_none, typeOf_term_some]),
    interpret_term_none, interpret_term_some, (interpret_term_wfl h₁ h₄).right]

theorem interpret_ifTrue {εs : SymEntities} {I : Interpretation} {g t : Term} :
  I.WellFormed εs → g.WellFormed εs → g.typeOf = .bool → t.WellFormed εs →
  (ifTrue g t).interpret I = ifTrue (g.interpret I) (t.interpret I)
:= by
  intro h₁ h₂ h₃ h₄
  simp [ifTrue, noneOf, someOf,
    interpret_ite h₁ h₂ (wf_term_some h₄ rfl).left (Term.WellFormed.none_wf (typeOf_wf_term_is_wf h₄))
      h₃ (by simp only [typeOf_term_none, typeOf_term_some]),
    interpret_term_none, interpret_term_some, (interpret_term_wfl h₁ h₄).right]

theorem interpret_ifSome {εs : SymEntities} {I : Interpretation} {g t : Term} :
  I.WellFormed εs → g.WellFormed εs → t.WellFormed εs →
  (ifSome g t).interpret I = ifSome (g.interpret I) (t.interpret I)
:= by
  intro h₁ h₂ h₃
  have h₄ := wf_isNone h₂
  have h₅ := interpret_term_wfl h₁ h₃
  rw [ifSome]
  split
  case h_1 heq =>
    have hwty := typeOf_wf_term_is_wf h₃
    rw [heq] at hwty
    cases hwty ; rename_i hwty
    rw [←h₅.right] at heq
    simp only [noneOf,
      interpret_ite h₁ h₄.left (Term.WellFormed.none_wf hwty) h₃
        h₄.right (by simp only [typeOf_term_none, ← heq, h₅]),
      interpret_isNone h₁ h₂, interpret_term_none, ifSome, heq]
  case h_2 hneq =>
    simp only [interpret_ifFalse h₁ h₄.left h₄.right h₃,
      interpret_isNone h₁ h₂]
    simp only [ifSome]
    split
    case h_1 heq' =>
      simp only [← h₅.right] at hneq
      simp only [heq', TermType.option.injEq, forall_eq'] at hneq
    case h_2 hneq' =>
      rfl

local macro "show_interpret_unary_op" op_fun:ident wfl_lit_of_type_thm:ident interpret_term_app_op_thm:ident : tactic => do
 `(tactic| (
    intro h₁ h₂ h₃
    simp only [$op_fun:ident]
    split
    · simp only [interpret_term_prim]
    · have hwf := interpret_term_wfl h₁ h₂
      rw [h₃] at hwf
      have ⟨_, ht⟩ := $wfl_lit_of_type_thm:ident hwf.left hwf.right
      simp only [$interpret_term_app_op_thm:ident, $op_fun:ident, ht]))

theorem interpret_string_like {εs : SymEntities} {I : Interpretation} {t : Term} {p : Pattern} :
  I.WellFormed εs → t.WellFormed εs → t.typeOf = .string →
  (Factory.string.like t p).interpret I = Factory.string.like (t.interpret I) p
:= by show_interpret_unary_op Factory.string.like wfl_of_type_string_is_string interpret_term_app_string_like

theorem interpret_bvnego {εs : SymEntities} {I : Interpretation} {t : Term} {n : Nat} :
  I.WellFormed εs → t.WellFormed εs → t.typeOf = .bitvec n →
  (Factory.bvnego t).interpret I = Factory.bvnego (t.interpret I)
:= by show_interpret_unary_op Factory.bvnego wfl_of_type_bitvec_is_bitvec interpret_term_app_bvnego

theorem interpret_bvneg {εs : SymEntities} {I : Interpretation} {t : Term} {n : Nat} :
  I.WellFormed εs → t.WellFormed εs → t.typeOf = .bitvec n →
  (Factory.bvneg t).interpret I = Factory.bvneg (t.interpret I)
:= by show_interpret_unary_op Factory.bvneg wfl_of_type_bitvec_is_bitvec interpret_term_app_bvneg

local macro "show_interpret_bvop" op_fun:ident pe_fun:ident interpret_op_thm:ident : tactic => do
 `(tactic| (
    simp only [$op_fun:ident, $pe_fun:ident]
    split
    · simp only [interpret_term_prim]
    · simp only [$interpret_op_thm:ident, $op_fun:ident, $pe_fun:ident]))

theorem interpret_bvslt {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvslt t₁ t₂).interpret I = Factory.bvslt (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvslt bvcmp interpret_term_app_bvslt

theorem interpret_bvsle {I : Interpretation} {t₁ t₂ : Term}  :
  (Factory.bvsle t₁ t₂).interpret I = Factory.bvsle (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvsle bvcmp interpret_term_app_bvsle

theorem interpret_bvule {I : Interpretation} {t₁ t₂ : Term}  :
  (Factory.bvule t₁ t₂).interpret I = Factory.bvule (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvule bvcmp interpret_term_app_bvule

theorem interpret_bvsaddo {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvsaddo t₁ t₂).interpret I = Factory.bvsaddo (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvsaddo bvso interpret_term_app_bvsaddo

theorem interpret_bvssubo {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvssubo t₁ t₂).interpret I = Factory.bvssubo (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvssubo bvso interpret_term_app_bvssubo

theorem interpret_bvsmulo {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvsmulo t₁ t₂).interpret I = Factory.bvsmulo (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvsmulo bvso interpret_term_app_bvsmulo

theorem interpret_bvadd {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvadd t₁ t₂).interpret I = Factory.bvadd (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvadd bvapp interpret_term_app_bvadd

theorem interpret_bvsub {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvsub t₁ t₂).interpret I = Factory.bvsub (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvsub bvapp interpret_term_app_bvsub

theorem interpret_bvmul {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvmul t₁ t₂).interpret I = Factory.bvmul (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvmul bvapp interpret_term_app_bvmul

theorem interpret_bvsdiv {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvsdiv t₁ t₂).interpret I = Factory.bvsdiv (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvsdiv bvapp interpret_term_app_bvsdiv

theorem interpret_bvudiv {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvudiv t₁ t₂).interpret I = Factory.bvudiv (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvudiv bvapp interpret_term_app_bvudiv

theorem interpret_bvsrem {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvsrem t₁ t₂).interpret I = Factory.bvsrem (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvsrem bvapp interpret_term_app_bvsrem

theorem interpret_bvsmod {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvsmod t₁ t₂).interpret I = Factory.bvsmod (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvsmod bvapp interpret_term_app_bvsmod

theorem interpret_bvumod {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvumod t₁ t₂).interpret I = Factory.bvumod (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvumod bvapp interpret_term_app_bvumod

theorem interpret_bvshl {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvshl t₁ t₂).interpret I = Factory.bvshl (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvshl bvapp interpret_term_app_bvshl

theorem interpret_bvlshr {I : Interpretation} {t₁ t₂ : Term} :
  (Factory.bvlshr t₁ t₂).interpret I = Factory.bvlshr (t₁.interpret I) (t₂.interpret I)
:= by show_interpret_bvop bvlshr bvapp interpret_term_app_bvlshr

local macro "show_interpret_bvopChecked" hI:ident hwf₁:ident hwf₂:ident hty₁:ident hty₂:ident factory_func:ident
  wf_check_func_thm:ident wf_op_func_thm:ident interp_check_func_thm:ident interp_op_func_thm:ident : tactic => do
 `(tactic| (
    have ⟨hgwf, hgty⟩ := $wf_check_func_thm $hwf₁ $hwf₂ $hty₁ $hty₂
    have ⟨htwf, htty⟩ := $wf_op_func_thm $hwf₁ $hwf₂ $hty₁ $hty₂
    simp only [$factory_func:ident, interpret_ifFalse $hI hgwf hgty htwf, $interp_check_func_thm:ident, $interp_op_func_thm:ident]
 ))

theorem interpret_bvaddChecked {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} {n : Nat}
  (hI : I.WellFormed εs)
  (hwf₁ : t₁.WellFormed εs) (hwf₂ : t₂.WellFormed εs)
  (hty₁ : t₁.typeOf = .bitvec n)
  (hty₂ : t₂.typeOf = .bitvec n) :
  (Factory.bvaddChecked t₁  t₂).interpret I = Factory.bvaddChecked (t₁.interpret I) (t₂.interpret I)
:= by
  show_interpret_bvopChecked hI hwf₁ hwf₂ hty₁ hty₂ Factory.bvaddChecked wf_bvsaddo wf_bvadd interpret_bvsaddo interpret_bvadd

theorem interpret_bvsubChecked {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} {n : Nat}
  (hI : I.WellFormed εs)
  (hwf₁ : t₁.WellFormed εs) (hwf₂ : t₂.WellFormed εs)
  (hty₁ : t₁.typeOf = .bitvec n)
  (hty₂ : t₂.typeOf = .bitvec n) :
  (Factory.bvsubChecked t₁  t₂).interpret I = Factory.bvsubChecked (t₁.interpret I) (t₂.interpret I)
:= by
  show_interpret_bvopChecked hI hwf₁ hwf₂ hty₁ hty₂ Factory.bvsubChecked wf_bvssubo wf_bvsub interpret_bvssubo interpret_bvsub

theorem interpret_bvmulChecked {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} {n : Nat}
  (hI : I.WellFormed εs)
  (hwf₁ : t₁.WellFormed εs) (hwf₂ : t₂.WellFormed εs)
  (hty₁ : t₁.typeOf = .bitvec n)
  (hty₂ : t₂.typeOf = .bitvec n) :
  (Factory.bvmulChecked t₁  t₂).interpret I = Factory.bvmulChecked (t₁.interpret I) (t₂.interpret I)
:= by
  show_interpret_bvopChecked hI hwf₁ hwf₂ hty₁ hty₂ Factory.bvmulChecked wf_bvsmulo wf_bvmul interpret_bvsmulo interpret_bvmul

theorem interpret_zero_extend {εs : SymEntities} {I : Interpretation} {n : Nat} {t : Term} :
  I.WellFormed εs → t.WellFormed εs →
  (Factory.zero_extend n t).interpret I = Factory.zero_extend n (t.interpret I)
:= by
  intro hI hw
  simp only [Factory.zero_extend]
  split <;> try simp only [interpret_term_prim]
  split <;> try simp only [interpret_term_app_zero_extend, zero_extend]
  split
  case h_1 hnty _ n _ heq =>
    have hty := (interpret_term_wf hI hw).right
    simp only [heq, typeOf_bv, TermType.bitvec] at hty
    rw [eq_comm] at hty
    specialize hnty n hty
    contradiction
  case h_2 hnty =>
    split <;> try rfl
    rename_i n heq
    have hlit := interpret_term_wfl hI hw
    replace ⟨bv, hlit⟩ := wfl_of_type_bitvec_is_bitvec hlit.left heq
    specialize hnty n bv hlit
    contradiction


theorem interpret_set_member {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} :
  t₁.WellFormed εs → t₂.WellFormed εs →
  Term.interpret I (set.member t₁ t₂) = set.member (Term.interpret I t₁) (Term.interpret I t₂)
:= by
  intro hw₁ hw₂
  simp only [set.member]
  split
  case h_1 =>
    simp only [interpret_term_prim, interpret_term_set_empty]
  case h_2 =>
    split
    case isTrue hlit =>
      simp only [Bool.and_eq_true] at hlit
      have hlit₁ := interpret_term_lit_id I (And.intro hw₁ hlit.left)
      have hlit₂ := interpret_term_lit_id I (And.intro hw₂ hlit.right)
      simp only [hlit₁, hlit₂, hlit, interpret_term_prim, set.member, Bool.and_self, ite_true]
    case isFalse =>
      simp only [interpret_term_app_set_member, set.member, Bool.and_eq_true]
  case h_3 =>
    simp only [interpret_term_app_set_member, set.member, Bool.and_eq_true]

theorem interpret_set_subset  {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} :
  t₁.WellFormed εs → t₂.WellFormed εs →
  Term.interpret I (set.subset t₁ t₂) = set.subset (Term.interpret I t₁) (Term.interpret I t₂)
:= by
  intro hw₁ hw₂
  simp only [set.subset]
  split
  case isTrue heq =>
    simp only [interpret_term_prim, heq, ite_true]
  case isFalse =>
    split
    case h_1 =>
      simp only [interpret_term_prim, interpret_term_set_empty, ite_self]
    case h_2 =>
      split
      case isTrue hneq hlit =>
        simp only [Bool.and_eq_true] at hlit
        have hlit₁ := interpret_term_lit_id I (And.intro hw₁ hlit.left)
        have hlit₂ := interpret_term_lit_id I (And.intro hw₂ hlit.right)
        simp only [hlit₁, hlit₂, hlit, hneq, interpret_term_prim, ite_false, ite_true, Bool.and_self]
      case isFalse =>
        simp only [interpret_term_app_set_subset, set.subset, Bool.and_eq_true]
    case h_3 =>
      simp only [interpret_term_app_set_subset, set.subset, Bool.and_eq_true]

theorem interpret_set_inter  {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs →
  t₁.typeOf = .set ty → t₂.typeOf = .set ty →
  Term.interpret I (set.inter t₁ t₂) = set.inter (Term.interpret I t₁) (Term.interpret I t₂)
:= by
  intro hI hw₁ hw₂ hty₁ hty₂
  simp only [set.inter]
  split
  case isTrue heq =>
    simp only [heq, ite_true]
  case isFalse =>
    split
    case h_1 =>
      simp only [interpret_term_set_empty, ite_self]
    case h_2 =>
      simp only [interpret_term_set_empty]
      split
      case isTrue h =>
        simp only [h]
      case isFalse =>
        split
        case h_1 h₂ _ _ _ h₃ =>
          have h₄ := (interpret_term_wf hI hw₁).right
          simp only [h₃, Term.typeOf, hty₁, TermType.set.injEq] at h₄
          subst h₄
          simp only [Term.typeOf, TermType.set.injEq] at hty₂
          simp only [h₃, hty₂, not_true_eq_false] at h₂
        case h_2 => rfl
        case h_3 hneq _ heq =>
          simp only [Term.set.injEq] at heq
          simp only [heq, forall_const] at hneq
        case h_4 hneq _ =>
          simp only [Term.set.injEq, true_and, forall_eq'] at hneq
    case h_3 hneq =>
      simp only [Term.typeOf, TermType.set.injEq] at hty₁ hty₂
      rw [eq_comm] at hty₁ hty₂ ; subst hty₁ hty₂
      split
      case isTrue s₁ s₂ _ _ heq =>
        simp only [Bool.and_eq_true] at heq
        simp only [Term.set.injEq, and_true] at hneq
        have hmap : (List.map (Term.interpret I) (Set.intersect s₁ s₂).1) = (Set.intersect s₁ s₂).1 := by
          rw (config := {occs := .pos [2]}) [← List.map_id' ((Set.intersect s₁ s₂).1)]
          apply List.map_congr
          intro x h
          rw [Set.in_list_iff_in_set] at h
          replace h : x ∈ s₁ ∩ s₂ := by simp only [Inter.inter, h]
          rw [Set.mem_inter_iff] at h
          have hlit := lit_term_set_implies_lit_elt heq.left h.left
          have hwf := wf_term_set_implies_wf_elt hw₁ h.left
          exact interpret_term_lit_id I (And.intro hwf hlit)
        have hws : (Set.intersect s₁ s₂).WellFormed := by
          exact Set.inter_wf (wf_term_set_implies_wf_set hw₁)
        simp only [Set.WellFormed, Set.toList, Set.elts] at hws
        simp only [interpret_term_lit_id I (And.intro hw₁ heq.left),
          interpret_term_lit_id I (And.intro hw₂ heq.right),
          hneq, heq, interpret_term_set, Set.elts, hmap, ← hws,
          Term.set.injEq, and_true, ite_false, ite_true, Bool.and_self]
      case isFalse =>
        simp only [interpret_term_app_set_inter, set.inter, Bool.and_eq_true]
    case h_4 =>
      simp only [interpret_term_app_set_inter, set.inter, Bool.and_eq_true]

theorem interpret_set_isEmpty {εs : SymEntities} {t : Term} {ty : TermType} :
  I.WellFormed εs → t.WellFormed εs → t.typeOf = .set ty →
  (set.isEmpty t).interpret I = set.isEmpty (t.interpret I)
:= by
  intro hI hw hty
  simp [set.isEmpty]
  split
  case h_1 =>
    simp only [interpret_term_prim, interpret_term_set_empty]
  case h_2 hd tl ty =>
    have hcons := List.canonicalize_not_nil (fun x => x) (Term.interpret I hd :: List.map (Term.interpret I) tl)
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_iff] at hcons
    replace ⟨_, _, hcons⟩ := List.exists_cons_of_ne_nil hcons
    simp only [interpret_term_prim, interpret_term_set, Set.make, Set.elts, List.map_cons, hcons]
  case h_3 =>
    have hwt := typeOf_wf_term_is_wf hw
    simp only [hty] at hwt
    cases hwt <;> rename_i hwt
    have hwe := wf_term_set_empty hwt
    simp only [hty, interpret_eq hI hw hwe.left, interpret_term_set_empty]
    have hwl := interpret_term_wfl hI hw
    simp only [hty] at hwl
    have ⟨ts, hws⟩ := wfl_of_type_set_is_set hwl.left hwl.right
    cases ts <;> rename_i ts
    simp only [hws] at *
    cases ts
    case nil =>
      simp only [pe_eq_same]
    case cons hd tl =>
      simp only [pe_eq_lit hwl.left.right (lit_term_set_empty ty), Term.prim.injEq,
        TermPrim.bool.injEq, beq_eq_false_iff_ne, ne_eq, Term.set.injEq, Set.mk.injEq, reduceCtorEq,
        and_true, not_false_eq_true]

theorem interpret_set_intersects {εs : SymEntities} {I : Interpretation} {t₁ t₂ : Term} {ty : TermType} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs →
  t₁.typeOf = .set ty → t₂.typeOf = .set ty →
  Term.interpret I (set.intersects t₁ t₂) = set.intersects (Term.interpret I t₁) (Term.interpret I t₂)
:= by
  intro hI hw₁ hw₂ hty₁ hty₂
  have hw₃ := wf_set_inter hw₁ hw₂ hty₁ hty₂
  have hw₄ := wf_set_isEmpty hw₃.left hw₃.right
  simp only [set.intersects, interpret_not hI hw₄.left,
    interpret_set_isEmpty hI hw₃.left hw₃.right,
    interpret_set_inter hI hw₁ hw₂ hty₁ hty₂]

private theorem interpret_anyTrue_foldl {εs : SymEntities} {I : Interpretation} {ts : List Term} {f : Term → Term} {init : Term} :
  I.WellFormed εs →
  (∀ t ∈ ts, (f t).WellFormed εs ∧ (f t).typeOf = .bool) →
  (∀ t ∈ ts, (f t).interpret I = f (t.interpret I)) →
  init.WellFormed εs →
  init.typeOf = .bool →
  (ts.foldl (λ acc t => Factory.or (f t) acc) init).interpret I =
  (ts.map (Term.interpret I)).foldl (λ acc t => Factory.or (f t) acc) (init.interpret I)
:= by
  intro hI hwts hts hwi htyi
  induction ts generalizing init
  case nil =>
    simp only [List.foldl_nil, List.map_nil]
  case cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons]
    have hhd := hwts hd
    simp only [List.mem_cons, true_or, forall_const] at hhd
    have hor := wf_or hhd.left hwi hhd.right htyi
    rw [ih _ _ hor.left hor.right]
    · specialize hts hd
      simp only [List.mem_cons, true_or, forall_const] at hts
      rw [interpret_or hI hhd.left hwi hhd.right htyi, hts]
    · intro t hin
      specialize hwts t
      simp only [List.mem_cons, hin, or_true, forall_const] at hwts
      exact hwts
    · intro t hin
      specialize hts t
      simp only [List.mem_cons, hin, or_true, forall_const] at hts
      exact hts

theorem interpret_anyTrue {εs : SymEntities} {I : Interpretation} {ts : List Term} {f : Term → Term} :
  I.WellFormed εs →
  (∀ t ∈ ts, (f t).WellFormed εs ∧ (f t).typeOf = .bool) →
  (∀ t ∈ ts, (f t).interpret I = f (t.interpret I)) →
  (anyTrue f ts).interpret I = anyTrue f (ts.map (Term.interpret I))
:= by
  intro hI hwt hts
  unfold anyTrue
  rw (config := {occs := .pos [2]}) [← @interpret_term_prim I]
  exact interpret_anyTrue_foldl hI hwt hts wf_bool typeOf_bool

theorem interpret_anyNone {εs : SymEntities} {I : Interpretation} {gs : List Term} :
  I.WellFormed εs →
  (∀ g ∈ gs, g.WellFormed εs) →
  (anyNone gs).interpret I = anyNone (gs.map (Term.interpret I))
:= by
  intro hI hwg
  unfold anyNone
  apply interpret_anyTrue hI <;>
  intro t hin <;>
  specialize hwg t hin
  · exact wf_isNone hwg
  · exact interpret_isNone hI hwg

theorem interpret_ifAllSome {εs : SymEntities} {I : Interpretation} {gs : List Term} {t : Term} :
  I.WellFormed εs →
  (∀ g ∈ gs, g.WellFormed εs) →
  t.WellFormed εs →
  t.typeOf = .option ty →
  (ifAllSome gs t).interpret I = ifAllSome (gs.map (Term.interpret I)) (t.interpret I)
:= by
  intro hI hwg hwt hty
  have ⟨_, hty'⟩ := interpret_term_wf hI hwt
  have hwn := wf_anyNone hwg
  have hwty := Term.WellFormed.none_wf (typeOf_wf_term_is_wf hwt)
  rw [hty] at hwty
  cases hwty ; rename_i hwty ; cases hwty ; rename_i hwty
  simp only [ifAllSome, hty', hty, noneOf,
    interpret_ite hI hwn.left (Term.WellFormed.none_wf hwty) hwt
      hwn.right (by simp only [typeOf_term_none, hty]),
    interpret_anyNone hI hwg, interpret_term_none]

theorem interpret_setOf {I : Interpretation} {ts : List Term} {ty : TermType} :
  (setOf ts ty).interpret I = setOf (ts.map (Term.interpret I)) ty
:= by
  simp only [setOf, interpret_term_set, Term.set.injEq, and_true, Set.make_make_eqv]
  exact List.map_equiv (Term.interpret I) (Set.elts (Set.make ts)) ts Set.elts_make_equiv

theorem interpret_recordOf {I : Interpretation} {ats : List (Attr × Term)} :
  (recordOf ats).interpret I = recordOf (ats.map (Prod.map id (Term.interpret I)))
:= by
  have h : (fun (x : Attr × Term) => (x.fst, Term.interpret I x.snd)) = Prod.map id (Term.interpret I) := by
    unfold Prod.map id
    simp only
  simp only [recordOf, interpret_term_record, h, Term.record.injEq]
  simp only [Map.make, Map.kvs, List.canonicalize_of_map_fst, List.canonicalize_idempotent]

theorem interpret_ext_decimal_val {I : Interpretation} {t : Term} :
  Term.interpret I (ext.decimal.val t) = ext.decimal.val (t.interpret I)
:= by
  simp only [ext.decimal.val]
  split
  case h_1 =>
    simp only [interpret_term_prim]
  case h_2 hneq =>
    split
    case h_1 heq =>
      simp only [interpret_term_app_ext_decimal_val, ext.decimal.val, heq]
    case h_2 =>
      simp only [interpret_term_app_ext_decimal_val, ext.decimal.val, ext.decimal.val.match_1.eq_2]

theorem interpret_ext_ipaddr_isV4 {I : Interpretation} {t : Term} :
  (ext.ipaddr.isV4 t).interpret I  = ext.ipaddr.isV4 (t.interpret I)
:= by
  simp only [ext.ipaddr.isV4]
  split <;> try (simp only [interpret_term_prim])
  simp only [interpret_term_app_ext_ipaddr_isV4, ext.ipaddr.isV4]

theorem interpret_ext_ipaddr_addrV4 {I : Interpretation} {t : Term} :
  (ext.ipaddr.addrV4 t).interpret I = ext.ipaddr.addrV4' I (t.interpret I)
:= by
  simp only [ext.ipaddr.addrV4]
  split <;> try (simp only [interpret_term_prim])
  · simp only [ext.ipaddr.addrV4', ext.ipaddr.addrV4]
  · simp only [interpret_term_app_ext_ipaddr_addrV4]

theorem interpret_ext_ipaddr_prefixV4 {I : Interpretation} {t : Term} :
  (ext.ipaddr.prefixV4 t).interpret I = ext.ipaddr.prefixV4' I (t.interpret I)
:= by
  simp only [ext.ipaddr.prefixV4]
  split <;> try (simp only [interpret_term_prim])
  · simp only [ext.ipaddr.prefixV4', ext.ipaddr.prefixV4]
    split <;>
    simp only [interpret_someOf, interpret_noneOf, interpret_term_prim] <;>
    simp only [noneOf, someOf]
  · simp only [interpret_term_app_ext_ipaddr_prefixV4]

theorem interpret_ext_ipaddr_addrV6 {I : Interpretation} {t : Term} :
  (ext.ipaddr.addrV6 t).interpret I = ext.ipaddr.addrV6' I (t.interpret I)
:= by
  simp only [ext.ipaddr.addrV6]
  split <;> try (simp only [interpret_term_prim])
  · simp only [ext.ipaddr.addrV6', ext.ipaddr.addrV6]
  · simp only [interpret_term_app_ext_ipaddr_addrV6]

theorem interpret_ext_ipaddr_prefixV6 {I : Interpretation} {t : Term} :
  (ext.ipaddr.prefixV6 t).interpret I = ext.ipaddr.prefixV6' I (t.interpret I)
:= by
  simp only [ext.ipaddr.prefixV6]
  split <;> try (simp only [interpret_term_prim])
  · simp only [ext.ipaddr.prefixV6', ext.ipaddr.prefixV6]
    split <;>
    simp only [interpret_someOf, interpret_noneOf, interpret_term_prim] <;>
    simp only [noneOf, someOf]
  · simp only [interpret_term_app_ext_ipaddr_prefixV6]

theorem interpret_ext_datetime_val {I : Interpretation} {t : Term} :
  Term.interpret I (ext.datetime.val t) = ext.datetime.val (t.interpret I)
:= by
  simp only [ext.datetime.val]
  split
  case h_1 =>
    simp only [interpret_term_prim]
  case h_2 hneq =>
    split
    case h_1 heq =>
      simp only [interpret_term_app_ext_datetime_val, ext.datetime.val, heq]
    case h_2 =>
      simp only [interpret_term_app_ext_datetime_val, ext.datetime.val, ext.datetime.val.match_1.eq_2]

theorem interpret_ext_datetime_ofBitVec {I : Interpretation} {t : Term} :
  Term.interpret I (ext.datetime.ofBitVec t) = ext.datetime.ofBitVec (t.interpret I)
:= by
  simp only [ext.datetime.ofBitVec]
  split
  case h_1 =>
    simp only [interpret_term_prim]
  case h_2 hneq =>
    split
    case h_1 heq =>
      simp only [interpret_term_app_ext_datetime_ofBitVec, ext.datetime.ofBitVec, heq]
    case h_2 =>
      simp only [interpret_term_app_ext_datetime_ofBitVec, ext.datetime.ofBitVec, ext.datetime.ofBitVec.match_1.eq_2]

theorem interpret_ext_duration_val {I : Interpretation} {t : Term} :
  Term.interpret I (ext.duration.val t) = ext.duration.val (t.interpret I)
:= by
  simp only [ext.duration.val]
  split
  case h_1 =>
    simp only [interpret_term_prim]
  case h_2 hneq =>
    split
    case h_1 heq =>
      simp only [interpret_term_app_ext_duration_val, ext.duration.val, heq]
    case h_2 =>
      simp only [interpret_term_app_ext_duration_val, ext.duration.val, ext.duration.val.match_1.eq_2]

theorem interpret_ext_duration_ofBitVec {I : Interpretation} {t : Term} :
  Term.interpret I (ext.duration.ofBitVec t) = ext.duration.ofBitVec (t.interpret I)
:= by
  simp only [ext.duration.ofBitVec]
  split
  case h_1 =>
    simp only [interpret_term_prim]
  case h_2 hneq =>
    split
    case h_1 heq =>
      simp only [interpret_term_app_ext_duration_ofBitVec, ext.duration.ofBitVec, heq]
    case h_2 =>
      simp only [interpret_term_app_ext_duration_ofBitVec, ext.duration.ofBitVec]

theorem interpret_tagOf {I : Interpretation} {t₁ t₂ : Term} :
  (tagOf t₁ t₂).interpret I = tagOf (t₁.interpret I) (t₂.interpret I)
:= by
  simp only [tagOf, EntityTag.mk, interpret_term_record, Map.make, Map.kvs, List.map_cons,
    List.map_nil, List.canonicalize, List.insertCanonical, String.reduceLT, ↓reduceIte]

end Cedar.Thm
