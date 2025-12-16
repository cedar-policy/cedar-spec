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

import Cedar.Thm.SymCC.Verifier.VerifyEvaluatePair
import Cedar.Thm.SymCC.Verifier.VerifyEvaluateQueries

/-!
This file proves that `verifyEvaluatePair` queries are well-behaved.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

@[simp]
private theorem error_beq_ok [BEq ε] [LawfulBEq ε] [BEq α] [LawfulBEq α] (e : ε) (v : α) :
  (Except.error e == Except.ok v) = false
:= by simp

@[simp]
private theorem ok_beq_ok [BEq ε] [LawfulBEq ε] [BEq α] [LawfulBEq α] (v₁ v₂ : α) :
  (Except.ok v₁ == Except.ok v₂ (ε := ε)) = (v₁ == v₂)
:= by
  by_cases v₁ = v₂
  · subst v₂ ; simp
  · simp [*, BEq.beq, instBEqExcept_cedar.beq]

@[simp]
private theorem ok_ne_ok [BEq ε] [LawfulBEq ε] [BEq α] [LawfulBEq α] (v₁ v₂ : α) :
  Except.ok v₁ ≠ Except.ok v₂ (ε := ε) ↔ v₁ ≠ v₂
:= by simp

theorem verifyMatchesEquivalent_wbepq :
  WellBehavedEvaluatePairQuery
    (λ t₁ t₂ =>
      let t₁matches := eq t₁ (⊙true)
      let t₂matches := eq t₂ (⊙true)
      eq t₁matches t₂matches)
    (λ r₁ r₂ => (r₁ == .ok true) == (r₂ == .ok true))
:= by
  constructor
  · -- WellFormedOutput
    simp only [WellBehavedEvaluatePairQuery.WellFormedOutput]
    intro t₁ t₂ εs ⟨hwt₁, hty₁, hwt₂, hty₂⟩
    have hwf₁ := wf_eq hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₁]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf₂ := wf_eq hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₂]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    exact wf_eq hwf₁.left hwf₂.left (by simp only [someOf]; rw [hwf₁.right, hwf₂.right])
  constructor
  · -- Interpretable
    simp only [WellBehavedEvaluatePairQuery.Interpretable]
    intro t₁ t₂ εs I ⟨hwt₁, hty₁, hwt₂, hty₂⟩ hwI
    have hwf₁ := wf_eq hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₁]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf₂ := wf_eq hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₂]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    simp only [someOf]
    rw [interpret_eq hwI hwf₁.left hwf₂.left,
        interpret_eq hwI hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true))),
        interpret_eq hwI hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))]
    simp only [interpret_term_some, interpret_term_prim]
  · -- Same
    intro t₁ t₂ εs r₁ r₂ ⟨hwt₁, hty₁, hwt₂, hty₂⟩ hs₁ hs₂
    cases r₁ <;> cases r₂
    case error.error =>
      replace ⟨_, hs₁⟩ := (same_error_implies hs₁).right
      replace ⟨_, hs₂⟩ := (same_error_implies hs₂).right
      subst hs₁ hs₂
      simp only [same_bool_def, someOf, pe_eq_none_some]
      rfl
    case error.ok =>
      replace ⟨_, hs₁⟩ := (same_error_implies hs₁).right
      replace ⟨t₂', heq₂, hs₂⟩ := same_ok_implies hs₂
      subst hs₁ heq₂
      have hwt₂' : t₂'.WellFormed εs ∧ t₂'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₂
        · rw [typeOf_term_some, TermType.option.injEq] at hty₂
          exact hty₂
      replace ⟨b₂, hv₂⟩ := value_type_bool_implies_bool hs₂ hwt₂'.right
      subst hv₂
      replace hs₂ := same_bool_implies hs₂
      subst hs₂
      simp only [same_bool_def, someOf, pe_eq_none_some, pe_eq_some_some]
      cases b₂ <;> simp only [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_eq_prim, error_beq_ok]
      · have : (Term.prim (.bool false) == Term.prim (.bool true)) = false := by simp
        simp [this]
      · simp
    case ok.error =>
      replace ⟨t₁', heq₁, hs₁⟩ := same_ok_implies hs₁
      replace ⟨_, hs₂⟩ := (same_error_implies hs₂).right
      subst heq₁ hs₂
      have hwt₁' : t₁'.WellFormed εs ∧ t₁'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₁
        · rw [typeOf_term_some, TermType.option.injEq] at hty₁
          exact hty₁
      replace ⟨b₁, hv₁⟩ := value_type_bool_implies_bool hs₁ hwt₁'.right
      subst hv₁
      replace hs₁ := same_bool_implies hs₁
      rw [hs₁]
      simp only [same_bool_def, someOf, pe_eq_some_some, pe_eq_none_some]
      cases b₁ <;> simp only [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_eq_prim, error_beq_ok]
      · have : (Term.prim (.bool false) == Term.prim (.bool true)) = false := by simp
        simp [this]
      · simp
    case ok.ok =>
      replace ⟨t₁', heq₁, hs₁⟩ := same_ok_implies hs₁
      replace ⟨t₂', heq₂, hs₂⟩ := same_ok_implies hs₂
      subst heq₁ heq₂
      have hwt₁' : t₁'.WellFormed εs ∧ t₁'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₁
        · rw [typeOf_term_some, TermType.option.injEq] at hty₁
          exact hty₁
      have hwt₂' : t₂'.WellFormed εs ∧ t₂'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₂
        · rw [typeOf_term_some, TermType.option.injEq] at hty₂
          exact hty₂
      replace ⟨b₁, hv₁⟩ := value_type_bool_implies_bool hs₁ hwt₁'.right
      replace ⟨b₂, hv₂⟩ := value_type_bool_implies_bool hs₂ hwt₂'.right
      subst hv₁ hv₂
      replace hs₁ := same_bool_implies hs₁
      replace hs₂ := same_bool_implies hs₂
      rw [hs₁, hs₂]
      simp only [same_bool_def, someOf, pe_eq_some_some]
      cases b₁ <;> cases b₂ <;> simp only [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_eq_prim]
      · have : (Term.prim (.bool false) == Term.prim (.bool true)) = false := by simp
        simp [this]
      · simp [BEq.beq, instBEqExcept_cedar.beq]
      · simp [BEq.beq, instBEqExcept_cedar.beq]
      · simp [BEq.beq, instBEqExcept_cedar.beq]

theorem verifyMatchesImplies_wbepq :
  WellBehavedEvaluatePairQuery
    (λ t₁ t₂ =>
      let t₁matches := eq t₁ (⊙true)
      let t₂matches := eq t₂ (⊙true)
      implies t₁matches t₂matches)
    (λ r₁ r₂ => (r₁ != .ok true) || (r₂ == .ok true))
:= by
  constructor
  · -- WellFormedOutput
    simp only [WellBehavedEvaluatePairQuery.WellFormedOutput]
    intro t₁ t₂ εs ⟨hwt₁, hty₁, hwt₂, hty₂⟩
    have hwf₁ := wf_eq hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₁]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf₂ := wf_eq hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₂]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    simp only [implies]
    have hwf_not := wf_not hwf₁.left hwf₁.right
    exact wf_or hwf_not.left hwf₂.left hwf_not.right hwf₂.right
  constructor
  · -- Interpretable
    simp only [WellBehavedEvaluatePairQuery.Interpretable]
    intro t₁ t₂ εs I ⟨hwt₁, hty₁, hwt₂, hty₂⟩ hwI
    have hwf₁ := wf_eq hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₁]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf₂ := wf_eq hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₂]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf_not := wf_not hwf₁.left hwf₁.right
    simp only [implies, someOf]
    rw [interpret_or hwI hwf_not.left hwf₂.left hwf_not.right hwf₂.right,
        interpret_not hwI hwf₁.left,
        interpret_eq hwI hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true))),
        interpret_eq hwI hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))]
    simp only [interpret_term_some, interpret_term_prim]
  · -- Same
    intro t₁ t₂ εs r₁ r₂ ⟨hwt₁, hty₁, hwt₂, hty₂⟩ hs₁ hs₂
    cases r₁ <;> cases r₂
    case error.error =>
      replace ⟨_, hs₁⟩ := (same_error_implies hs₁).right
      replace ⟨_, hs₂⟩ := (same_error_implies hs₂).right
      subst hs₁ hs₂
      simp only [same_bool_def, someOf, implies, pe_eq_none_some, pe_not_lit]
      rfl
    case error.ok =>
      replace ⟨_, hs₁⟩ := (same_error_implies hs₁).right
      replace ⟨t₂', heq₂, hs₂⟩ := same_ok_implies hs₂
      subst hs₁ heq₂
      have hwt₂' : t₂'.WellFormed εs ∧ t₂'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₂
        · rw [typeOf_term_some, TermType.option.injEq] at hty₂
          exact hty₂
      replace ⟨b₂, hv₂⟩ := value_type_bool_implies_bool hs₂ hwt₂'.right
      subst hv₂
      replace hs₂ := same_bool_implies hs₂
      subst hs₂
      simp only [same_bool_def, someOf, implies, pe_eq_none_some, pe_eq_some_some]
      cases b₂ <;> simp [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_not_lit, pe_or_true_left]
    case ok.error =>
      replace ⟨t₁', heq₁, hs₁⟩ := same_ok_implies hs₁
      replace ⟨_, hs₂⟩ := (same_error_implies hs₂).right
      subst heq₁ hs₂
      have hwt₁' : t₁'.WellFormed εs ∧ t₁'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₁
        · rw [typeOf_term_some, TermType.option.injEq] at hty₁
          exact hty₁
      replace ⟨b₁, hv₁⟩ := value_type_bool_implies_bool hs₁ hwt₁'.right
      subst hv₁
      replace hs₁ := same_bool_implies hs₁
      rw [hs₁]
      simp only [same_bool_def, someOf, implies, pe_eq_some_some, pe_eq_none_some]
      cases b₁ <;> simp [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_not_lit, pe_or_false_right]
      · simp [BEq.beq]
    case ok.ok =>
      replace ⟨t₁', heq₁, hs₁⟩ := same_ok_implies hs₁
      replace ⟨t₂', heq₂, hs₂⟩ := same_ok_implies hs₂
      subst heq₁ heq₂
      have hwt₁' : t₁'.WellFormed εs ∧ t₁'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₁
        · rw [typeOf_term_some, TermType.option.injEq] at hty₁
          exact hty₁
      have hwt₂' : t₂'.WellFormed εs ∧ t₂'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₂
        · rw [typeOf_term_some, TermType.option.injEq] at hty₂
          exact hty₂
      replace ⟨b₁, hv₁⟩ := value_type_bool_implies_bool hs₁ hwt₁'.right
      replace ⟨b₂, hv₂⟩ := value_type_bool_implies_bool hs₂ hwt₂'.right
      subst hv₁ hv₂
      replace hs₁ := same_bool_implies hs₁
      replace hs₂ := same_bool_implies hs₂
      rw [hs₁, hs₂]
      simp only [same_bool_def, someOf, implies, pe_eq_some_some]
      have : (Term.prim (.bool false) == Term.prim (.bool true)) = false := by simp
      cases b₁ <;> cases b₂ <;> simp [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_not_lit, pe_or_true_right, pe_or_false_right, this]

theorem verifyMatchesDisjoint_wbepq :
  WellBehavedEvaluatePairQuery
    (λ t₁ t₂ =>
      let t₁matches := eq t₁ (⊙true)
      let t₂matches := eq t₂ (⊙true)
      not (and t₁matches t₂matches))
    (λ r₁ r₂ => !((r₁ == .ok true) && (r₂ == .ok true)))
:= by
  constructor
  · -- WellFormedOutput
    simp only [WellBehavedEvaluatePairQuery.WellFormedOutput]
    intro t₁ t₂ εs ⟨hwt₁, hty₁, hwt₂, hty₂⟩
    have hwf₁ := wf_eq hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₁]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf₂ := wf_eq hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₂]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf_and := wf_and hwf₁.left hwf₂.left hwf₁.right hwf₂.right
    exact wf_not hwf_and.left hwf_and.right
  constructor
  · -- Interpretable
    simp only [WellBehavedEvaluatePairQuery.Interpretable]
    intro t₁ t₂ εs I ⟨hwt₁, hty₁, hwt₂, hty₂⟩ hwI
    have hwf₁ := wf_eq hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₁]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf₂ := wf_eq hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by rw [hty₂]; simp only [typeOf_term_some, Term.typeOf, TermPrim.typeOf])
    have hwf_and := wf_and hwf₁.left hwf₂.left hwf₁.right hwf₂.right
    simp only [someOf]
    rw [interpret_not hwI hwf_and.left,
        interpret_and hwI hwf₁.left hwf₂.left hwf₁.right hwf₂.right,
        interpret_eq hwI hwt₁ (Term.WellFormed.some_wf (wf_bool (b := true))),
        interpret_eq hwI hwt₂ (Term.WellFormed.some_wf (wf_bool (b := true)))]
    simp only [interpret_term_some, interpret_term_prim]
  · -- Same
    intro t₁ t₂ εs r₁ r₂ ⟨hwt₁, hty₁, hwt₂, hty₂⟩ hs₁ hs₂
    cases r₁ <;> cases r₂
    case error.error =>
      replace ⟨_, hs₁⟩ := (same_error_implies hs₁).right
      replace ⟨_, hs₂⟩ := (same_error_implies hs₂).right
      subst hs₁ hs₂
      simp only [same_bool_def, someOf, pe_eq_none_some, pe_and_false_left, pe_not_false]
      rfl
    case error.ok =>
      replace ⟨_, hs₁⟩ := (same_error_implies hs₁).right
      replace ⟨t₂', heq₂, hs₂⟩ := same_ok_implies hs₂
      subst hs₁ heq₂
      have hwt₂' : t₂'.WellFormed εs ∧ t₂'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₂
        · rw [typeOf_term_some, TermType.option.injEq] at hty₂
          exact hty₂
      replace ⟨b₂, hv₂⟩ := value_type_bool_implies_bool hs₂ hwt₂'.right
      subst hv₂
      replace hs₂ := same_bool_implies hs₂
      subst hs₂
      simp only [same_bool_def, someOf, pe_eq_none_some, pe_eq_some_some]
      cases b₂ <;> simp [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_and_false_left, pe_not_false]
    case ok.error =>
      replace ⟨t₁', heq₁, hs₁⟩ := same_ok_implies hs₁
      replace ⟨_, hs₂⟩ := (same_error_implies hs₂).right
      subst heq₁ hs₂
      have hwt₁' : t₁'.WellFormed εs ∧ t₁'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₁
        · rw [typeOf_term_some, TermType.option.injEq] at hty₁
          exact hty₁
      replace ⟨b₁, hv₁⟩ := value_type_bool_implies_bool hs₁ hwt₁'.right
      subst hv₁
      replace hs₁ := same_bool_implies hs₁
      rw [hs₁]
      simp only [same_bool_def, someOf, pe_eq_some_some, pe_eq_none_some]
      cases b₁ <;> simp only [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_and_false_right, pe_not_false]
      · simp [Bool.and_false, Bool.not_false]
      · simp [Bool.and_false, Bool.not_false]
    case ok.ok =>
      replace ⟨t₁', heq₁, hs₁⟩ := same_ok_implies hs₁
      replace ⟨t₂', heq₂, hs₂⟩ := same_ok_implies hs₂
      subst heq₁ heq₂
      have hwt₁' : t₁'.WellFormed εs ∧ t₁'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₁
        · rw [typeOf_term_some, TermType.option.injEq] at hty₁
          exact hty₁
      have hwt₂' : t₂'.WellFormed εs ∧ t₂'.typeOf = .bool := by
        constructor
        · exact wf_term_some_implies hwt₂
        · rw [typeOf_term_some, TermType.option.injEq] at hty₂
          exact hty₂
      replace ⟨b₁, hv₁⟩ := value_type_bool_implies_bool hs₁ hwt₁'.right
      replace ⟨b₂, hv₂⟩ := value_type_bool_implies_bool hs₂ hwt₂'.right
      subst hv₁ hv₂
      replace hs₁ := same_bool_implies hs₁
      replace hs₂ := same_bool_implies hs₂
      rw [hs₁, hs₂]
      simp only [same_bool_def, someOf, pe_eq_some_some]
      have : (Term.prim (.bool false) == Term.prim (.bool true)) = false := by simp
      cases b₁ <;> cases b₂ <;> simp [pe_eq_simplify_same, pe_eq_simplify_lit, term_prim_is_lit, pe_and_false_left, pe_and_false_right, pe_and_true_left, pe_not_false, pe_not_true, this]

end Cedar.Thm
