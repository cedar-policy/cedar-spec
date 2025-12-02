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

import Cedar.Thm.SymCC.Verifier.VerifyEvaluate

/-!
This file proves that `verifyEvaluate` queries are well-behaved.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

private theorem value_type_bool_implies_bool {v : Value} {t : Term} :
  v ∼ t → t.typeOf = .bool → ∃ b, v = .prim (.bool b)
:= by
  intro hs hty
  simp only [Same.same, SameValues] at hs
  cases t
  case prim p =>
    cases p
    case bool b =>
      simp only [Term.value?, TermPrim.value?, Option.some.injEq] at hs
      exists b
      simp only [hs]
    all_goals simp_all [Term.value?, TermPrim.value?, Term.typeOf, TermPrim.typeOf]
    case ext x => split at hty <;> simp_all
  all_goals simp_all [Term.value?, Term.typeOf]
  case record m => cases m ; simp_all [Term.value?, Term.typeOf]

theorem verifyNeverErrors_wbeq :
  WellBehavedEvaluateQuery isSome Except.isOk
:= by
  have hwo : WellBehavedEvaluateQuery.WellFormedOutput isSome := by
    simp only [WellBehavedEvaluateQuery.WellFormedOutput]
    intro _ _ hwt
    exact wf_isSome hwt.left
  have hi : WellBehavedEvaluateQuery.Interpretable isSome := by
    simp only [WellBehavedEvaluateQuery.Interpretable]
    intro _ _ _ hwt hI
    exact interpret_isSome hI hwt.left
  have hs : WellBehavedEvaluateQuery.Same isSome Except.isOk := by
    simp only [WellBehavedEvaluateQuery.Same]
    intro t εs r hwt hs
    cases r <;> simp only [Except.isOk, Except.toBool]
    case error =>
      replace ⟨_, hs⟩ := (same_error_implies hs).right
      subst hs
      simp only [pe_isSome_none, same_bool_def]
    case ok =>
      replace ⟨_, heq, hs⟩ := same_ok_implies hs
      subst heq
      simp only [pe_isSome_some, same_bool_def]
  simp only [WellBehavedEvaluateQuery, hwo, hi, hs, and_self]

theorem verifyAlwaysMatches_wbeq :
  WellBehavedEvaluateQuery (eq · (⊙true)) (· == .ok true)
:= by
  have hwo : WellBehavedEvaluateQuery.WellFormedOutput (eq · (⊙true)) := by
    simp only [WellBehavedEvaluateQuery.WellFormedOutput]
    intro _ _ hwt
    apply wf_eq hwt.left (Term.WellFormed.some_wf (wf_bool (b := true)))
    simp only [hwt.right, Term.typeOf, typeOf_bool]
  have hi : WellBehavedEvaluateQuery.Interpretable (eq · (⊙true)) := by
    simp only [WellBehavedEvaluateQuery.Interpretable, someOf]
    intro _ _ _ hwt hI
    have := interpret_eq hI hwt.left (Term.WellFormed.some_wf (wf_bool (b := true))) (t₂ := .some true)
    simp [interpret_term_some, interpret_term_prim] at this
    exact this
  have hs : WellBehavedEvaluateQuery.Same (eq · (⊙true)) (λ r => r == .ok true) := by
    simp only [WellBehavedEvaluateQuery.Same, someOf]
    intro t εs r hwt hs
    cases r
    case error =>
      replace ⟨_, hs⟩ := (same_error_implies hs).right
      subst hs
      simp only [pe_eq_none_some, same_bool_def, Term.prim.injEq, TermPrim.bool.injEq,
        Bool.false_eq, beq_eq_false_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true]
    case ok v =>
      replace ⟨t', heq, hs⟩ := same_ok_implies hs
      subst heq
      simp only [pe_eq_some_some]
      have hwt' : t'.WellFormed εs ∧ t'.typeOf = .bool := by
        simp [WellBehavedEvaluateQuery.WellFormedInput, Term.typeOf] at hwt
        simp [hwt, wf_term_some_implies]
      replace ⟨b, hv⟩ := value_type_bool_implies_bool hs hwt'.right
      subst hv
      replace hs := same_bool_implies hs
      rw [hs]
      simp only [same_bool_def, Term.bool]
      cases b
      case false =>
        show eq.simplify (.prim (.bool false)) (.prim (.bool true)) = .prim (.bool false)
        have := pe_eq_simplify_lit (t₁ := .prim (.bool false)) (t₂ := .prim (.bool true)) term_prim_is_lit term_prim_is_lit
        rw [this.right]
        rfl
      case true =>
        show eq.simplify (.prim (.bool true)) (.prim (.bool true)) = .prim (.bool true)
        exact pe_eq_simplify_same
  simp only [WellBehavedEvaluateQuery, hwo, hi, hs, and_self]

theorem verifyNeverMatches_wbeq :
  WellBehavedEvaluateQuery (λ t => not (eq t (⊙true))) (· != .ok true)
:= by
  have hwo : WellBehavedEvaluateQuery.WellFormedOutput (λ t => not (eq t (⊙true))) := by
    simp only [WellBehavedEvaluateQuery.WellFormedOutput]
    intro _ _ hwt
    have hwf_eq := wf_eq hwt.left (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by simp only [hwt.right, Term.typeOf, typeOf_bool])
    exact wf_not hwf_eq.left hwf_eq.right
  have hi : WellBehavedEvaluateQuery.Interpretable (λ t => not (eq t (⊙true))) := by
    simp only [WellBehavedEvaluateQuery.Interpretable, someOf]
    intro _ _ _ hwt hI
    have hwf_eq := wf_eq hwt.left (Term.WellFormed.some_wf (wf_bool (b := true)))
      (by simp only [hwt.right, Term.typeOf, typeOf_bool])
    rw [interpret_not hI hwf_eq.left, interpret_eq hI hwt.left (Term.WellFormed.some_wf (wf_bool (b := true)))]
    simp only [interpret_term_some, interpret_term_prim]
  have hs : WellBehavedEvaluateQuery.Same (λ t => not (eq t (⊙true))) (λ r => r != .ok true) := by
    simp only [WellBehavedEvaluateQuery.Same, someOf]
    intro t εs r hwt hs
    cases r
    case error =>
      replace ⟨_, hs⟩ := (same_error_implies hs).right
      subst hs
      simp only [pe_not_lit, pe_eq_none_some, same_bool_def, Term.bool]
      rfl
    case ok v =>
      replace ⟨t', heq, hs⟩ := same_ok_implies hs
      subst heq
      simp only [pe_eq_some_some]
      have hwt' : t'.WellFormed εs ∧ t'.typeOf = .bool := by
        simp [WellBehavedEvaluateQuery.WellFormedInput, Term.typeOf] at hwt
        simp [hwt, wf_term_some_implies]
      replace ⟨b, hv⟩ := value_type_bool_implies_bool hs hwt'.right
      subst hv
      replace hs := same_bool_implies hs
      rw [hs]
      simp only [same_bool_def, Term.bool]
      cases b
      case false =>
        show not (eq.simplify (.prim (.bool false)) (.prim (.bool true))) = .prim (.bool true)
        have := pe_eq_simplify_lit (t₁ := .prim (.bool false)) (t₂ := .prim (.bool true)) term_prim_is_lit term_prim_is_lit
        rw [this.right, pe_not_lit]
        rfl
      case true =>
        show not (eq.simplify (.prim (.bool true)) (.prim (.bool true))) = .prim (.bool false)
        rw [pe_eq_simplify_same, pe_not_lit]
        rfl
  simp only [WellBehavedEvaluateQuery, hwo, hi, hs, and_self]

end Cedar.Thm
