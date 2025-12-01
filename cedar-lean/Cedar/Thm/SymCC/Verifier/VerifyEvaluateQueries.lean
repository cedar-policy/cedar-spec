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
    apply wf_eq hwt.left (Term.WellFormed.some_wf wf_bool)
    simp only [hwt.right, typeOf_term_some, typeOf_bool]
  have hi : WellBehavedEvaluateQuery.Interpretable (eq · (⊙true)) := by
    simp only [WellBehavedEvaluateQuery.Interpretable, someOf]
    intro _ _ _ hwt hI
    have := interpret_eq hI hwt.left (Term.WellFormed.some_wf wf_bool) (t₂ := .some true)
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
      replace ⟨_, heq, hs⟩ := same_ok_implies hs
      subst heq
      simp only [pe_eq_some_some]
      cases v <;> simp only [Value.prim.injEq] at hs
      case prim p =>
        cases p <;> simp only at hs
        case bool b =>
          subst hs
          cases b <;> simp only [pe_eq_prim, Term.bool, beq_self_eq_true, beq_false_right]
  simp only [WellBehavedEvaluateQuery, hwo, hi, hs, and_self]

theorem verifyNeverMatches_wbeq :
  WellBehavedEvaluateQuery (λ t => not (eq t (⊙true))) (· != .ok true)
:= by
  have hwo : WellBehavedEvaluateQuery.WellFormedOutput (λ t => not (eq t (⊙true))) := by
    simp only [WellBehavedEvaluateQuery.WellFormedOutput]
    intro _ _ hwt
    have hwf_eq := wf_eq hwt.left (Term.WellFormed.some_wf wf_bool)
      (by simp only [hwt.right, typeOf_term_some, typeOf_bool])
    exact wf_not hwf_eq.left hwf_eq.right
  have hi : WellBehavedEvaluateQuery.Interpretable (λ t => not (eq t (⊙true))) := by
    simp only [WellBehavedEvaluateQuery.Interpretable]
    intro _ _ _ hwt hI
    have hwf_eq := wf_eq hwt.left (Term.WellFormed.some_wf wf_bool)
      (by simp only [hwt.right, typeOf_term_some, typeOf_bool])
    exact interpret_not hI hwf_eq.left
  have hs : WellBehavedEvaluateQuery.Same (λ t => not (eq t (⊙true))) (λ r => r != .ok true) := by
    simp only [WellBehavedEvaluateQuery.Same]
    intro t εs r hwt hs
    cases r <;> simp only [bne_iff_ne, ne_eq]
    case error =>
      replace ⟨_, hs⟩ := (same_error_implies hs).right
      subst hs
      simp only [pe_not_lit, pe_eq_none_some, same_bool_def, Bool.not_false]
    case ok v =>
      replace ⟨_, heq, hs⟩ := same_ok_implies hs
      subst heq
      simp only [same_bool_def] at hs
      cases v <;> simp only [Value.prim.injEq] at hs
      case prim p =>
        cases p <;> simp only at hs
        case bool b =>
          subst hs
          cases b <;> simp only [pe_not_lit, pe_eq_prim, Term.bool, beq_self_eq_true,
            beq_false_right, Bool.not_true, Bool.not_false, same_bool_def]
  simp only [WellBehavedEvaluateQuery, hwo, hi, hs, and_self]

end Cedar.Thm
