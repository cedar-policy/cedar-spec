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
  WellBehavedEvaluateQuery (eq · (⊙true)) (λ r => r == .ok true)
:= by
  sorry

theorem verifyNeverMatches_wbeq :
  WellBehavedEvaluateQuery (λ t => not (eq t (⊙true))) (λ r => r != .ok true)
:= by
  sorry

end Cedar.Thm
