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

import Cedar.Thm.SymCC.Compiler

/-!
This file proves auxiliary lemmas about `Asserts`, which are lists of
(well-formed) boolean Terms.
--/

namespace Cedar.Thm

open Spec SymCC

theorem asserts_satisfiedBy_true {I : Interpretation} {asserts : Asserts} :
  asserts.satisfiedBy I ↔
  ∀ t ∈ asserts, t.interpret I = true
:= by
  simp only [Asserts.satisfiedBy, List.all_eq_true, decide_eq_true_eq]

theorem asserts_satisfiable_def {εnv : SymEnv} {asserts : Asserts} :
  (εnv ⊧ asserts) ↔
  ∃ I, I.WellFormed εnv.entities ∧ ∀ t ∈ asserts, t.interpret I = true
:= by
  simp only [Asserts.Satisfiable, asserts_satisfiedBy_true]

theorem asserts_unsatisfiable_def {εnv : SymEnv} {asserts : Asserts} :
  (εnv ⊭ asserts) ↔
  ∀ I, I.WellFormed εnv.entities → ∃ t ∈ asserts, t.interpret I ≠ true
:= by
  simp only [Asserts.Unsatisfiable, asserts_satisfiable_def, not_exists, not_and,
    Classical.not_forall, not_imp, ne_eq, exists_prop]

theorem asserts_last_not_true {I : Interpretation} {ts : Asserts} {t t' : Term} :
  ts.satisfiedBy I →
  t ∈ ts ++ [t'] →
  t.interpret I ≠ Term.prim (TermPrim.bool true) →
  t = t'
:= by
  intro h₁ h₂ h₃
  rw [asserts_satisfiedBy_true] at h₁
  simp only [List.mem_append, List.mem_singleton] at h₂
  rcases h₂ with h₂ | h₂ <;> try exact h₂
  specialize h₁ t h₂
  contradiction

theorem asserts_all_true {I : Interpretation} {ts : Asserts} {t' : Term} :
  (∀ t ∈ ts ++ [t'], t.interpret I = true) →
  ts.satisfiedBy I ∧ t'.interpret I = true
:= by
  intro h
  constructor
  · rw [asserts_satisfiedBy_true]
    intro t ht
    apply h
    simp only [List.mem_append, ht, List.mem_singleton, true_or]
  · apply h
    simp only [List.mem_append, List.mem_singleton, or_true]

end Cedar.Thm
