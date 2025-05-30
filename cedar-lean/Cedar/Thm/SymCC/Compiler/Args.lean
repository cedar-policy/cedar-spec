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

import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

/-!
This file contains utility lemmas for proving reduction theorems
about lists of argument terms.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem compile_wfs {xs : List Expr} {εnv : SymEnv} {ts : List Term}
  (hwφ : ∀ (x : Expr), x ∈ xs → SymEnv.WellFormedFor εnv x)
  (hok : List.Forall₂ (λ x t => compile x εnv = Except.ok t) xs ts) :
  ∀ t ∈ ts, t.WellFormed εnv.entities
:= by
  intro t ht
  replace ⟨x, hx, hok⟩ := List.forall₂_implies_all_right hok t ht
  exact (compile_wf (hwφ x hx) hok).left

theorem compile_interpret_ihs {xs : List Expr} {εnv : SymEnv} {I : Interpretation} {ts : List Term}
  (hI  : Interpretation.WellFormed I εnv.entities)
  (hwε : ∀ (x : Expr), x ∈ xs → SymEnv.WellFormedFor εnv x)
  (ih  : ∀ (x : Expr), x ∈ xs → ReduceInterpret x)
  (hok : List.Forall₂ (fun x t => compile x εnv = Except.ok t) xs ts) :
  List.Forall₂ (fun x t => compile x (SymEnv.interpret I εnv) = Except.ok (Term.interpret I t)) xs ts
:= by
  cases xs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    assumption
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨thd, hok, ttl, htl, hts⟩ := hok
    subst hts
    exists thd
    simp only [ih.left hI hwε.left hok, List.cons.injEq, true_and]
    exists ttl
    simp only [and_true]
    exact compile_interpret_ihs hI hwε.right ih.right htl

theorem compile_interpret_args_not_error {εnv : SymEnv} {I : Interpretation} {xs : List Expr} {ts : List Term} {e : SymCC.Error} :
  List.Forall₂ (fun x t => compile x (SymEnv.interpret I εnv) = Except.ok (Term.interpret I t)) xs ts →
  List.mapM (fun x => compile x (SymEnv.interpret I εnv)) xs = Except.error e →
  False
:= by
  intro ih h
  replace ⟨x, hmem, h⟩ := List.mapM_error_implies_exists_error h
  replace ⟨_, _, ih⟩ := List.forall₂_implies_all_left ih x hmem
  simp only [h, reduceCtorEq] at ih

theorem compile_interpret_terms {xs : List Expr} {εnv : SymEnv} {I : Interpretation} {ts ts' : List Term}
  (h₁ : List.Forall₂ (λ x t => compile x (SymEnv.interpret I εnv) = Except.ok (Term.interpret I t)) xs ts)
  (h₂ : List.Forall₂ (λ x t => compile x (SymEnv.interpret I εnv) = Except.ok t) xs ts') :
  List.Forall₂ (λ t t' => Term.interpret I t = t') ts ts'
:= by
  rw [List.forall₂_iff_map_eq] at h₁ h₂
  rw [h₁, ← List.forall₂_iff_map_eq] at h₂
  simp only [Except.ok.injEq] at h₂
  exact h₂

theorem compile_evaluate_ihs {xs : List Expr} {env : Env} {εnv : SymEnv}
  (heq : env ∼ εnv)
  (hwe : ∀ (x : Expr), x ∈ xs → env.WellFormedFor x)
  (hwε : ∀ (x : Expr), x ∈ xs → εnv.WellFormedFor x)
  (ih  : ∀ (x : Expr), x ∈ xs → ReduceEvaluate x)
  (hok : List.Forall₂ (fun x t => compile x εnv = Except.ok t) xs ts) :
  List.Forall₂ (fun x t => evaluate x env.request env.entities ∼ t) xs ts
:= by
  cases xs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    assumption
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨thd, hok, ttl, htl, hts⟩ := hok
    subst hts
    exists thd
    simp only [ih.left heq hwe.left hwε.left hok, List.cons.injEq, true_and]
    exists ttl
    simp only [and_true]
    exact compile_evaluate_ihs heq hwe.right hwε.right ih.right htl

end Cedar.Thm
