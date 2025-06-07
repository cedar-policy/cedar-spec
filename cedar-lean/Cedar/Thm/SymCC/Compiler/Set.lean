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

import Cedar.Thm.SymCC.Compiler.Args
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

/-!
This file proves the compilation lemmas for `.set` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem interpret_terms_wfls {ts : List Term} {ty : TermType} {I : Interpretation} {εs : SymEntities}
  (hI  : Interpretation.WellFormed I εs)
  (hwφ : ∀ t ∈ ts, Term.WellFormed εs t)
  (hty : ∀ t ∈ ts, Term.typeOf t = ty) :
  ∀ t ∈ ts, (t.interpret I).WellFormedLiteral εs ∧ (t.interpret I).typeOf = ty
:= by
  intro t ht
  have hw := interpret_term_wfl hI (hwφ t ht)
  simp only [hw, hty t ht, and_self]

theorem pe_interpret_terms_of_type_option {ts : List Term} {ty : TermType} {I : Interpretation} {εs : SymEntities}
  (hwi : ∀ t ∈ ts, (t.interpret I).WellFormedLiteral εs ∧ (t.interpret I).typeOf = .option ty) :
  (∃ ty, .none ty ∈ ts.map (Term.interpret I)) ∨
  (∃ ts', List.map (Term.interpret I) ts = List.map Term.some ts')
:= by
  generalize h₃ : (List.map (Term.interpret I) ts) = ts'
  have hn : ∀ t' ∈ ts', t'.WellFormedLiteral εs ∧ ∃ ty', t'.typeOf = .option ty' := by
    intro tᵢ hᵢ
    subst h₃
    simp only [List.mem_map] at hᵢ
    replace ⟨t', ht', hᵢ⟩ := hᵢ
    subst hᵢ
    simp only [hwi t' ht', TermType.option.injEq, exists_eq', and_self]
  replace hn := pe_wfls_of_type_option hn
  subst h₃
  exact hn

private theorem compile_interpret_set_ifAllSome {εs : SymEntities} {I : Interpretation} {ts : List Term} {ty : TermType}
  (hI  : Interpretation.WellFormed I εs)
  (hwφ : ∀ t ∈ ts, Term.WellFormed εs t)
  (hty : ∀ t ∈ ts, Term.typeOf t = TermType.option ty)
  (hwty : ty.WellFormed εs) :
  ifAllSome (ts.map (Term.interpret I))
    (Term.some (setOf (List.map (λ t => option.get (t.interpret I)) ts) ty)) =
  Term.interpret I (ifAllSome ts (Term.some (setOf (List.map option.get ts) ty)))
:= by
  have hwi := interpret_terms_wfls hI hwφ hty
  have hws := wf_some_setOf_map (wf_option_get_mem_of_type hwφ hty) hwty
  simp only [interpret_ifAllSome hI hwφ hws.left hws.right, interpret_term_some, interpret_setOf,
    List.map_map]
  generalize h₁ : Term.some (setOf (List.map (fun t => option.get (Term.interpret I t)) ts) ty) = t₁
  generalize h₂ : Term.some (setOf (List.map (Term.interpret I ∘ option.get) ts) ty) = t₂
  have hw₁ : t₁.WellFormed εs ∧ t₁.typeOf = .option (.set ty) := by
    subst h₁
    apply wf_some_setOf_map _ hwty
    intro t ht
    have hw := hwi t ht
    exact wf_option_get hw.left.left hw.right
  have hw₂ : t₂.WellFormed εs ∧ t₂.typeOf = .option (.set ty) := by
    subst h₂
    apply wf_some_setOf_map _ hwty
    intro t ht
    simp only [Function.comp_apply, interpret_option_get I (hwφ t ht) (hty t ht)]
    have hw := hwi t ht
    exact wf_option_get' hI hw.left.left hw.right
  have hn := pe_interpret_terms_of_type_option hwi
  rcases hn with ⟨_, hn⟩ | ⟨_, hn⟩
  case inl =>
    simp only [pe_ifAllSome_none hn hw₁.right, pe_ifAllSome_none hn hw₂.right]
  case inr =>
    simp only [hn, pe_ifAllSome_some hw₁.right, pe_ifAllSome_some hw₂.right]
    have heq : List.map (fun t => option.get (Term.interpret I t)) ts = List.map (Term.interpret I ∘ option.get) ts := by
      apply List.map_congr
      intro t h
      rw [← List.forall₂_iff_map_eq] at hn
      replace ⟨t', _, hn⟩ := List.forall₂_implies_all_left hn t h
      simp only [hn, pe_option_get_some, Function.comp_apply,
        interpret_option_get I (hwφ t h) (hty t h), pe_option_get'_some]
    simp only [← h₁, heq, ← h₂]

theorem compile_interpret_set {xs : List Expr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.set xs))
  (hok : compile (.set xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpret x) :
  compile (.set xs) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨ts, hok, ht⟩ := compile_set_ok_implies hok
  replace ⟨ty, hd, tl, hcons, hty, ht⟩ := compileSet_ok_implies ht
  subst ht hcons
  replace hwε := wf_εnv_for_set_implies hwε
  have hwφ := compile_wfs hwε hok
  replace ih := compile_interpret_ihs hI hwε ih hok
  simp only [compile, List.mapM₁_eq_mapM (fun x => compile x (SymEnv.interpret I εnv))]
  simp_do_let (List.mapM (fun x => compile x (SymEnv.interpret I εnv)) xs)
  case error h =>
    exact compile_interpret_args_not_error ih h
  case ok hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    unfold compileSet
    split
    case h_1 =>
      rw [List.forall₂_nil_right_iff] at hok'
      subst hok'
      rw [List.forall₂_nil_left_iff] at hok
      contradiction
    case h_2 ts' hd' tl' =>
      replace ih := compile_interpret_terms ih hok'
      clear hok'
      have hwφ' : ∀ (t' : Term), t' ∈ hd' :: tl' → t'.WellFormed εnv.entities ∧ Term.typeOf t' = TermType.option ty := by
        intro t' ht'
        replace ⟨t, ht, ih'⟩ := List.forall₂_implies_all_right ih t' ht'
        subst ih'
        rw [← hty t ht]
        exact interpret_term_wf hI (hwφ t ht)
      have hwφₕ' := hwφ' hd' (by simp only [List.mem_cons, true_or])
      simp only [hwφₕ'.right, List.all_cons, decide_true, Bool.true_and, List.all_eq_true,
        decide_eq_true_eq, List.map_cons]
      split
      case isTrue =>
        simp only [Except.ok.injEq, someOf]
        rw [List.forall₂_iff_map_eq] at ih
        simp only [List.map_cons, List.map_id', List.cons.injEq] at ih
        replace ⟨ih, ihₜ⟩ := ih ; subst ih ihₜ
        rw [← List.map_cons, ← List.map_cons, ← List.map_cons, ← List.map_cons, List.map_map]
        have hwty := typeOf_option_wf_terms_is_wf rfl hwφ hty
        exact compile_interpret_set_ifAllSome hI hwφ hty hwty
      case isFalse h =>
        simp only [Classical.not_forall, exists_prop] at h
        replace ⟨t', h⟩ := h
        specialize hwφ' t' (by simp only [h.left, List.mem_cons, or_true])
        simp only [hwφ', not_true_eq_false, and_false] at h

private theorem compile_evaluate_list {xs : List Expr} {ts : List Term} {vs : List Value} {env : Env}
  (h₁ : List.Forall₂ (λ x t => evaluate x env.request env.entities ∼ t) xs ts)
  (h₂ : List.Forall₂ (λ x v => evaluate x env.request env.entities = Except.ok v) xs vs) :
  ∃ (ts' : List Term),
    ts = ts'.map Term.some ∧
    List.Forall₂ (λ t v => v ∼ t) ts' vs
:= by
  cases xs
  case nil =>
    rw [List.forall₂_nil_left_iff] at h₁ h₂
    subst h₁ h₂
    exists []
    simp only [List.map_nil, List.Forall₂.nil, and_self]
  case cons xhd xtl =>
    replace ⟨thd, ttl, h₁, htl₁, hts⟩ := List.forall₂_cons_left_iff.mp h₁
    replace ⟨vhd, vtl, h₂, htl₂, hvs⟩ := List.forall₂_cons_left_iff.mp h₂
    subst hts hvs
    have ⟨tl', ih⟩ := compile_evaluate_list htl₁ htl₂
    simp only [h₂] at h₁
    replace ⟨hd', h₁⟩ := same_ok_implies h₁
    exists (hd' :: tl')
    simp only [h₁, ih, List.map_cons, List.forall₂_cons, and_self]

private theorem same_forall₂_implies_same_set {ts : List Term} {vs : List Value} {ty : TermType}
  (hs : List.Forall₂ (λ t v => v ∼ t) ts vs) :
  Term.value? (Term.set (Set.make ts) ty) = some (Value.set (Set.make vs))
:= by
  unfold Term.value?
  simp only [List.mapM₁_eq_mapM, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Value.set.injEq]
  simp only [same_values_def] at hs
  have heqv := List.canonicalize_equiv ts
  have ⟨vs', hts⟩ : ∃ vs', List.mapM Term.value? (List.canonicalize id ts) = some vs' := by
    rw [← List.mapM_some_iff_forall₂] at hs
    exact List.mapM_some_subset hs heqv.right
  have hts' := hts
  unfold id at hts'
  exists vs'
  rw [Set.make]
  simp only [hts', true_and]
  clear hts'
  rw [List.mapM_some_iff_forall₂] at hts
  rw [Set.make_make_eqv]
  apply List.Equiv.symm
  apply List.forall₂_fun_equiv_implies hs hts _ heqv
  intro t v v' hv hv'
  simp only [hv, Option.some.injEq] at hv'
  exact hv'

theorem compile_evaluate_set {xs : List Expr} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.set xs))
  (hwε : εnv.WellFormedFor (.set xs))
  (hok : compile (.set xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileEvaluate x) :
  evaluate (.set xs) env.request env.entities ∼ t
:= by
  replace ⟨ts, hok, ht⟩ := compile_set_ok_implies hok
  replace ⟨ty, hd, tl, hcons, hty, ht⟩ := compileSet_ok_implies ht
  subst ht hcons
  replace hwε := wf_εnv_for_set_implies hwε
  have hwφ := compile_wfs hwε hok
  replace hwe := wf_env_for_set_implies hwe
  replace ih := compile_evaluate_ihs heq hwe hwε ih hok
  simp only [evaluate, List.mapM₁_eq_mapM λ x => evaluate x env.request env.entities]
  simp_do_let (List.mapM (fun x => evaluate x env.request env.entities) xs)
  case error h =>
    replace ⟨x, hx, h⟩ := List.mapM_error_implies_exists_error h
    replace ⟨_, ht, ih⟩ := List.forall₂_implies_all_left ih x hx
    rw [h] at ih
    exact same_error_implies_ifAllSome_error ih ht typeOf_term_some
  case ok vs hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    replace ⟨ts', hts, ih⟩ := compile_evaluate_list ih hok'
    clear hok'
    simp only [hts, List.map_map, Function.comp_def, pe_option_get_some, List.map_id'] at *
    simp only [Same.same, SameResults, pe_ifAllSome_some typeOf_term_some, SameValues]
    simp only [setOf, same_forall₂_implies_same_set ih]

end Cedar.Thm
