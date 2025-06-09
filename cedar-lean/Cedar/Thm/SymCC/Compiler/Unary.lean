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
This file proves the compilation lemmas for `.unaryApp` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

private theorem compileApp₁_implies_apply₁ {op₁ : UnaryOp} {v₁ : Value} {t₁ t₂ : Term} {εs : SymEntities}
  (hwφ₁ : Term.WellFormed εs t₁)
  (ih : v₁ ∼ t₁)
  (hr : compileApp₁ op₁ t₁ = Except.ok t₂) :
  apply₁ op₁ v₁ ∼ t₂
:= by
  have hwfl : t₁.WellFormedLiteral εs := And.intro hwφ₁ (same_value_implies_lit ih)
  replace hr := compileApp₁_ok_implies hr
  simp only [apply₁]
  cases op₁ <;>
  simp only at hr
  case not =>
    have ⟨_, h⟩ := wfl_of_type_bool_is_bool hwfl hr.left
    subst h
    replace ih := same_bool_term_implies ih
    simp only [Same.same, SameResults, ih, hr.right, pe_not_lit, ne_eq]
    exact same_implies_same_value same_bool
  case neg =>
    have ⟨bv, h⟩ := wfl_of_type_bitvec_is_bitvec hwfl hr.left
    subst h
    replace ⟨i, ih, hi⟩ := same_bitvec64_term_implies ih
    simp only [ih, hr.right, bvnego, bvneg, hi, Int64.neg?, Int64.ofInt?]
    split <;> rename_i h
    case isTrue =>
      simp only [Same.same, SameResults, intOrErr, BitVec.overflows_false_64 h, BitVec.neg_eq,
        pe_ifFalse_false]
      apply same_implies_same_value
      exact same_int h (BitVec.neg_toInt_eq_neg_64 h hi)
    case isFalse =>
      simp only [Same.same, SameResults, intOrErr, BitVec.overflows_true_64 h,
        pe_ifFalse_true, ne_eq, not_false_eq_true, reduceCtorEq]
  case like =>
    have ⟨_, h⟩ := wfl_of_type_string_is_string hwfl hr.left
    subst h
    replace ih := same_string_term_implies ih
    simp only [Same.same, SameResults, ih, hr.right, string.like, ne_eq]
    exact same_implies_same_value same_bool
  case is =>
    replace ⟨_, hr⟩ := hr
    have ⟨_, huid, hty⟩ := wfl_of_type_entity_is_entity hwfl hr.left
    subst huid hty
    replace ih := same_entity_term_implies ih
    simp only [Same.same, SameResults, ih, hr.right, ne_eq]
    exact same_implies_same_value same_bool
  case isEmpty =>
    replace ⟨⟨_, hty⟩, hr⟩ := hr
    have ⟨ts, hs⟩ := wfl_of_type_set_is_set hwfl hty
    subst hs hr
    replace ⟨vs, hv, ih⟩ := same_set_term_implies ih
    subst hv
    simp only [pe_set_isEmpty, ← same_ok_bool_iff]
    cases h : ts.isEmpty
    case false =>
      replace h : ¬ ts.isEmpty := by simp only [h, Bool.false_eq_true, not_false_eq_true]
      rw [Set.non_empty_iff_exists] at h
      replace ⟨t, h⟩ := h
      replace ⟨v, ih, _⟩ := set_value?_implies_in_value ih t h
      replace ih : ∃ v, v ∈ vs := by exists v
      simp only [← Set.non_empty_iff_exists, Bool.not_eq_true] at ih
      exact ih
    case true =>
      simp only [Set.empty_iff_not_exists, not_exists] at h
      by_contra hc
      rw [Set.non_empty_iff_exists] at hc
      replace ⟨v, hc⟩ := hc
      replace ⟨t, ih, _⟩ := set_value?_implies_in_term ih v hc
      specialize h t ih
      contradiction

theorem compile_evaluate_unaryApp {op₁ : UnaryOp} {x₁ : Expr} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.unaryApp op₁ x₁))
  (hwε : εnv.WellFormedFor (.unaryApp op₁ x₁))
  (hok : compile (.unaryApp op₁ x₁) εnv = .ok t)
  (ih  : CompileEvaluate x₁) :
  evaluate (.unaryApp op₁ x₁) env.request env.entities ∼ t
:= by
  replace ⟨t₁, t₂, hok, hr, ht⟩ := compile_unaryApp_ok_implies hok
  subst ht
  replace hwε := wf_εnv_for_unaryApp_implies hwε
  have ⟨hwφ₁, _, hty₁⟩ := compile_wf hwε hok
  replace ih := ih heq (wf_env_for_unaryApp_implies hwe) hwε hok
  have hwo := wf_option_get hwφ₁ hty₁
  have ⟨_, ty₂, hty₂⟩ := compileApp₁_wf hwo.left hr
  unfold evaluate
  simp_do_let (evaluate x₁ env.request env.entities)
  case error e he =>
    rw [he] at ih
    exact same_error_implies_ifSome_error ih hty₂
  case ok v₁ hv₁ =>
    rw [hv₁] at ih
    replace ⟨t₁', ht₁, ih⟩ := same_ok_implies ih
    subst ht₁
    simp only [pe_ifSome_some hty₂]
    simp only [pe_option_get_some] at hr
    exact compileApp₁_implies_apply₁ (wf_term_some_implies hwφ₁) ih hr

theorem interpret_compileApp₁ {op₁ : UnaryOp} {t t₁: Term} {εs : SymEntities} {I : Interpretation}
  (hI  : Interpretation.WellFormed I εs)
  (hwt : Term.WellFormed εs t₁)
  (hok : compileApp₁ op₁ t₁ = Except.ok t) :
  compileApp₁ op₁ (t₁.interpret I) = .ok (t.interpret I)
:= by
  have hwt' := interpret_term_wfl hI hwt
  replace hok := compileApp₁_ok_implies hok
  simp only [compileApp₁, hwt'.right]
  cases op₁ <;>
  simp only at hok
  case not =>
    simp only [hok, someOf, interpret_term_some, interpret_not hI hwt]
  case neg =>
    have hwt₁ := wf_bvnego hwt hok.left
    have hwt₂ := wf_bvneg hwt hok.left
    simp only [hok, someOf,
      interpret_ifFalse hI hwt₁.left hwt₁.right hwt₂.left,
      interpret_bvnego hI hwt hok.left,
      interpret_bvneg hI hwt hok.left]
  case like =>
    simp only [hok, someOf, interpret_term_some, interpret_string_like hI hwt hok.left]
  case is =>
    replace ⟨ety₂, hok⟩ := hok
    simp only [hok, someOf, interpret_term_some, interpret_term_prim]
  case isEmpty =>
    replace ⟨⟨_, hty⟩, hok⟩ := hok
    simp only [hty, someOf, hok, interpret_term_some, interpret_set_isEmpty hI hwt hty]

private theorem compileApp₁_ok_typeOf {op₁ : UnaryOp} {t₁ t₁' t₂ : Term}
  (hty : t₁.typeOf = t₂.typeOf)
  (hok : compileApp₁ op₁ t₁ = Except.ok t₁') :
  ∃ t₂', compileApp₁ op₁ t₂ = Except.ok t₂'
:= by
  replace hok := compileApp₁_ok_implies hok
  simp only [compileApp₁, ← hty]
  split at hok <;>
  try (simp only [hok.left, Except.ok.injEq, exists_eq'])
  case _ =>
    replace ⟨ety₂, hok⟩ := hok
    simp only [hok.left, Except.ok.injEq, exists_eq']
  case _ =>
    replace ⟨⟨_, hty⟩, _⟩ := hok
    simp only [hty, Except.ok.injEq, exists_eq']

private theorem compileApp₁_ok_typeOf_eq {op₁ : UnaryOp} {t₁ t₁' t₂ t₂' : Term} {εs : SymEntities}
  (hw₁ : t₁.WellFormed εs)
  (hw₂ : t₂.WellFormed εs)
  (hok₁ : compileApp₁ op₁ t₁ = Except.ok t₁')
  (hok₂ : compileApp₁ op₁ t₂ = Except.ok t₂') :
  t₁'.typeOf = t₂'.typeOf
:= by
  replace hw₁ := (compileApp₁_wf_types hw₁ hok₁).right
  replace hw₂ := (compileApp₁_wf_types hw₂ hok₂).right
  cases op₁
  all_goals {
    simp only at hw₁ hw₂
    simp only [hw₁, hw₂]
  }

theorem compile_interpret_unaryApp {op₁ : UnaryOp} {x₁ : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.unaryApp op₁ x₁))
  (hok : compile (.unaryApp op₁ x₁) εnv = .ok t)
  (ih  : CompileInterpret x₁) :
  compile (.unaryApp op₁ x₁) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨t₁, t₂, hok, ha, ht⟩ := compile_unaryApp_ok_implies hok
  subst ht
  have hwφ₁ := wf_εnv_for_unaryApp_implies hwε
  replace ih := ih hI hwφ₁ hok
  replace ⟨hwφ₁, ty₁, hty₁⟩ := compile_wf hwφ₁ hok
  have hwo := wf_option_get hwφ₁ hty₁
  have hwφ₁' := interpret_term_wfl hI hwφ₁
  rw [hty₁] at hwφ₁'
  have hwo' := wf_option_get hwφ₁'.left.left hwφ₁'.right
  rw [eq_comm, ← hwo.right] at hwo'
  simp only [compile, ih, Except.bind_ok]
  have hi := interpret_compileApp₁ hI hwo.left ha
  simp_do_let (compileApp₁ op₁ (option.get (Term.interpret I t₁))) <;>
  rename_i heq
  case error =>
    have ⟨_, hok'⟩ := compileApp₁_ok_typeOf hwo'.right ha
    simp only [heq, reduceCtorEq] at hok'
  case ok t₃ =>
    have ⟨hwφ₂, ty₂, hty₂⟩ := compileApp₁_wf hwo.left ha
    simp only [interpret_ifSome hI hwφ₁ hwφ₂, Except.ok.injEq]
    rw [interpret_option_get I hwφ₁ hty₁] at hi
    have hty₃ := compileApp₁_ok_typeOf_eq hwo.left hwo'.left ha heq
    rw [eq_comm, hty₂] at hty₃
    rw [← (interpret_term_wf hI hwφ₂).right] at hty₂
    exact pe_ifSome_ok_get_eq_get' I (compileApp₁ op₁) hwφ₁' hty₂ hty₃ hi heq

end Cedar.Thm
