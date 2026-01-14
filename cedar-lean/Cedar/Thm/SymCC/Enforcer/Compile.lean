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

import Cedar.SymCC.Enforcer
import Cedar.Thm.SymCC.Concretizer
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Env.SWF
import Cedar.Thm.SymCC.Enforcer.Asserts
import Cedar.Thm.SymCC.Enforcer.Footprint
import Cedar.Thm.SymCC.Enforcer.Util
import Cedar.Thm.SymCC.Compiler

/-!
This file proves that a term produced by compiling an expression `x`
has the same value under interpretations `I₁` and `I₂` that agree
on the footprint of `x`.  See `compile_interpret_on_footprint`.

This proof relies on the theorem `compile_interpret_in_footprint`, which says
that every entity produced by interpreting a subexpression of `x` is
in the footprint of `x`.
--/


namespace Cedar.Thm

open Data Spec SymCC Factory

-------------------

private theorem compile_isOptionEntityType {x : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor x)
  (hI  : I.WellFormed εnv.entities)
  (hok : compile x εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  t.typeOf.isOptionEntityType
:= by
  have hwt := (compile_wf hwε hok).left
  have hty := (interpret_term_wf hI hwt).right
  rw [ht] at hty
  rw [← hty]
  simp only [TermType.isOptionEntityType, Term.typeOf, TermPrim.typeOf]

private theorem typeOf_ifSome_ite_option_bool {t₁ t₂ t₃ : Term} {εs : SymEntities} :
  t₁.WellFormed εs → t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .option .bool → t₂.typeOf = .option .bool → t₃.typeOf = .option .bool →
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).typeOf = .option .bool
:= by
  intro hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty₃
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwi := wf_ite hwo₁.left hwt₂ hwt₃ hwo₁.right (by simp only [hty₂, hty₃])
  rw [hty₂] at hwi
  simp only [wf_ifSome_option hwt₁ hwi.left hwi.right]

private theorem typeOf_compile_and_option_bool {x₁ x₂ : Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.and x₁ x₂))
  (hok : compile (.and x₁ x₂) εnv = .ok t) :
  t.typeOf = .option .bool
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_and_ok_implies hok
  split at hok
  · subst hok
    simp only [typeOf_term_some, typeOf_bool]
  · replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    try have hwε := wf_εnv_for_and_implies hwε
    try have hwε := wf_εnv_for_or_implies hwε
    have hwt₁ := (compile_wf hwε.left hok₁).left
    have hwt₂ := (compile_wf hwε.right hok₂).left
    exact typeOf_ifSome_ite_option_bool hwt₁ hwt₂ (Term.WellFormed.some_wf wf_bool) hty₁ hty₂ (by simp only [typeOf_term_some, typeOf_bool])

private theorem typeOf_compile_or_option_bool {x₁ x₂ : Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.or x₁ x₂))
  (hok : compile (.or x₁ x₂) εnv = .ok t) :
  t.typeOf = .option .bool
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_or_ok_implies hok
  split at hok
  · subst hok
    simp only [typeOf_term_some, typeOf_bool]
  · replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    try have hwε := wf_εnv_for_and_implies hwε
    try have hwε := wf_εnv_for_or_implies hwε
    have hwt₁ := (compile_wf hwε.left hok₁).left
    have hwt₂ := (compile_wf hwε.right hok₂).left
    exact typeOf_ifSome_ite_option_bool hwt₁ (Term.WellFormed.some_wf wf_bool) hwt₂ hty₁ (by simp only [typeOf_term_some, typeOf_bool]) hty₂

private theorem typeOf_compile_unaryApp_option_types {op₁ : UnaryOp} {x₁ : Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.unaryApp op₁ x₁))
  (hok : compile (.unaryApp op₁ x₁) εnv = .ok t) :
  t.typeOf = .option .bool ∨ t.typeOf = .option (.bitvec 64)
:= by
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_unaryApp_ok_implies hok
  subst heq
  have ⟨ty₁, ⟨hwt₁, _⟩, hwo₁⟩ := compile_option_get_wf (wf_εnv_for_unaryApp_implies hwε) hok₁
  have ⟨hwt₂, hty₂⟩ := compileApp₁_wf_types hwo₁.left hok
  split at hty₂ <;>
  simp only [wf_ifSome_option hwt₁ hwt₂ hty₂, TermType.option.injEq, TermType.prim.injEq, or_true, or_false, reduceCtorEq]

private theorem typeOf_compile_hasAttr_option_bool {x : Expr} {a : Attr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.hasAttr x a))
  (hok : compile (.hasAttr x a) εnv = .ok t) :
  t.typeOf = .option .bool
:= by
  replace ⟨_, _, hok₁, hok, heq⟩ := compile_hasAttr_ok_implies hok
  subst heq
  have ⟨_, ⟨hwt₁, _⟩, hwo₁⟩ := compile_option_get_wf (wf_εnv_for_hasAttr_implies hwε) hok₁
  have ⟨hwt₂, hty₂⟩ := compileHasAttr_wf hwε.left.right hwo₁.left hok
  simp only [wf_ifSome_option hwt₁ hwt₂ hty₂]

private theorem typeOf_compile_set_option_set {xs : List Expr} {t : Term} {εnv : SymEnv}
  (hok : compile (.set xs) εnv = .ok t) :
  ∃ ty, t.typeOf = .option (.set ty)
:= by
  replace ⟨ts, _, hok⟩ := compile_set_ok_implies hok
  replace ⟨ty, _, _, _, _, hok⟩ := compileSet_ok_implies hok
  subst hok
  exists ty
  apply typeOf_ifAllSome_option_type
  simp only [setOf, Term.typeOf]

private theorem typeOf_compile_record_option_record {axs : List (Attr × Expr)} {t : Term} {εnv : SymEnv}
  (hok : compile (.record axs) εnv = .ok t) :
  ∃ rty, t.typeOf = .option (.record rty)
:= by
  replace ⟨ts, _, hok⟩ := compile_record_ok_implies hok
  subst hok
  simp only [compileRecord, someOf, recordOf]
  have ⟨rty, hty⟩ := @typeOf_term_record_is_record_type (Map.make (List.map (Prod.map id option.get) ts))
  exists rty
  apply typeOf_ifAllSome_option_type
  simp only [typeOf_term_some, hty]

private theorem typeOf_compile_call_option_types {xfn : ExtFun} {xs : List Expr} {t : Term} {εnv : SymEnv}
  (hwε : εnv.WellFormedFor (.call xfn xs))
  (hok : compile (.call xfn xs) εnv = .ok t) :
  t.typeOf = .option .bool ∨ (∃ xty, t.typeOf = .option (.ext xty)) ∨ t.typeOf = .option (.bitvec 64)
:= by
  replace ⟨ts, ha, hok⟩ := compile_call_ok_implies hok
  replace ha := List.forall₂_implies_all_right ha
  replace hwε := wf_εnv_for_call_implies hwε
  have hwf : ∀ t ∈ ts, t.WellFormed εnv.entities := by
    intro t ht
    replace ⟨x, ha, hr⟩ := ha t ht
    simp only [compile_wf (hwε x ha) hr]
  have ⟨_, hty⟩ := compileCall_wf_types hwf hok
  split at hty <;>
  simp only [hty, TermType.option.injEq, TermType.prim.injEq,
    TermPrimType.ext.injEq, exists_eq', or_true, exists_const, or_false, reduceCtorEq]

private theorem compile_interpret_lit_in_footprint {p : Prim} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor (Expr.lit p))
  (hI  : I.WellFormed εnv.entities)
  (hok : compile (Expr.lit p) εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  ∃ tₑ ∈ footprint (Expr.lit p) εnv, tₑ.interpret I = .some (.entity uid)
:= by
  have hok' := hok
  have hty := compile_isOptionEntityType hwε hI hok ht
  simp only [compile, compilePrim] at hok
  cases p <;> simp only [someOf, Except.ok.injEq] at hok
  case bool | int | string =>
    subst hok
    simp only [TermType.isOptionEntityType, Term.typeOf, TermPrim.typeOf, Bool.false_eq_true] at hty
  case entityUID uid' =>
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    simp only [interpret_term_some, interpret_term_prim, Term.some.injEq, Term.prim.injEq,
      TermPrim.entity.injEq] at ht
    subst ht
    exists (Term.some (Term.entity uid'))
    simp only [footprint, footprint.ofEntity, hok', TermType.isOptionEntityType, Term.typeOf,
      TermPrim.typeOf, ↓reduceIte, Set.mem_singleton_iff_eq, interpret_term_some,
      interpret_term_prim, and_self]

private theorem compile_interpret_var_in_footprint {v : Var} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor (Expr.var v))
  (hI  : I.WellFormed εnv.entities)
  (hok : compile (Expr.var v) εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  ∃ tₑ ∈ footprint (Expr.var v) εnv, tₑ.interpret I = .some (.entity uid)
:= by
  have hok' := hok
  have hty := compile_isOptionEntityType hwε hI hok ht
  simp only [compile, compileVar] at hok
  cases v <;>
  simp only [someOf] at hok <;>
  split at hok <;>
  simp only [Except.ok.injEq, reduceCtorEq] at hok <;>
  subst hok
  case principal | action | resource =>
    simp only [interpret_term_some, Term.some.injEq] at ht
    simp only [footprint, footprint.ofEntity, hok', hty, ↓reduceIte, Set.mem_singleton_iff_eq,
      exists_eq_left, interpret_term_some, ht]
  case context hty' =>
    cases h : εnv.request.context.typeOf <;>
    simp only [TermType.isRecordType, h, Bool.false_eq_true] at hty'
    simp only [TermType.isOptionEntityType, typeOf_term_some, h, Bool.false_eq_true] at hty

private theorem interpret_ifSome_ite_eq_implies {t₁ t₂ t₃ t₄ : Term} {ty : TermType} {I : Interpretation} {εs : SymEntities} :
  I.WellFormed εs → t₁.WellFormed εs → t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .option .bool → t₂.typeOf = .option ty → t₂.typeOf = t₃.typeOf →
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).interpret I = t₄.some →
  t₂.interpret I = t₄.some ∨ t₃.interpret I = t₄.some
:= by
  intro hI hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty heq
  have hwo₁ := wf_option_get hwt₁ hty₁
  have hwi := wf_ite hwo₁.left hwt₂ hwt₃ hwo₁.right hty
  rw [hty₂] at hwi
  have hlit := interpret_term_wfl hI hwt₁
  rw [hty₁] at hlit
  simp only [interpret_ifSome hI hwt₁ hwi.left] at heq
  have hwi' := interpret_term_wf hI hwi.left
  rw [hwi.right] at hwi'
  have hopt := wfl_of_type_option_is_option hlit.left hlit.right
  rcases hopt with hopt | ⟨t', hopt, _⟩ <;>
  simp only [hopt, pe_ifSome_none hwi'.right, pe_ifSome_some hwi'.right, reduceCtorEq] at heq
  rename_i hty'
  simp only [interpret_ite hI hwo₁.left hwt₂ hwt₃ hwo₁.right hty,
    interpret_option_get I hwt₁ hty₁, hopt, pe_option_get'_some] at heq
  replace hlit := interpret_term_wfl hI hwt₁
  simp only [hopt] at hlit
  have hwt' := wf_term_some_implies hlit.left.left
  replace hlit := lit_term_some_implies_lit hlit.left.right
  have hb := wfl_of_type_bool_is_true_or_false (And.intro hwt' hlit) hty'
  rcases hb with hb | hb <;>
  subst hb <;>
  simp only [pe_ite_false, pe_ite_true] at heq <;>
  simp only [heq, true_or, or_true]

theorem compile_interpret_in_footprint {x : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term} {uid : EntityUID}
  (hwε : εnv.WellFormedFor x)
  (hI  : I.WellFormed εnv.entities)
  (hok : compile x εnv = .ok t)
  (ht  : t.interpret I = .some (.entity uid)) :
  ∃ tₑ ∈ footprint x εnv, tₑ.interpret I = .some (.entity uid)
:= by
  induction x using compile.induct generalizing t
  case case1 =>
    exact compile_interpret_lit_in_footprint hwε hI hok ht
  case case2 =>
    exact compile_interpret_var_in_footprint hwε hI hok ht
  case case3 x₁ x₂ x₃ _ ih₂ ih₃ =>
    replace hwε := wf_εnv_for_ite_implies hwε
    replace ⟨t₁, hok₁, hok⟩ := compile_ite_ok_implies hok
    simp only [footprint, footprint.ofBranch, hok₁]
    split at hok <;> simp only
    · rw [eq_comm] at hok
      exact ih₂ hwε.right.left hok ht
    · rw [eq_comm] at hok
      exact ih₃ hwε.right.right hok ht
    · replace ⟨hty₁, t₂, t₃, hok₂, hok₃, hty, hok⟩ := hok
      subst hok
      simp only [Set.mem_union_iff_mem_or]
      have hwt₁ := (compile_wf hwε.left hok₁).left
      have ⟨hwt₂, _, hty₂⟩ := compile_wf hwε.right.left hok₂
      have hwt₃ := (compile_wf hwε.right.right hok₃).left
      have heq := interpret_ifSome_ite_eq_implies hI hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty ht
      rcases heq with heq | heq
      · have ⟨tₑ, ih₂⟩ := ih₂ hwε.right.left hok₂ heq
        exists tₑ
        simp only [ih₂, or_true, true_or, and_self]
      · have ⟨tₑ, ih₃⟩ := ih₃ hwε.right.right hok₃ heq
        exists tₑ
        simp only [ih₃, or_true, and_self]
  case case9 =>
    simp only [footprint, footprint.ofEntity, hok, compile_isOptionEntityType hwε hI hok ht,
      ↓reduceIte, Set.mem_union_iff_mem_or, Set.mem_singleton_iff_eq, exists_eq_or_imp, ht, true_or]
  case' case4 =>
    have hty := typeOf_compile_and_option_bool hwε hok
  case' case5 =>
    have hty := typeOf_compile_or_option_bool hwε hok
  case' case6 =>
    have hty := typeOf_compile_unaryApp_option_types hwε hok
    rcases hty with hty | hty
  case case7 =>
    exists t
    simp [footprint, footprint.ofEntity, hok, compile_isOptionEntityType hwε hI hok ht,
      ↓reduceIte, Set.mem_union_iff_mem_or, Set.mem_singleton_iff_eq, ht]
  case' case8 =>
    have hty := typeOf_compile_hasAttr_option_bool hwε hok
  case' case10 =>
    have ⟨_, hty⟩ := typeOf_compile_set_option_set hok
  case' case11 =>
    have ⟨_, hty⟩ := typeOf_compile_record_option_record hok
  case' case12 =>
    have hty := typeOf_compile_call_option_types hwε hok
    rcases hty with hty | ⟨_, hty⟩ | hty
  all_goals {
    have hty' := compile_isOptionEntityType hwε hI hok ht
    simp only [TermType.isOptionEntityType, hty, Bool.false_eq_true] at hty'
  }

-------------------

private def CompileInterpretOnFootprint (x : Expr) (ft : Set Term) (εnv : SymEnv) (I₁ I₂ : Interpretation) : Prop :=
  ∀ {t : Term},
    εnv.WellFormedFor x →
    I₁.WellFormed εnv.entities →
    I₂.WellFormed εnv.entities →
    εnv.SameOn ft I₁ I₂ →
    footprint x εnv ⊆ ft →
    compile x εnv = .ok t →
    t.interpret I₁ = t.interpret I₂

theorem compile_interpret_lit_on_footprint {p : Prim} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hok : compile (.lit p) εnv = .ok t) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [compile, compilePrim] at hok
  split at hok <;>
  (try split at hok) <;>
  simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok <;>
  subst hok <;>
  simp only [interpret_term_some, interpret_term_prim]

theorem compile_interpret_var_on_footprint {v : Var} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.var v))
  (hsm : εnv.SameOn ft I₁ I₂)
  (hok : compile (.var v) εnv = .ok t) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [compile, compileVar] at hok
  replace hsm := hsm.left
  simp only [SymRequest.interpret, SymRequest.mk.injEq] at hsm
  cases v
  all_goals {
    simp only at hok
    split at hok <;>
    simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    simp only [someOf, interpret_term_some, hsm]
  }

local macro "simp_ifSome_eq" hI₁:ident hI₂:ident hwt₁:ident hty₁:ident hwt₂:ident hty₂:ident ih:ident : tactic => do
  `(tactic | (
    simp only [interpret_ifSome $hI₁ $hwt₁ $hwt₂, interpret_ifSome $hI₂ $hwt₁ $hwt₂, $ih:ident]
    have hwt₁₂ := interpret_term_wf $hI₁ $hwt₂
    have hwt₂₂ := interpret_term_wf $hI₂ $hwt₂
    rw [$hty₂:term] at hwt₁₂ hwt₂₂
    have hwl₂ := interpret_term_wfl $hI₂ $hwt₁
    rw [$hty₁:term] at hwl₂
    have hlit₂ := wfl_of_type_option_is_option hwl₂.left hwl₂.right
    rcases hlit₂ with hlit₂ | ⟨t₂', hlit₂, hty₂'⟩ <;>
    simp only [hlit₂, pe_ifSome_none hwt₁₂.right, pe_ifSome_none hwt₂₂.right]
    simp only [pe_ifSome_some hwt₁₂.right, pe_ifSome_some hwt₂₂.right]
    clear hwt₁₂ hwt₂₂ hwl₂))

private theorem interpret_option_get_eq {t t' : Term} {I₁ I₂ : Interpretation} {εs : SymEntities} :
  t.WellFormed εs → t.typeOf = .option ty →
  t.interpret I₁ = t.interpret I₂ →
  t.interpret I₂ = .some t' →
  (Factory.option.get t).interpret I₁ = (Factory.option.get t).interpret I₂
:= by
  intro hwt hty heq₁ heq₂
  simp only [interpret_option_get I₁ hwt hty, heq₁, heq₂, pe_option_get'_some,
    interpret_option_get I₂ hwt hty]

private theorem interpret_ifSome_ifSome_ite_eq {t₁ t₂ t₃ : Term} {I₁ I₂ : Interpretation} {εs : SymEntities} :
  I₁.WellFormed εs → I₂.WellFormed εs →
  t₁.WellFormed εs → t₂.WellFormed εs → t₃.WellFormed εs →
  t₁.typeOf = .option .bool →
  t₂.typeOf = .option ty →
  t₃.typeOf = .option ty →
  t₁.interpret I₁ = t₁.interpret I₂ →
  t₂.interpret I₁ = t₂.interpret I₂ →
  t₃.interpret I₁ = t₃.interpret I₂ →
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).interpret I₁ =
  (ifSome t₁ (Factory.ite (option.get t₁) t₂ t₃)).interpret I₂
:= by
  intro hI₁ hI₂ hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty₃ ht₁ ht₂ ht₃
  have ⟨hwo₁, hoty₁⟩ := wf_option_get hwt₁ hty₁
  rw [← hty₂, eq_comm] at hty₃
  have hwi := wf_ite hwo₁ hwt₂ hwt₃ hoty₁ hty₃
  rw [hty₂] at hwi
  have hwi₁ := interpret_term_wf hI₁ hwi.left
  have hwi₂ := interpret_term_wf hI₂ hwi.left
  rw [hwi.right] at hwi₁ hwi₂
  simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hwi.left hwi.right ht₁
  rename_i ht₁' _
  simp only [interpret_ite hI₁ hwo₁ hwt₂ hwt₃ hoty₁ hty₃,
    interpret_ite hI₂ hwo₁ hwt₂ hwt₃ hoty₁ hty₃,
    ht₂, ht₃, interpret_option_get_eq hwt₁ hty₁ ht₁ ht₁']

private theorem compile_interpret_ite_on_footprint {x₁ x₂ x₃ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.ite x₁ x₂ x₃))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.ite x₁ x₂ x₃) εnv ⊆ ft)
  (hok : compile (.ite x₁ x₂ x₃) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂)
  (ih₃ : CompileInterpretOnFootprint x₃ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace hwε := wf_εnv_for_ite_implies hwε
  replace ⟨t₁, hok₁, hok⟩ := compile_ite_ok_implies hok
  split at hok <;>
  simp only [footprint, footprint.ofBranch, hok₁] at hft
  · rw [eq_comm] at hok
    exact ih₂ hwε.right.left hI₁ hI₂ hsm hft hok
  · rw [eq_comm] at hok
    exact ih₃ hwε.right.right hI₁ hI₂ hsm hft hok
  · rename_i hnt hnf
    replace ⟨hty₁, t₂, t₃, hok₂, hok₃, hty, hok⟩ := hok
    subst hok
    simp only [Set.union_subset] at hft
    have hwt₁ := (compile_wf hwε.left hok₁).left
    have ⟨hwt₂, _, hty₂⟩ := compile_wf hwε.right.left hok₂
    have hwt₃ := (compile_wf hwε.right.right hok₃).left
    have hty₃ := hty₂ ; rw [hty] at hty₃
    exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂ hwt₁ hwt₂ hwt₃ hty₁ hty₂ hty₃
      (ih₁ hwε.left hI₁ hI₂ hsm hft.left.left hok₁)
      (ih₂ hwε.right.left hI₁ hI₂ hsm hft.left.right hok₂)
      (ih₃ hwε.right.right hI₁ hI₂ hsm hft.right hok₃)

private theorem compile_interpret_and_on_footprint {x₁ x₂ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.and x₁ x₂))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.and x₁ x₂) εnv ⊆ ft)
  (hok : compile (.and x₁ x₂) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_and_ok_implies hok
  split at hok
  · subst hok
    simp only [interpret_term_some, interpret_term_prim]
  · rename_i hf
    replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    replace hwε := wf_εnv_for_and_implies hwε
    cases ht : decide (t₁ = .some (.bool true)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ht <;>
    simp only [footprint, footprint.ofBranch, hok₁] at hft
    · simp only [Set.union_subset] at hft
      specialize @ih₁ t₁ hwε.left hI₁ hI₂ hsm hft.left.left hok₁
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft.left.right hok₂
      have hwt₁ := (compile_wf hwε.left hok₁).left
      have hwt₂ := (compile_wf hwε.right hok₂).left
      exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂
        hwt₁ hwt₂ (Term.WellFormed.some_wf wf_bool)
        hty₁ hty₂ (by simp only [typeOf_term_some, typeOf_bool])
        ih₁ ih₂ (by simp only [interpret_term_some, interpret_term_prim])
    · subst ht
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft hok₂
      simp only [pe_option_get_some, pe_ite_true, pe_ifSome_some hty₂, ih₂]

private theorem compile_interpret_or_on_footprint {x₁ x₂ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.or x₁ x₂))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.or x₁ x₂) εnv ⊆ ft)
  (hok : compile (.or x₁ x₂) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace ⟨t₁, hok₁, hok⟩ := compile_or_ok_implies hok
  split at hok
  · subst hok
    simp only [interpret_term_some, interpret_term_prim]
  · rename_i hf
    replace ⟨hty₁, t₂, hok₂, hty₂, hok⟩ := hok
    subst hok
    replace hwε := wf_εnv_for_or_implies hwε
    cases ht : decide (t₁ = .some (.bool false)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at ht <;>
    simp only [footprint, footprint.ofBranch, hok₁] at hft
    · simp only [Set.union_subset] at hft
      specialize @ih₁ t₁ hwε.left hI₁ hI₂ hsm hft.left.left hok₁
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft.right hok₂
      have hwt₁ := (compile_wf hwε.left hok₁).left
      have hwt₂ := (compile_wf hwε.right hok₂).left
      exact interpret_ifSome_ifSome_ite_eq hI₁ hI₂
        hwt₁ (Term.WellFormed.some_wf wf_bool) hwt₂
        hty₁ (by simp only [typeOf_term_some, typeOf_bool]) hty₂
        ih₁ (by simp only [interpret_term_some, interpret_term_prim]) ih₂
    · subst ht
      specialize @ih₂ t₂ hwε.right hI₁ hI₂ hsm hft hok₂
      simp only [pe_option_get_some, pe_ite_false, pe_ifSome_some hty₂, ih₂]

private theorem same_footprint_ancestors {x : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t t' : Term} {ety₁ : EntityType}
  (hwε  : εnv.WellFormedFor x)
  (hI₁  : I₁.WellFormed εnv.entities)
  (hsm  : εnv.SameOn ft I₁ I₂)
  (hft  : footprint x εnv ⊆ ft)
  (hok  : compile x εnv = Except.ok t)
  (heq₁ : Term.interpret I₁ t = Term.interpret I₂ t)
  (heq₂ : Term.interpret I₂ t = t'.some)
  (hty  : t'.typeOf = .entity ety₁) :
  ∃ uid₁ : EntityUID,
    t' = .entity uid₁ ∧
    uid₁.ty = ety₁ ∧
    ∀ ety₂ f,
      εnv.entities.ancestorsOfType uid₁.ty ety₂ = some f →
      app (UnaryFunction.interpret I₁ f) (Term.entity uid₁) =
      app (UnaryFunction.interpret I₂ f) (Term.entity uid₁)
:= by
  rw [heq₂] at heq₁
  have hwt := (compile_wf hwε hok).left
  have hlit := (interpret_term_wfl hI₁ hwt).left
  simp only [heq₁] at hlit
  replace ⟨hwt, hlit⟩ := hlit
  replace hwt := wf_term_some_implies hwt
  replace hlit := lit_term_some_implies_lit hlit
  have ⟨uid₁, ht', hty'⟩ := wfl_of_type_entity_is_entity (And.intro hwt hlit) hty
  subst ht' hty'
  simp only [Term.prim.injEq, TermPrim.entity.injEq, exists_eq_left', true_and]
  intro ety₂ f hancs
  simp only [SymEntities.ancestorsOfType, SymEntities.ancestors, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at hancs
  replace ⟨_, ⟨δ, hδ, hancs⟩, hf⟩ := hancs
  subst hancs
  have ⟨tₑ, hin, heq₃⟩ := compile_interpret_in_footprint hwε hI₁ hok heq₁
  replace hin := Set.mem_subset_mem hin hft
  exact (hsm.right uid₁.ty δ hδ).right.left ety₂ f hf tₑ hin uid₁ heq₃ rfl

private theorem compile_interpret_unaryApp_on_footprint {op₁ : UnaryOp} {x₁ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.unaryApp op₁ x₁))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.unaryApp op₁ x₁) εnv ⊆ ft)
  (hok : compile (.unaryApp op₁ x₁) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint] at hft
  replace hwε := wf_εnv_for_unaryApp_implies hwε
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_unaryApp_ok_implies hok
  subst heq
  specialize ih₁ hwε hI₁ hI₂ hsm hft hok₁
  replace ⟨ty₁, hwt₁, hwo₁⟩ := compile_option_get_wf hwε hok₁
  have hwt₂ := compileApp₁_wf_types hwo₁.left hok
  have ⟨_, hty₂⟩ : ∃ ty, t₂.typeOf = .option ty := by
    split at hwt₂ <;> simp only [hwt₂, TermType.option.injEq, exists_eq']
  replace hwt₂ := hwt₂.left
  simp_ifSome_eq hI₁ hI₂ hwt₁.left hwt₁.right hwt₂ hty₂ ih₁
  rename_i ht₁ _
  replace ih₁ := interpret_option_get_eq hwt₁.left hwt₁.right ih₁ ht₁
  have hr₁ := interpret_compileApp₁ hI₁ hwo₁.left hok
  have hr₂ := interpret_compileApp₁ hI₂ hwo₁.left hok
  simp only [ih₁, hr₂, Except.ok.injEq] at hr₁
  simp only [hr₁]

private theorem compile_interpret_binaryApp_on_footprint {op₂ : BinaryOp} {x₁ x₂ : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.binaryApp op₂ x₁ x₂))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.binaryApp op₂ x₁ x₂) εnv ⊆ ft)
  (hok : compile (.binaryApp op₂ x₁ x₂) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂)
  (ih₂ : CompileInterpretOnFootprint x₂ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compile_binaryApp_ok_implies hok
  subst ht
  replace ⟨hwε, hwt₂⟩ := wf_εnv_for_binaryApp_implies hwε
  simp only [footprint, Set.union_subset] at hft
  specialize @ih₁ t₁ hwε hI₁ hI₂ hsm hft.left.right hok₁
  specialize @ih₂ t₂ hwt₂ hI₁ hI₂ hsm hft.right hok₂
  replace ⟨ty₁, hwt₁, hwo₁⟩ := compile_option_get_wf hwε hok₁
  replace ⟨ty₂, hwt₂, hwo₂⟩ := compile_option_get_wf hwt₂ hok₂
  have ⟨hwt₃, ty₃, hty₃⟩ := compileApp₂_wf hwε.left.right hwo₁.left hwo₂.left hok
  have hwt₂₃ := wf_ifSome_option hwt₂.left hwt₃ hty₃
  simp_ifSome_eq hI₁ hI₂ hwt₁.left hwt₁.right hwt₂₃.left hwt₂₃.right ih₁
  rename_i t₁' hlit₁ hty₁'
  simp_ifSome_eq hI₁ hI₂ hwt₂.left hwt₂.right hwt₃ hty₃ ih₂
  rename_i hlit₂ _
  clear hwt₃ hty₃ hwt₂₃
  have ih₁' := interpret_option_get_eq hwt₁.left hwt₁.right ih₁ hlit₁
  have ih₂' := interpret_option_get_eq hwt₂.left hwt₂.right ih₂ hlit₂
  cases op₂
  case eq =>
    rcases compileApp₂_eq_ok_implies hok with ⟨_, hok⟩ | ⟨_, hok⟩ <;> subst hok
    · simp only [interpret_term_some, interpret_eq hI₁ hwo₁.left hwo₂.left,
        interpret_eq hI₂ hwo₁.left hwo₂.left, ih₁', ih₂']
    · simp only [interpret_term_some, interpret_term_prim]
  case mem =>
    replace ⟨ety₁, ety₂, hety₁, hok⟩ := compileApp₂_mem_ok_implies hok
    have hwl₁₁ := interpret_term_wf hI₁ hwo₁.left
    have hwl₁₂ := interpret_term_wf hI₁ hwo₂.left
    have hwl₂₁ := interpret_term_wf hI₂ hwo₁.left
    have hwl₂₂ := interpret_term_wf hI₂ hwo₂.left
    rcases hok with ⟨hety₂, hok⟩ | ⟨hety₂, hok⟩
    all_goals {
      subst hok
      simp only [hwo₁.right] at hety₁
      simp only [hwo₂.right] at hety₂
      subst hety₁ hety₂
      have ⟨uid₁, heqt, heqty, heqf⟩ := same_footprint_ancestors hwε hI₁ hsm hft.left.right hok₁ ih₁ hlit₁ hty₁'
      subst heqt heqty
      simp only [interpret_term_some]
      try simp only [
        interpret_compileInₑ hwε.left.right hI₁ hwo₁.left hwo₂.left hwl₁₁ hwl₁₂ hwo₁.right hwo₂.right,
        interpret_compileInₑ hwε.left.right hI₂ hwo₁.left hwo₂.left hwl₂₁ hwl₂₂ hwo₁.right hwo₂.right]
      try simp only [
        interpret_compileInₛ hwε.left.right hI₁ hwo₁.left hwo₂.left hwl₁₁ hwl₁₂ hwo₁.right hwo₂.right,
        interpret_compileInₛ hwε.left.right hI₂ hwo₁.left hwo₂.left hwl₂₁ hwl₂₂ hwo₁.right hwo₂.right]
      simp only [ih₁', ih₂',
        interpret_option_get I₂ hwt₁.left hwt₁.right,
        interpret_option_get I₂ hwt₂.left hwt₂.right,
        hlit₁, hlit₂, pe_option_get'_some, compileInₑ, compileInₛ, Term.some.injEq]
      cases hancs : εnv.entities.ancestorsOfType uid₁.ty ety₂
      case none =>
        simp only [interpret_entities_ancestorsOfType_none hancs]
      case some f =>
        simp only [interpret_entities_ancestorsOfType_some hancs]
        repeat apply congr_arg
        exact heqf ety₂ f hancs }
  case less =>
    rcases compileApp₂_less_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    all_goals(
      subst hok
      simp only [interpret_term_some, interpret_bvslt, interpret_ext_duration_val,
        interpret_ext_datetime_val, ih₁', ih₂']
    )
  case lessEq =>
    rcases compileApp₂_lessEq_ok_implies hok with ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩ | ⟨hty₁, hty₂, hok⟩
    all_goals(
      subst hok
      simp only [interpret_term_some, interpret_bvsle, interpret_ext_duration_val,
        interpret_ext_datetime_val, ih₁', ih₂']
    )
  case contains =>
    replace ⟨_, hok⟩ := compileApp₂_contains_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_member hwo₂.left hwo₁.left, ih₁', ih₂']
  case containsAll =>
    replace ⟨_, _, _, hok⟩ := compileApp₂_containsAll_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_subset hwo₂.left hwo₁.left, ih₁', ih₂']
  case containsAny =>
    replace ⟨_, hty₁, hty₂, hok⟩ := compileApp₂_containsAny_ok_implies hok
    subst hok
    simp only [interpret_term_some, interpret_set_intersects hI₁ hwo₁.left hwo₂.left hty₁ hty₂,
      ih₁', ih₂', interpret_set_intersects hI₂ hwo₁.left hwo₂.left hty₁ hty₂]
  case add =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_add_ok_implies hok
    subst hok
    have hwa := wf_bvadd hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvsaddo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvsaddo, interpret_bvadd, ih₁', ih₂']
  case sub =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_sub_ok_implies hok
    subst hok
    have hwa := wf_bvsub hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvssubo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvssubo, interpret_bvsub, ih₁', ih₂']
  case mul =>
    replace ⟨hty₁, hty₂, hok⟩ := compileApp₂_mul_ok_implies hok
    subst hok
    have hwa := wf_bvmul hwo₁.left hwo₂.left hty₁ hty₂
    have hws := wf_bvsmulo hwo₁.left hwo₂.left hty₁ hty₂
    simp only [interpret_ifFalse hI₁ hws.left hws.right hwa.left,
      interpret_ifFalse hI₂ hws.left hws.right hwa.left,
      interpret_bvsmulo, interpret_bvmul, ih₁', ih₂']
  case hasTag =>
    replace ⟨ety, hty₁, _, hok⟩ := compileApp₂_hasTag_ok_implies hok
    replace hok := compileHasTag_ok_implies hok
    rcases hok with ⟨_, hok⟩ | ⟨τs, hτs, hok⟩ <;> subst hok
    · simp only [interpret_term_some, interpret_term_prim]
    · simp only [interpret_term_some,
        ← interpret_hasTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₁ hwo₁.left hwo₂.left hty₁,
        ← interpret_hasTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₂ hwo₁.left hwo₂.left hty₁,
        ih₁', ih₂', Term.some.injEq]
      simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs
      replace ⟨δ, hδ, hτs⟩ := hτs
      simp only [(hsm.right ety δ hδ).right.right τs hτs]
  case getTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_getTag_ok_implies hok
    replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
    subst hok
    simp only [
      ← interpret_getTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₁ hwo₁.left hwo₂.left hty₁ hty₂,
      ← interpret_getTag (wf_εs_implies_wf_tags hwε.left.right hτs) hI₂ hwo₁.left hwo₂.left hty₁ hty₂,
      ih₁', ih₂']
    simp only [SymEntities.tags, Option.map_eq_some_iff] at hτs
    replace ⟨δ, hδ, hτs⟩ := hτs
    simp only [(hsm.right ety δ hδ).right.right τs hτs]

private theorem compileAttrsOf_interpret_record_get_eq {t₁ t₃ : Term} {a₁ : Attr} {tyₐ : TermType} {rty : Map Attr TermType} {εs : SymEntities} {I₁ I₂ : Interpretation}
  (hwε  : εs.WellFormed)
  (hI₁  : I₁.WellFormed εs)
  (hI₂  : I₂.WellFormed εs)
  (hsm  : εs.SameOn ft I₁ I₂)
  (hwt₁ : t₁.WellFormed εs)
  (hok  : compileAttrsOf t₁ εs = .ok t₃)
  (hwt₃ : Term.WellFormed εs t₃)
  (hty₃ : t₃.typeOf = TermType.record rty)
  (htyₐ : rty.find? a₁ = some tyₐ)
  (ih₁  : Term.interpret I₁ t₁ = Term.interpret I₂ t₁) :
  (record.get t₃ a₁).interpret I₁ = (record.get t₃ a₁).interpret I₂
:= by
  replace hok := compileAttrsOf_ok_implies hok
  rcases hok with ⟨_, hty₁, hok⟩ | ⟨ety, fₐ, hty₁, hf, hok⟩ <;>
  subst hok <;>
  simp only [interpret_record_get I₁ hwt₃ hty₃ htyₐ, interpret_record_get I₂ hwt₃ hty₃ htyₐ, ih₁]
  have hwf := wf_εs_implies_wf_attrs hwε hf
  rw [eq_comm, ← hty₁] at hwf
  simp only [interpret_app hI₁ hwt₁ hwf.left hwf.right.left, interpret_app hI₂ hwt₁ hwf.left hwf.right.left, ih₁]
  simp only [SymEntities.attrs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hf
  replace ⟨δ, hf⟩ := hf
  replace hsm := (hsm ety δ hf.left).left
  simp only [hf.right] at hsm
  simp only [hsm]

private theorem compile_interpret_hasAttr_on_footprint {x₁ : Expr}  {a₁ : Attr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.hasAttr x₁ a₁))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.hasAttr x₁ a₁) εnv ⊆ ft)
  (hok : compile (.hasAttr x₁ a₁) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace hwε := wf_εnv_for_hasAttr_implies hwε
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_hasAttr_ok_implies hok
  subst heq
  simp only [footprint] at hft
  specialize ih₁ hwε hI₁ hI₂ hsm hft hok₁
  have ⟨ty₁, ⟨hwt₁, hty₁⟩, hwo₁⟩ := compile_option_get_wf hwε hok₁
  replace ⟨t₃, rty, hok, hr⟩ := compileHasAttr_ok_implies hok
  replace ⟨hty₃, hr⟩ := hr
  split at hr <;> subst hr
  case h_1 tyₐ htyₐ =>
    have hwt₃ := (compileAttrsOf_wf hwε.left.right hwo₁.left hok).left
    have hwr := wf_record_get hwt₃ hty₃ htyₐ
    have ⟨hws, hwsty⟩ := wf_isSome hwr.left
    replace ⟨hws, hwsty⟩ := wf_term_some hws hwsty
    simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hws hwsty ih₁
    rename_i ht₁ _
    simp only [interpret_term_some, interpret_isSome hI₁ hwr.left,
      interpret_isSome hI₂ hwr.left,
      compileAttrsOf_interpret_record_get_eq
        hwε.left.right hI₁ hI₂ hsm.right hwo₁.left hok hwt₃ hty₃ htyₐ
        (interpret_option_get_eq hwt₁ hty₁ ih₁ ht₁)]
  case h_2 | h_3 =>
    simp only [interpret_ifSome hI₁ hwt₁ (Term.WellFormed.some_wf wf_bool),
      interpret_ifSome hI₂ hwt₁ (Term.WellFormed.some_wf wf_bool),
      ih₁, interpret_term_some, interpret_term_prim]

private theorem compile_interpret_getAttr_on_footprint {x₁ : Expr}  {a₁ : Attr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.getAttr x₁ a₁))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.getAttr x₁ a₁) εnv ⊆ ft)
  (hok : compile (.getAttr x₁ a₁) εnv = .ok t)
  (ih₁ : CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint, footprint.ofEntity, hok, Set.union_subset] at hft
  replace hwε := wf_εnv_for_getAttr_implies hwε
  replace ⟨t₁, t₂, hok₁, hok, heq⟩ := compile_getAttr_ok_implies hok
  subst heq
  specialize ih₁ hwε hI₁ hI₂ hsm hft.right hok₁
  clear hft
  have ⟨ty₁, ⟨hwt₁, hty₁⟩, hwo₁⟩ := compile_option_get_wf hwε hok₁
  replace ⟨t₃, rty, hok, hr⟩ := compileGetAttr_ok_implies hok
  replace ⟨hty₃, tyₐ, htyₐ, hr⟩ := hr
  have hwt₃ := (compileAttrsOf_wf hwε.left.right hwo₁.left hok).left
  have ⟨hwr, hwrty⟩ := wf_record_get hwt₃ hty₃ htyₐ
  split at hr <;> subst hr
  case' h_2 => replace ⟨hwr, hwrty⟩ := wf_term_some hwr hwrty
  all_goals {
    simp_ifSome_eq hI₁ hI₂ hwt₁ hty₁ hwr hwrty ih₁
    rename_i ht₁ _
    simp only [interpret_term_some,
      compileAttrsOf_interpret_record_get_eq
        hwε.left.right hI₁ hI₂ hsm.right hwo₁.left hok hwt₃ hty₃ htyₐ
        (interpret_option_get_eq hwt₁ hty₁ ih₁ ht₁)]
  }

private theorem map_interpret_option_get_eq {ts ts' : List Term} {ty : TermType} {I₁ I₂ : Interpretation} {εs : SymEntities}
  (hwt : ∀ t ∈ ts, t.WellFormed εs)
  (hty : ∀ t ∈ ts, t.typeOf = .option ty)
  (h₁  : ∀ t ∈ ts, Term.interpret I₁ t = Term.interpret I₂ t)
  (h₂  : ts.map (Term.interpret I₂) = ts'.map Term.some) :
  ts.map (Term.interpret I₁ ∘ option.get) = ts.map (Term.interpret I₂ ∘ option.get)
:= by
  apply List.map_congr
  intro t ht
  specialize h₁ t ht
  have h₃ : t.interpret I₂ ∈ ts.map (Term.interpret I₂) := by
    simp only [List.mem_map]
    exists t
  simp only [h₂, List.mem_map] at h₃
  replace ⟨t', _, h₃⟩ := h₃
  rw [eq_comm] at h₃
  exact interpret_option_get_eq (hwt t ht) (hty t ht) h₁ h₃

private theorem compile_interpret_on_footprint_ihs {xs : List Expr} {ts : List Term} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation}
  (hwε : ∀ (x : Expr), x ∈ xs → εnv.WellFormedFor x)
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : xs.mapUnion (footprint · εnv) ⊆ ft)
  (hok : ∀ t ∈ ts, ∃ x ∈ xs, compile x εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpretOnFootprint x ft εnv I₁ I₂) :
  ∀ t ∈ ts, t.interpret I₁ = t.interpret I₂
:= by
  intro t ht
  replace ⟨x, hx, hok⟩ := hok t ht
  apply ih x hx (hwε x hx) hI₁ hI₂ hsm _ hok
  exact Set.subset_trans (List.mem_implies_subset_mapUnion (footprint · εnv) hx) hft

private theorem compile_interpret_set_on_footprint {xs : List Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.set xs))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.set xs) εnv ⊆ ft)
  (hok : compile (.set xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpretOnFootprint x ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  replace hwε := wf_εnv_for_set_implies hwε
  simp only [footprint, List.mapUnion₁_eq_mapUnion (footprint · εnv)] at hft
  replace ⟨ts, ha, hok⟩ := compile_set_ok_implies hok
  replace ⟨ty, hd, tl, heq, hty, hok⟩ := compileSet_ok_implies hok
  subst hok
  have hwts := compile_wfs hwε ha
  replace ha := List.forall₂_implies_all_right ha
  have hwty := typeOf_option_wf_terms_is_wf heq hwts hty
  have hwo := wf_option_get_mem_of_type hwts hty
  have hws := @wf_setOf_map _ option.get _ _ hwo hwty
  replace hws := wf_term_some hws.left hws.right
  simp only [interpret_ifAllSome hI₁ hwts hws.left hws.right,
    interpret_ifAllSome hI₂ hwts hws.left hws.right]
  replace ih := compile_interpret_on_footprint_ihs hwε hI₁ hI₂ hsm hft ha ih
  simp only [List.map_congr ih]
  have hws₁ := interpret_term_wf hI₁ hws.left
  have hws₂ := interpret_term_wf hI₂ hws.left
  rw [hws.right] at hws₁ hws₂
  have hn := pe_interpret_terms_of_type_option (interpret_terms_wfls hI₂ hwts hty)
  rcases hn with ⟨_, hn⟩ | ⟨_, hs⟩
  · simp only [pe_ifAllSome_none hn hws₁.right, pe_ifAllSome_none hn hws₂.right]
  · simp only [hs, interpret_term_some, interpret_setOf, List.map_map,
      map_interpret_option_get_eq hwts hty ih hs]

private theorem map_interpret_snd_option_get_eq {ats : List (Attr × Term)} {ts : List Term} {I₁ I₂ : Interpretation} {εs : SymEntities}
  (hwt : ∀ a t, (a, t) ∈ ats → t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty)
  (h₁  : ∀ p ∈ ats, p.snd.interpret I₁ = p.snd.interpret I₂)
  (h₂  : List.map (Term.interpret I₂ ∘ Prod.snd) ats = List.map Term.some ts) :
  ats.map (Prod.map id (Term.interpret I₁ ∘ option.get)) =
  ats.map (Prod.map id (Term.interpret I₂ ∘ option.get))
:= by
  apply List.map_congr
  intro (a, t) ht
  specialize h₁ (a, t) ht
  simp only at h₁
  simp only [Prod.map, id_eq, Function.comp_apply, Prod.mk.injEq, true_and]
  have h₃ : (Term.interpret I₂ ∘ Prod.snd) (a, t) ∈ ats.map (Term.interpret I₂ ∘ Prod.snd) := by
    simp only [List.mem_map]
    exists (a, t)
  simp only [h₂, List.mem_map] at h₃
  replace ⟨t', _, h₃⟩ := h₃
  rw [eq_comm] at h₃
  replace ⟨hwt, _, hty⟩ := hwt a t ht
  exact interpret_option_get_eq hwt hty h₁ h₃

private theorem compile_interpret_record_on_footprint {axs : List (Attr × Expr)} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.record axs))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.record axs) εnv ⊆ ft)
  (hok : compile (.record axs) εnv = .ok t)
  (ih  : ∀ (a₁ : Attr) (x₁ : Expr), sizeOf (a₁, x₁).snd < 1 + sizeOf axs →
    CompileInterpretOnFootprint x₁ ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint, List.mapUnion₂_eq_mapUnion (λ x : Attr × Expr => footprint x.snd εnv)] at hft
  replace hft : ∀ ax ∈ axs, footprint ax.snd εnv ⊆ ft := by
    intro x hx
    have h := List.mem_implies_subset_mapUnion (fun x : Attr × Expr => footprint x.snd εnv) hx
    simp only at h
    exact Set.subset_trans h hft
  replace hwε := wf_εnv_for_record_implies hwε
  replace ⟨ats, ha, hok⟩ := compile_record_ok_implies hok
  subst hok
  have hwts := compile_attr_expr_wfs hwε ha
  have hwg := wf_prods_implies_wf_map_snd (wf_prods_option_implies_wf_prods hwts)
  have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd hwts)
  replace ha := List.forall₂_implies_all_right ha
  replace ih : ∀ p ∈ ats, (Term.interpret I₁ ∘ Prod.snd) p = (Term.interpret I₂ ∘ Prod.snd) p := by
    intro (a, t) ht
    have ⟨(a', x), hx, heq, hok⟩ := ha (a, t) ht
    simp only at heq hok
    subst heq
    simp only [Function.comp_apply]
    exact ih a' x (List.sizeOf_attach₂ hx) (hwε (a', x) hx) hI₁ hI₂ hsm (hft (a', x) hx) hok
  simp only [compileRecord, someOf, interpret_ifAllSome hI₁ hwg hwo hty,
    interpret_ifAllSome hI₂ hwg hwo hty, List.map_map, List.map_congr ih]
  have hwo₁ := interpret_term_wf hI₁ hwo
  have hwo₂ := interpret_term_wf hI₂ hwo
  rw [hty] at hwo₁ hwo₂
  have hwts' := interpret_attr_terms_wfls hI₂ hwts
  rcases (pe_wfls_of_type_option hwts') with ⟨_, hn⟩ | ⟨ts, hs⟩
  · simp only [pe_ifAllSome_none hn hwo₁.right, pe_ifAllSome_none hn hwo₂.right]
  · simp only [hs, interpret_term_some, interpret_recordOf, List.map_map,
      prod_map_id_comp_eq, map_interpret_snd_option_get_eq hwts ih hs]

private theorem compile_interpret_call_on_footprint {xfn : ExtFun} {xs : List Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor (.call xfn xs))
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint (.call xfn xs) εnv ⊆ ft)
  (hok : compile (.call xfn xs) εnv = .ok t)
  (ih  : ∀ x ∈ xs, CompileInterpretOnFootprint x ft εnv I₁ I₂) :
  t.interpret I₁ = t.interpret I₂
:= by
  simp only [footprint, List.mapUnion₁_eq_mapUnion (footprint · εnv)] at hft
  replace hwε := wf_εnv_for_call_implies hwε
  replace ⟨ts, ha, hok⟩ := compile_call_ok_implies hok
  have hwts := compile_wfs hwε ha
  replace ha := List.forall₂_implies_all_right ha
  replace ih := compile_interpret_on_footprint_ihs hwε hI₁ hI₂ hsm hft ha ih
  have hr₁ := compileCall_interpret hI₁ hwts hok
  have hr₂ := compileCall_interpret hI₂ hwts hok
  simp only [List.map_congr ih] at hr₁
  simp only [hr₁, Except.ok.injEq] at hr₂
  exact hr₂

theorem compile_interpret_on_footprint {x : Expr} {ft : Set Term} {εnv : SymEnv} {I₁ I₂ : Interpretation} {t : Term}
  (hwε : εnv.WellFormedFor x)
  (hI₁ : I₁.WellFormed εnv.entities)
  (hI₂ : I₂.WellFormed εnv.entities)
  (hsm : εnv.SameOn ft I₁ I₂)
  (hft : footprint x εnv ⊆ ft)
  (hok : compile x εnv = .ok t) :
  t.interpret I₁ = t.interpret I₂
:= by
  induction x using compile.induct generalizing t
  case case1 =>
    exact compile_interpret_lit_on_footprint hok
  case case2 =>
    exact compile_interpret_var_on_footprint hwε hsm hok
  case case3 ih₁ ih₂ ih₃ =>
    exact compile_interpret_ite_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε) (λ hwε _ _ _ => ih₃ hwε)
  case case4 ih₁ ih₂ =>
    exact compile_interpret_and_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε)
  case case5 ih₁ ih₂ =>
    exact compile_interpret_or_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε)
  case case6 ih₁ =>
    exact compile_interpret_unaryApp_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε)
  case case7 ih₁ ih₂ =>
    exact compile_interpret_binaryApp_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε) (λ hwε _ _ _ => ih₂ hwε)
  case case8 ih₁ =>
    exact compile_interpret_hasAttr_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε)
  case case9 ih₁ =>
    exact compile_interpret_getAttr_on_footprint hwε hI₁ hI₂ hsm hft hok (λ hwε _ _ _ => ih₁ hwε)
  case case10 ih =>
    exact compile_interpret_set_on_footprint hwε hI₁ hI₂ hsm hft hok (λ x₁ hmem _ hwε _ _ _ => ih x₁ hmem hwε)
  case case11 ih =>
    exact compile_interpret_record_on_footprint hwε hI₁ hI₂ hsm hft hok (λ a₁ x₁ hsizeOf t hwε _ _ _ => ih a₁ x₁ hsizeOf hwε)
  case case12 ih =>
    exact compile_interpret_call_on_footprint hwε hI₁ hI₂ hsm hft hok (λ x₁ hmem _ hwε _ _ _ => ih x₁ hmem hwε)

end Cedar.Thm
