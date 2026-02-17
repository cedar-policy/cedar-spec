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
This file proves the compilation lemmas for `.record` expressions.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem compile_attr_expr_wfs {εnv : SymEnv} {axs : List (Attr × Expr)} {ats : List (Attr × Term)}
  (hwε : ∀ (ax : Attr × Expr), ax ∈ axs → SymEnv.WellFormedFor εnv ax.snd)
  (hok : List.Forall₂ (λ px pt => px.fst = pt.fst ∧ compile px.snd εnv = Except.ok pt.snd) axs ats) :
  ∀ a t, (a, t) ∈ ats → t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  intro a t ht
  replace ⟨x, hx, ha, hok⟩ := List.forall₂_implies_all_right hok (a, t) ht
  simp only at ha hok
  subst ha
  specialize hwε x hx
  exact compile_wf hwε hok

private theorem compile_interpret_ihs {axs : List (Attr × Expr)} {ats : List (Attr × Term)} {εnv : SymEnv} {I : Interpretation}
  (hI : Interpretation.WellFormed I εnv.entities)
  (hwε : ∀ (ax : Attr × Expr), ax ∈ axs → SymEnv.WellFormedFor εnv ax.snd)
  (ih : ∀ (a : Attr) (x : Expr), (a, x) ∈ axs → CompileInterpret x)
  (hok : List.Forall₂ (λ px pt => px.fst = pt.fst ∧ compile px.snd εnv = Except.ok pt.snd) axs ats) :
  List.Forall₂ (λ (a, x) (a', t) => a = a' ∧ compile x (εnv.interpret I) = .ok (t.interpret I)) axs ats
:= by
  cases axs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    exact hok
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨(a, t), heq, ttl, hok, htl⟩ := hok
    exists (a, t)
    have ih₁ := ih xhd.fst xhd.snd
    simp only [true_or, forall_const] at ih₁
    simp only [heq.left, ih₁ hI hwε.left heq.right, and_self, true_and]
    exists ttl
    simp only [htl, and_true]
    apply compile_interpret_ihs hI hwε.right _ hok
    intro a x h
    apply ih a x
    exact Or.inr h

private theorem compile_interpret_prods {axs : List (Attr × Expr)} {εnv : SymEnv} {I : Interpretation} {ats ats' : List (Attr × Term)}
  (h₁ : List.Forall₂ (λ (a, x) (a', t) => a = a' ∧ compile x (SymEnv.interpret I εnv) = Except.ok (Term.interpret I t)) axs ats)
  (h₂ : List.Forall₂ (λ (a, x) t' => (do .ok (a, ← compile x (SymEnv.interpret I εnv))) = Except.ok t') axs ats') :
  ats' = ats.map (Prod.map id (Term.interpret I))
:= by
  cases h₁
  case nil =>
    simp only [List.forall₂_nil_left_iff] at *
    exact h₂
  case cons xhd thd xtl ttl hhd htl =>
    simp only [List.forall₂_cons_left_iff] at *
    replace ⟨_, ttl', h₂, h₃, h₄⟩ := h₂
    simp only [hhd.right, Except.bind_ok, Except.ok.injEq] at h₂
    subst h₂ h₄
    simp only [List.map_cons, List.cons.injEq]
    constructor
    · unfold Prod.map id
      simp only [hhd]
    · exact compile_interpret_prods htl h₃

private theorem prod_snd_comp_prod_map_eq {f : α → γ} {g : β → δ} :
  Prod.snd ∘ Prod.map f g = g ∘ Prod.snd
:= by
  unfold Prod.map
  apply funext
  simp only [Function.comp_apply, implies_true]

theorem prod_map_id_comp_eq {f g : β → β} :
  Prod.map (@id α) f ∘ Prod.map id g = Prod.map id (f ∘ g)
:= by
  unfold Prod.map id
  apply funext
  simp only [Function.comp_apply, implies_true]

private theorem compile_interpret_record_ifAllSome_none {εs : SymEntities} {I : Interpretation} {ats : List (Attr × Term)}
  (hI  : Interpretation.WellFormed I εs)
  (hwφ : ∀ a t, (a, t) ∈ ats → Term.WellFormed εs t ∧ ∃ ty, Term.typeOf t = TermType.option ty) :
  Term.typeOf (recordOf (List.map (Prod.map id (option.get ∘ Term.interpret I)) ats)) =
  Term.typeOf (recordOf (List.map (Prod.map id (Term.interpret I ∘ option.get)) ats))
:= by
  simp only [recordOf, Map.make, List.canonicalize_of_map_fst, typeOf_term_record_eq, List.map_map,
    TermType.record.injEq, Map.mk.injEq]
  apply List.map_congr
  intro p hp
  replace hp := List.in_canonicalize_in_list hp
  simp only [Function.comp_apply, Prod.map, id_eq, Prod.mk.injEq, true_and]
  replace ⟨hwφ, ty, hty⟩ := hwφ p.fst p.snd (by simp only [hp])
  have hwi := interpret_term_wf hI hwφ
  rw [hty] at hwi
  simp only [
    interpret_option_get I hwφ hty,
    wf_option_get hwi.left hwi.right,
    wf_option_get' hI hwi.left hwi.right]

private theorem compile_interpret_record_ifAllSome_some {εs : SymEntities} {I : Interpretation} {ats : List (Attr × Term)} {ts : List Term}
  (hwφ : ∀ (a : Attr) (t : Term), (a, t) ∈ ats → Term.WellFormed εs t ∧ ∃ ty, Term.typeOf t = TermType.option ty)
  (hs : List.map (Term.interpret I ∘ Prod.snd) ats = List.map Term.some ts) :
  recordOf (List.map (Prod.map id (option.get ∘ Term.interpret I)) ats) =
  recordOf (List.map (Prod.map id (Term.interpret I ∘ option.get)) ats)
:= by
  simp only [recordOf, Map.make, List.canonicalize_of_map_fst, Term.record.injEq, Map.mk.injEq]
  apply List.map_congr
  intro p hp
  replace hp := List.in_canonicalize_in_list hp
  simp only [Prod.map, id_eq, Function.comp_apply, Prod.mk.injEq, true_and]
  replace ⟨hwφ, _, hty⟩ := hwφ p.fst p.snd (by simp only [hp])
  rw [← List.forall₂_iff_map_eq] at hs
  replace hs := List.forall₂_implies_all_left hs
  replace ⟨t, _, hs⟩ := hs p hp
  simp only [Function.comp_apply] at hs
  simp only [hs, pe_option_get_some, interpret_option_get I hwφ hty, pe_option_get'_some]

theorem interpret_attr_terms_wfls {ats : List (Attr × Term)} {I : Interpretation} {εs : SymEntities}
  (hI  : Interpretation.WellFormed I εs)
  (hwφ : ∀ a t, (a, t) ∈ ats → Term.WellFormed εs t ∧ ∃ ty, Term.typeOf t = TermType.option ty) :
  ∀ t ∈ ats.map (Term.interpret I ∘ Prod.snd),
    Term.WellFormedLiteral εs t ∧ ∃ ty, Term.typeOf t = TermType.option ty
:= by
  intro t' h'
  simp only [List.mem_map, Function.comp_apply] at h'
  replace ⟨(a, t), h, h'⟩ := h'
  simp only at h' ; subst h'
  replace ⟨hwφ, ty, hty⟩ := hwφ a t h
  have hwl := interpret_term_wfl hI hwφ
  simp only [hwl, true_and]
  exists ty

private theorem compile_interpret_record_ifAllSome {εs : SymEntities} {I : Interpretation} {ats : List (Attr × Term)}
  (hI  : Interpretation.WellFormed I εs)
  (hwφ : ∀ a t, (a, t) ∈ ats → Term.WellFormed εs t ∧ ∃ ty, Term.typeOf t = TermType.option ty) :
  ifAllSome (List.map (Term.interpret I ∘ Prod.snd) ats)
    (Term.some (recordOf (List.map (Prod.map id (option.get ∘ Term.interpret I)) ats))) =
  ifAllSome (List.map (Term.interpret I ∘ Prod.snd) ats)
    (Term.some (recordOf (List.map (Prod.map id (Term.interpret I ∘ option.get)) ats)))
:= by
  have hwi := interpret_attr_terms_wfls hI hwφ
  rcases (pe_wfls_of_type_option hwi) with ⟨_, hn⟩ | ⟨ts, hs⟩
  case inl =>
    simp only [pe_ifAllSome_none hn typeOf_term_some, Term.none.injEq]
    exact compile_interpret_record_ifAllSome_none hI hwφ
  case inr =>
    simp only [hs, pe_ifAllSome_some typeOf_term_some, Term.some.injEq]
    exact compile_interpret_record_ifAllSome_some hwφ hs

theorem compile_interpret_record {axs : List (Attr × Expr)} {εnv : SymEnv} {I : Interpretation} {t : Term}
  (hI  : I.WellFormed εnv.entities)
  (hwε : εnv.WellFormedFor (.record axs))
  (hok : compile (.record axs) εnv = .ok t)
  (ih  : ∀ a x, (a, x) ∈ axs → CompileInterpret x) :
  compile (.record axs) (εnv.interpret I) = .ok (t.interpret I)
:= by
  replace ⟨ats, hok, ht⟩ := compile_record_ok_implies hok
  subst ht
  replace hwε := wf_εnv_for_record_implies hwε
  have hwφ := compile_attr_expr_wfs hwε hok
  replace ih := compile_interpret_ihs hI hwε ih hok
  simp only [compile, List.mapM₂_eq_mapM λ (p : Attr × Expr) => match p with | (a₁, x₁) => do .ok (a₁, ← compile x₁ (SymEnv.interpret I εnv))]
  simp_do_let (axs.mapM λ (a₁, x₁) => do .ok (a₁, ← compile x₁ (SymEnv.interpret I εnv)))
  case error he =>
    replace ⟨ax, hmem, he⟩ := List.mapM_error_implies_exists_error he
    replace ⟨_, _, ih⟩ := List.forall₂_implies_all_left ih ax hmem
    simp only at ih
    simp only [ih, Except.bind_ok, reduceCtorEq] at he
  case ok ats' hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    replace ih := compile_interpret_prods ih hok'
    subst ih
    simp only [compileRecord, someOf, Except.ok.injEq]
    have hwg := wf_prods_implies_wf_map_snd (wf_prods_option_implies_wf_prods hwφ)
    have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd hwφ)
    simp only [interpret_ifAllSome hI hwg hwo hty, interpret_term_some,
      interpret_recordOf, List.map_map, prod_snd_comp_prod_map_eq, prod_map_id_comp_eq]
    exact compile_interpret_record_ifAllSome hI hwφ

private theorem compile_evaluate_ihs {axs : List (Attr × Expr)} {ats : List (Attr × Term)} {env : Env} {εnv : SymEnv}
  (heq : env ∼ εnv)
  (hwe : ∀ (ax : Attr × Expr), ax ∈ axs → env.WellFormedFor ax.snd)
  (hwε : ∀ (ax : Attr × Expr), ax ∈ axs → εnv.WellFormedFor ax.snd)
  (ih  : ∀ a x, (a, x) ∈ axs → CompileEvaluate x)
  (hok : List.Forall₂ (fun px pt => px.fst = pt.fst ∧ compile px.snd εnv = Except.ok pt.snd) axs ats) :
  List.Forall₂ (fun px pt => px.fst = pt.fst ∧ evaluate px.snd env.request env.entities ∼ pt.snd) axs ats
:= by
  cases axs
  case nil =>
    simp only [List.not_mem_nil, false_implies, forall_const, List.forall₂_nil_left_iff] at *
    assumption
  case cons xhd xtl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.forall₂_cons_left_iff, exists_and_left] at *
    replace ⟨thd, hok, ttl, htl, hts⟩ := hok
    subst hts
    exists thd
    simp only [hok.left,
      ih xhd.fst xhd.snd (by simp only [true_or]) heq hwe.left hwε.left hok.right, and_self,
      List.cons.injEq, true_and, exists_eq_right']
    apply compile_evaluate_ihs heq hwe.right hwε.right _ htl
    intro a x h
    apply ih a x
    exact Or.inr h

private theorem compile_evaluate_prods {axs : List (Attr × Expr)} {ats : List (Attr × Term)} {avs : List (Attr × Value)} {env : Env}
  (h₁ : List.Forall₂ (λ px pt => px.fst = pt.fst ∧ evaluate px.snd env.request env.entities ∼ pt.snd) axs ats)
  (h₂ : List.Forall₂ (λ px pv => bindAttr px.fst (evaluate px.snd env.request env.entities) = Except.ok pv) axs avs) :
  ∃ (ats' : List (Attr × Term)),
    ats = ats'.map (Prod.map id Term.some) ∧
    List.Forall₂ (λ pt pv => pt.fst = pv.fst ∧ pv.snd ∼ pt.snd) ats' avs
:= by
  cases axs
  case nil =>
    rw [List.forall₂_nil_left_iff] at h₁ h₂
    subst h₁ h₂
    exists []
    simp only [List.map_nil, List.Forall₂.nil, and_self]
  case cons xhd xtl =>
    replace ⟨thd, ttl, h₁, htl₁, hts⟩ := List.forall₂_cons_left_iff.mp h₁
    replace ⟨vhd, vtl, h₂, htl₂, hvs⟩ := List.forall₂_cons_left_iff.mp h₂
    subst hts hvs
    have ⟨tl', ih⟩ := compile_evaluate_prods htl₁ htl₂
    simp only [bindAttr] at h₂
    simp_do_let (evaluate xhd.snd env.request env.entities) at h₂
    rename_i v hok
    simp only [pure, Except.pure, Except.ok.injEq] at h₂
    subst h₂
    simp only [hok] at h₁
    have ⟨hd', hhd⟩ := same_ok_implies h₁.right
    exists ((thd.fst, hd') :: tl')
    simp only [ih.left, List.map_cons, Prod.map, id_eq, ← hhd.left, h₁.left, List.forall₂_cons,
      hhd.right, and_self, ih.right]

private theorem same_forall₂_implies_same_record {ats : List (Attr × Term)} {avs : List (Attr × Value)}
  (hs : List.Forall₂ (λ pt pv => pt.fst = pv.fst ∧ pv.snd ∼ pt.snd) ats avs) :
  Term.value? (Term.record (Map.make ats)) = some (Value.record (Map.make avs))
:= by
  simp only [Map.make]
  simp only [same_values_def] at hs
  rw [← @List.forallᵥ_def _ _ _ (λ t v => Term.value? t = some v)] at hs
  replace hs := List.canonicalize_preserves_forallᵥ _ _ _ hs
  generalize h₁ : (List.canonicalize Prod.fst ats) = ts
  generalize h₂ : (List.canonicalize Prod.fst avs) = vs
  rw [h₁, h₂] at hs
  clear h₁ h₂
  have ⟨avs', hts⟩ : ∃ avs', List.mapM' (λ x => Term.value?.attrValue? x.fst x.snd) ts = some avs' := by
    induction hs
    case nil =>
      exists []
    case cons thd vhd ttl _ h₁ _ ih =>
      replace ⟨vtl', ih⟩ := ih
      exists ((vhd.fst, some vhd.snd) :: vtl')
      simp only [List.mapM'_cons, value?_some_implies_attrValue?_some h₁.right, ih, Option.pure_def,
        Option.bind_some_fun, ← h₁.left]
  apply record_value?_some_implied_by hts
  replace hts := List.mapM'_some_eq_filterMap hts
  subst hts
  simp only [List.filterMap_filterMap]
  induction hs
  case nil =>
    simp only [List.filterMap_nil]
  case cons thd vhd ttl vtl h₁ _ ih =>
    simp only at h₁
    have hhd : Term.value?.attrValue? thd.fst thd.snd = some (vhd.fst, some vhd.snd) := by
      rw [← h₁.left, value?_some_implies_attrValue?_some h₁.right]
    simp only [List.filterMap_cons, hhd, Option.bind_some, Option.map_some, ih]

theorem compile_evaluate_record {axs : List (Attr × Expr)} {env : Env} {εnv : SymEnv} {t : Term}
  (heq : env ∼ εnv)
  (hwe : env.WellFormedFor (.record axs))
  (hwε : εnv.WellFormedFor (.record axs))
  (hok : compile (.record axs) εnv = .ok t)
  (ih  : ∀ a x, (a, x) ∈ axs → CompileEvaluate x) :
  evaluate (.record axs) env.request env.entities ∼ t
:= by
  replace ⟨ats, hok, ht⟩ := compile_record_ok_implies hok
  subst ht
  replace hwε := wf_εnv_for_record_implies hwε
  replace hwe := wf_env_for_record_implies hwe
  replace ih := compile_evaluate_ihs heq hwe hwε ih hok
  simp only [compileRecord, someOf, evaluate,
      List.mapM₂_eq_mapM λ (p : Attr × Expr) => bindAttr p.fst (evaluate p.snd env.request env.entities)]
  simp_do_let (axs.mapM λ p => bindAttr p.fst (evaluate p.snd env.request env.entities))
  case error he =>
    replace ⟨px, hx, he⟩ := List.mapM_error_implies_exists_error he
    replace ⟨pt, ht, ih⟩ := List.forall₂_implies_all_left ih px hx
    simp only [bindAttr] at he
    simp_do_let (evaluate px.snd env.request env.entities) at he
    case error =>
      simp at he ; subst he ; rename_i he
      rw [he] at ih
      have hmem : pt.snd ∈ List.map Prod.snd ats := by
        simp only [List.mem_map]
        exists pt
      exact same_error_implies_ifAllSome_error ih.right hmem typeOf_term_some
    case ok =>
      simp [pure, Except.pure] at he
  case ok avs hok' =>
    rw [List.mapM_ok_iff_forall₂] at hok'
    replace ⟨ats', hts, ih⟩ := compile_evaluate_prods ih hok'
    subst hts
    clear hok'
    simp only [List.map_map, prod_snd_comp_prod_map_eq, prod_map_id_comp_eq]
    rw [← List.map_map, pe_ifAllSome_some typeOf_term_some]
    have hid : (Prod.map (@id Attr) (option.get ∘ Term.some)) = id := by
      apply funext
      intro x
      simp only [Prod.map, id_eq, Function.comp_apply, pe_option_get_some]
    simp only [Same.same, SameResults, SameValues, recordOf, hid, List.map_id]
    exact same_forall₂_implies_same_record ih

end Cedar.Thm
