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

import Cedar.Thm.SymCC.Data.Basic
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.Interpret.Lit
import Cedar.Thm.SymCC.Term.Interpret.WF

/-!
# Properties of interpretations on symbolic enviornments

This file proves basic lemmas about the `interpret` function
on symbolic environments.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem interpret_entities_find?_some {εs : SymEntities} {I : Interpretation} {ety : EntityType} {d : SymEntityData}
  (h₁ : εs.find? ety = .some d) :
  (εs.interpret I).find? ety = .some (d.interpret I)
:= by
  simp [SymEntities.interpret]
  apply Map.find?_mapOnValues_some
  exact h₁

theorem interpret_entities_find?_none {εs : SymEntities} {I : Interpretation} {ety : EntityType}
  (h₁ : εs.find? ety = .none) :
  (εs.interpret I).find? ety = .none
:= by
  simp [SymEntities.interpret]
  apply Map.find?_mapOnValues_none
  exact h₁

theorem interpret_entities_isValidEntityUID (εs : SymEntities) (I : Interpretation) (uid : EntityUID) :
  εs.isValidEntityUID uid = (εs.interpret I).isValidEntityUID uid
:= by
  simp only [SymEntities.isValidEntityUID]
  split
  case h_1 d h =>
    simp only [interpret_entities_find?_some h, SymEntityData.interpret]
  case h_2 h =>
    simp only [interpret_entities_find?_none h]

theorem interpret_entities_isValidEntityType (εs : SymEntities) (I : Interpretation) (ety : EntityType) :
  εs.isValidEntityType ety = (εs.interpret I).isValidEntityType ety
:= by
  simp only [SymEntities.isValidEntityType, SymEntities.interpret]
  rw [Map.mapOnValues_contains (SymEntityData.interpret I)]

theorem interpret_entities_ancestors_none  {εs : SymEntities} {ety : EntityType} (I : Interpretation) :
  εs.ancestors ety = .none →
  (εs.interpret I).ancestors ety = .none
:= by
  simp only [SymEntities.ancestors, Option.bind_eq_bind, Option.bind_eq_none_iff]
  intro h₁ _ h₂
  cases h₃ : εs.find? ety
  case none =>
    replace h₃ := @interpret_entities_find?_none _ I _ h₃
    simp only [h₃, reduceCtorEq] at h₂
  case some =>
    simp only [h₃, Option.some.injEq, forall_eq', reduceCtorEq] at h₁

theorem interpret_entities_ancestors_some  {εs : SymEntities} {ety : EntityType} {ancs : Map EntityType UnaryFunction} (I : Interpretation) :
  εs.ancestors ety = .some ancs →
  (εs.interpret I).ancestors ety = .some (ancs.mapOnValues (UnaryFunction.interpret I))
:= by
  simp only [SymEntities.ancestors, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    SymEntities.interpret, forall_exists_index, and_imp]
  intro _ h₁ h₂
  simp only [Map.find?_mapOnValues_some _ h₁, SymEntityData.interpret, h₂,
    Option.some.injEq, exists_eq_left']

theorem interpret_entities_ancestorsOfType_none {εs : SymEntities} {ety ancTy : EntityType} {I : Interpretation} :
  εs.ancestorsOfType ety ancTy = .none →
  (εs.interpret I).ancestorsOfType ety ancTy = .none
:= by
  simp only [SymEntities.ancestorsOfType, Option.bind_eq_bind, Option.bind_eq_none_iff]
  intro h₁ _ h₂
  cases h₃ : SymEntities.ancestors εs ety
  case none =>
    replace h₃ := interpret_entities_ancestors_none I h₃
    simp only [h₃, reduceCtorEq] at h₂
  case some =>
    simp only [h₃, Option.some.injEq, forall_eq'] at h₁
    replace h₃ := interpret_entities_ancestors_some I h₃
    simp only [h₃, Option.some.injEq] at h₂
    subst h₂
    exact Map.find?_mapOnValues_none _ h₁

theorem interpret_entities_ancestorsOfType_some {εs : SymEntities} {ety ancTy : EntityType} {I : Interpretation} {f : UnaryFunction} :
  εs.ancestorsOfType ety ancTy = .some f →
  (εs.interpret I).ancestorsOfType ety ancTy = .some (f.interpret I)
:= by
  simp only [SymEntities.ancestorsOfType, Option.bind_eq_bind, Option.bind_eq_some_iff,
    forall_exists_index, and_imp]
  intro _ h₁ h₂
  simp only [interpret_entities_ancestors_some I h₁, Map.find?_mapOnValues_some _ h₂,
    Option.some.injEq, exists_eq_left']

theorem interpret_entities_tags_none {εs : SymEntities} {I : Interpretation} {ety : EntityType} :
  εs.tags ety = some none →
  (εs.interpret I).tags ety = some none
:= by
  simp only [SymEntities.tags, Option.map_eq_some_iff, forall_exists_index, and_imp]
  intro δ hf hτs
  replace hf := @interpret_entities_find?_some _ I _ _ hf
  exists (SymEntityData.interpret I δ)
  simp only [hf, SymEntityData.interpret, hτs, Option.map_none, and_self]

theorem interpret_entities_tags_some {εs : SymEntities} {I : Interpretation} {ety : EntityType} {τs : SymTags} :
  εs.tags ety = some τs →
  (εs.interpret I).tags ety = some (τs.interpret I)
:= by
  simp only [SymEntities.tags, Option.pure_def, Option.bind_some_fun, Option.map_eq_some_iff,
    forall_exists_index, and_imp]
  intro δ hf hτs
  replace hf := @interpret_entities_find?_some _ I _ _ hf
  exists (SymEntityData.interpret I δ)
  simp only [hf, SymEntityData.interpret, hτs, Option.map_some, and_self]

theorem interpret_entities_same_domain (εs : SymEntities) (I : Interpretation) :
  SameDomain εs (εs.interpret I)
:= And.intro (interpret_entities_isValidEntityUID εs I) (interpret_entities_isValidEntityType εs I)

theorem interpret_uf_wf {εs : SymEntities} {I : Interpretation} {f : UnaryFunction} :
  I.WellFormed εs →
  f.WellFormed εs →
  (f.interpret I).WellFormed εs ∧
  (f.interpret I).argType = f.argType ∧
  (f.interpret I).outType = f.outType
:= by
  intro h₁ h₂
  cases f <;>
  simp only [UnaryFunction.WellFormed] at * <;>
  simp only [UnaryFunction.interpret, and_self, and_true]
  case udf => exact h₂
  case uuf f =>
    simp only [UnaryFunction.argType, UnaryFunction.outType]
    replace h₁ := h₁.right.left f h₂
    simp only [Interpretation.WellFormed.WellFormedUUFInterpretation] at h₁
    simp only [h₁, and_self]

theorem interpret_εdata_wf {εs : SymEntities} {I : Interpretation} {ety : EntityType} {εd : SymEntityData} :
  I.WellFormed εs →
  εd.WellFormed εs ety →
  (εd.interpret I).WellFormed εs ety
:= by
  simp only [SymEntityData.WellFormed, and_imp]
  intro h₁ h₂ h₃ h₄ h₅
  have h₆ := interpret_uf_wf h₁ h₂
  simp only [SymEntityData.interpret, h₆, h₃, h₄, true_and]
  intro hwf
  simp only [← Map.mapOnValues_wf, hwf, Option.map_eq_some_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, true_and]
  intro htags hmems
  constructor
  · intro pty f h₇
    cases h : Map.find? εd.ancestors pty
    case none =>
      replace h := Map.find?_mapOnValues_none (UnaryFunction.interpret I) h
      simp only [h, reduceCtorEq] at h₇
    case some f' =>
      have h' := Map.find?_mapOnValues_some (UnaryFunction.interpret I) h
      simp only [h₇, Option.some.injEq] at h'  ; subst h'
      specialize h₅ pty f' h
      have h₇ := interpret_uf_wf h₁ h₅.left
      simp only [h₇, h₅, and_self]
  · constructor
    · intro τs h₇
      specialize htags τs h₇
      simp only [SymTags.WellFormed] at *
      simp only [SymTags.interpret, interpret_uf_wf h₁ htags.left, htags,
        interpret_uf_wf h₁ htags.right.right.right.left, and_self]
    · exact hmems

theorem interpret_εntities_wf {εs : SymEntities} {I : Interpretation} :
  εs.WellFormed →
  I.WellFormed εs →
  (εs.interpret I).WellFormed
:= by
  simp only [SymEntities.WellFormed, SymEntities.interpret]
  intro h₀ h₂
  simp only [← Map.mapOnValues_wf, h₀.left, true_and]
  intro ety d h₃
  have h₁ := h₀.right ety
  cases h₄ : (Map.find? εs ety)
  case none =>
    replace h₄ := Map.find?_mapOnValues_none (SymEntityData.interpret I) h₄
    simp only [h₃, reduceCtorEq] at h₄
  case some d' =>
    specialize h₁ d' h₄
    have h₅ := Map.find?_mapOnValues_some (SymEntityData.interpret I) h₄
    simp only [h₃, Option.some.injEq] at h₅
    subst h₅
    have h₆ := interpret_εdata_wf h₂ h₁
    exact wf_εdata_same_domain (interpret_entities_same_domain εs I) h₆

private theorem interpret_term_wf_fun_typeOf
  {εs : SymEntities} {I : Interpretation} {t : Term}
  {f : TermType → Bool} :
  I.WellFormed εs → t.WellFormed εs → f t.typeOf →
  (t.interpret I).WellFormed εs ∧ f (t.interpret I).typeOf
:= by
  intro h₁ h₂ h₃
  have ⟨h₄, h₅⟩ := interpret_term_wf h₁ h₂
  simp only [h₄, h₅, h₃, and_self]

theorem interpret_ρeq_wf {εs : SymEntities} {ρeq : SymRequest} {I : Interpretation} :
  I.WellFormed εs →
  ρeq.WellFormed εs →
  (ρeq.interpret I).WellFormed εs
:= by
  intro h₁ h₂
  have ⟨hp, hp', ha, ha', hr, hr', hc, hc'⟩ := h₂
  simp [SymRequest.WellFormed, SymRequest.interpret,
    interpret_term_wf_fun_typeOf h₁ hp hp',
    interpret_term_wf_fun_typeOf h₁ ha ha',
    interpret_term_wf_fun_typeOf h₁ hr hr',
    interpret_term_wf_fun_typeOf h₁ hc hc']

theorem interpret_εnv_wf {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormed →
  I.WellFormed εnv.entities →
  (εnv.interpret I).WellFormed
:= by
  intro ⟨hρeq, hεs⟩ hI
  have hdom := interpret_entities_same_domain εnv.entities I
  simp only [SymEnv.interpret, SymEnv.WellFormed]
  constructor
  · exact interpret_ρeq_wf (wf_interpretation_same_domain hdom hI) (wf_ρeq_same_domain hdom hρeq)
  · exact interpret_εntities_wf hεs hI

theorem interpret_εnv_wf_for_expr {x : Expr} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormedFor x →
  I.WellFormed εnv.entities →
  (εnv.interpret I).WellFormedFor x
:= by
  intro ⟨hwε, hvr⟩ hI
  simp only [SymEnv.WellFormedFor]
  constructor
  · exact interpret_εnv_wf hwε hI
  · exact expr_valid_refs_same_domain (interpret_entities_same_domain εnv.entities I) hvr

theorem interpret_εnv_wf_for_policies {ps : Policies} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormedForPolicies ps →
  I.WellFormed εnv.entities →
  (εnv.interpret I).WellFormedForPolicies ps
:= by
  intro ⟨hwε, hvr⟩ hI
  simp only [SymEnv.WellFormedForPolicies, interpret_εnv_wf hwε hI, true_and]
  intro p hin
  exact expr_valid_refs_same_domain (interpret_entities_same_domain εnv.entities I) (hvr p hin)

theorem interpret_uf_lit {εs : SymEntities} {I : Interpretation} {f : UnaryFunction} :
  I.WellFormed εs →
  f.WellFormed εs →
  (f.interpret I).isLiteral
:= by
  intro hI hwf
  simp only [UnaryFunction.interpret]
  split <;>
  simp only [UnaryFunction.isLiteral] <;>
  simp only [UnaryFunction.WellFormed] at hwf
  · exact wf_udf_implies_lit (wf_interpretation_implies_wf_udf hI hwf).left
  · exact wf_udf_implies_lit hwf

theorem interpret_εnv_lit {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormed →
  I.WellFormed εnv.entities →
  (εnv.interpret I).isLiteral
:= by
  intro hw hI
  simp only [SymEnv.isLiteral, SymEnv.interpret, Bool.and_eq_true]
  constructor
  case left =>
    have ⟨hwp, _, hwa, _, hwr, _, hwc, _⟩ := wf_εnv_implies_wf_ρeq hw
    simp only [SymRequest.isLiteral, SymRequest.interpret,
      interpret_term_lit hI hwp, interpret_term_lit hI hwa,
      interpret_term_lit hI hwr, interpret_term_lit hI hwc, Bool.and_self]
  case right =>
    simp only [SymEntities.isLiteral, SymEntities.interpret, List.all_eq_true]
    simp only [Map.toList, Map.kvs, Map.mapOnValues, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro tyδ hin
    rw [Map.in_list_iff_find?_some hw.right.left] at hin
    replace hw := hw.right.right tyδ.1 tyδ.2 hin
    simp only [SymEntityData.isLiteral, SymEntityData.interpret, Bool.and_eq_true, List.all_eq_true]
    constructor
    · constructor
      · exact interpret_uf_lit hI hw.left
      · simp only [Map.toList, Map.kvs, Map.mapOnValues, List.mem_map, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
        intro tyf hin'
        replace hw := hw.right.right.right
        rw [Map.in_list_iff_find?_some hw.right.left] at hin'
        have hwl := hw.left tyf.1 tyf.2 hin'
        exact interpret_uf_lit hI hwl.left
    · simp only [Option.all]
      split <;> try rfl
      rename_i τs' hτs
      simp only [Option.map_eq_some_iff] at hτs
      replace ⟨τs, hτs, heq⟩ := hτs
      subst heq
      have hwr := hw.right.right.right.right.right.left τs hτs
      simp only [SymTags.isLiteral, SymTags.interpret, interpret_uf_lit hI hwr.left,
        interpret_uf_lit hI hwr.right.right.right.left, Bool.and_self]

end Cedar.Thm
