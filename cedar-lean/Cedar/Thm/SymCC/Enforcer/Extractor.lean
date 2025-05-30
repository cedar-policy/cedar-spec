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

import Cedar.Thm.SymCC.Concretizer
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Env.SWF
import Cedar.Thm.SymCC.Enforcer.Asserts
import Cedar.Thm.SymCC.Enforcer.Footprint
import Cedar.Thm.SymCC.Enforcer.Util
import Cedar.Thm.SymCC.Compiler

/-!
This file proves properties of the counterexample extraction functions
in `Cedar/SymCC/Extractor.lean`.
--/

namespace Cedar.Thm

open Data Spec SymCC Factory

private theorem footprintUIDs_wf {xs : List Expr} {εnv : SymEnv} {I : Interpretation} :
  (Interpretation.repair.footprintUIDs xs εnv I).WellFormed
:= by
  simp only [Interpretation.repair.footprintUIDs, Set.mapUnion_wf, true_and]

private theorem footprintUIDs_valid {xs : List Expr} {εnv : SymEnv} {I : Interpretation}
  (hwε : εnv.WellFormed)
  (hvr : ∀ (x : Expr), x ∈ xs → εnv.entities.ValidRefsFor x)
  (hI : I.WellFormed εnv.entities) :
  ∀ uid ∈ Interpretation.repair.footprintUIDs xs εnv I, εnv.entities.isValidEntityUID uid
:= by
  simp only [Interpretation.repair.footprintUIDs]
  intro uid hin
  simp only [Set.mem_mapUnion_iff_mem_exists, Function.comp_apply] at hin
  replace ⟨t, hinₓ, hin⟩ := hin
  rw [Set.in_list_iff_in_set, mem_footprints_iff] at hinₓ
  replace ⟨x, hinₓ, hinₜ⟩ := hinₓ
  have hwf := mem_footprint_wf (And.intro hwε (hvr x hinₓ)) hinₜ
  have ⟨ety, hty⟩ := mem_footprint_option_entity hinₜ
  have heq := interpret_option_entity_term hI hwf hty
  rcases heq with heq | ⟨uid', heq, _⟩ <;> simp only [heq] at hin
  · simp only [Term.entityUIDs, Set.empty_no_elts] at hin
  · apply wf_term_implies_valid_uids _ _ hin
    simp only [← heq, interpret_term_wf hI hwf]

private theorem repairAncestors_default_wfl {εs : SymEntities} {f : UDF}
  (hlt : Term.WellFormedLiteral εs f.default)
  (hty : f.default.typeOf = f.out) :
  Term.WellFormedLiteral εs (UUF.repairAncestors.default f) ∧
  (UUF.repairAncestors.default f).typeOf = f.out
:= by
  simp only [UUF.repairAncestors.default]
  split <;> try simp only [hlt, hty, and_self]
  rename_i ty heq
  replace hlt := typeOf_wf_term_is_wf hlt.left
  simp only [hty, heq] at hlt
  cases hlt <;> rename_i hlt
  replace hlt := wf_term_set_empty hlt
  simp only [Set.empty, hlt, heq, and_true]
  exact And.intro hlt.left (lit_term_set_empty ty)

private theorem repairAncestors_table_wf {uids : Set EntityUID} {f : UDF} :
  uids.WellFormed →
  (UUF.repairAncestors.table uids f).WellFormed
:= by
  intro hw
  rw [Set.wf_iff_sorted] at hw
  simp only [UUF.repairAncestors.table, Map.wf_iff_sorted, Map.toList, Map.kvs]
  generalize h : uids.elts = elts
  simp only [h] at hw
  clear h
  induction hw
  case nil =>
    simp only [List.filterMap_nil]
    exact List.SortedBy.nil
  case cons_nil =>
    simp only [List.filterMap_cons, List.filterMap_nil]
    split
    · exact List.SortedBy.nil
    . exact List.SortedBy.cons_nil
  case cons_cons h₁ h₂ ih =>
    simp only [List.filterMap_cons] at *
    rename_i x y ys
    simp only [id_eq] at h₁
    split <;> split <;>
    rename_i hfy <;>
    simp only [hfy] at ih <;>
    try exact ih
    · rename_i b hfx _
      simp only [UUF.repairAncestors.entry, Option.ite_none_right_eq_some, Option.some.injEq] at hfx
      replace hfx := hfx.right ; subst hfx
      cases hys : (ys.filterMap (UUF.repairAncestors.entry f))
      case nil =>
        exact List.SortedBy.cons_nil
      case cons yhd ytl =>
        simp only [hys] at ih
        apply List.SortedBy.cons_cons _ ih
        simp only
        have hin : yhd ∈ List.filterMap (UUF.repairAncestors.entry f) ys := by
          simp only [hys, List.mem_cons, true_or]
        simp only [List.mem_filterMap] at hin
        replace ⟨uid, hin, hfu⟩ := hin
        replace h₂ := List.sortedBy_implies_head_lt_tail h₂ uid hin
        simp only [id_eq] at h₂
        replace h₁ := StrictLT.transitive x y uid h₁ h₂
        simp only [UUF.repairAncestors.entry, Option.ite_none_right_eq_some, Option.some.injEq] at hfu
        replace hfu := hfu.right ; subst hfu
        simp only [LT.lt] at h₁
        simp only [LT.lt, Term.lt, TermPrim.lt, h₁, decide_true]
    · rename_i hfx _ _
      simp only [UUF.repairAncestors.entry, Option.ite_none_right_eq_some, Option.some.injEq] at hfx hfy
      replace hfx := hfx.right
      replace hfy := hfy.right
      subst hfx hfy
      apply List.SortedBy.cons_cons _ ih
      simp only [LT.lt] at h₁
      simp only [LT.lt, Term.lt, TermPrim.lt, h₁, decide_true]

private theorem repairAncestors_wf {uids : Set EntityUID} {f : UDF} {εs : SymEntities}
  (hwf : f.WellFormed εs)
  (hwu : uids.WellFormed)
  (hwv : ∀ uid ∈ uids, εs.isValidEntityUID uid) :
  UDF.WellFormed εs ⟨f.arg, f.out, UUF.repairAncestors.table uids f, UUF.repairAncestors.default f⟩
:= by
  simp only [UDF.WellFormed, repairAncestors_default_wfl hwf.left hwf.right.left, repairAncestors_table_wf hwu, true_and]
  intro tᵢ tₒ hin
  simp only [Map.toList, Map.kvs, UUF.repairAncestors.table, List.mem_filterMap] at hin
  replace ⟨uid, hin, heq⟩ := hin
  rw [Set.in_list_iff_in_set] at hin
  simp only [UUF.repairAncestors.entry, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at heq
  replace ⟨hty, heq, heq'⟩ := heq
  subst heq heq'
  have hwl := wfl_entity (hwv uid hin)
  simp only [hwl, hty, true_and]
  simp only [Term.WellFormedLiteral, pe_app_wfl hwl hwf, and_true]
  apply wf_app hwl.left
  · simp only [hty, UnaryFunction.argType]
  · simp only [UnaryFunction.WellFormed, hwf]

theorem repair_wf {xs : List Expr} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormed →
  (∀ x ∈ xs, εnv.entities.ValidRefsFor x) →
  I.WellFormed εnv.entities →
  (I.repair xs εnv).WellFormed εnv.entities
:= by
  intro hwε hvr hI
  simp only [Interpretation.repair]
  apply And.intro hI.left
  apply And.intro _ hI.right.right
  simp only
  intro f hwf
  have hwf' := hI.right.left f hwf
  simp only [Interpretation.repair.funs]
  split <;> try exact hwf'
  rename_i f' hf
  simp only [Interpretation.repair.footprintAncestors] at hf
  replace hf := Map.find?_mem_toList hf
  simp only [Map.toList, Map.kvs, List.mem_map, Prod.mk.injEq] at hf
  replace ⟨_, hin, hf', hf⟩ := hf
  rw [eq_comm] at hf'
  subst hf' hf
  simp only [Interpretation.WellFormed.WellFormedUUFInterpretation, UUF.repairAncestors, hwf'.right,
    and_self, and_true]
  exact repairAncestors_wf hwf'.left footprintUIDs_wf (footprintUIDs_valid hwε hvr hI)

private theorem env_wf_same {xs : List Expr} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormed →
  (∀ x ∈ xs, εnv.entities.ValidRefsFor x) →
  I.WellFormed εnv.entities →
  ∃ env : Env,
    env ∼ εnv.interpret I ∧
    env.WellFormed ∧
    ∀ x ∈ xs, env.entities.ValidRefsFor x
:= by
  intro hwε hvr hI
  have ⟨env, heq, hwf⟩ := exists_wf_env (wf_εnv_valid_refs_implies_wf_εnv_for_set hwε hvr) hI
  exists env
  simp only [heq, hwf.left, true_and]
  intro x hin
  exact (wf_env_for_set_implies hwf x hin).right

theorem repair_env_wf_same {xs : List Expr} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormed →
  (∀ x ∈ xs, εnv.entities.ValidRefsFor x) →
  I.WellFormed εnv.entities →
  (I.repair xs εnv).WellFormed εnv.entities ∧
  ∃ env : Env,
    env ∼ εnv.interpret (I.repair xs εnv) ∧
    env.WellFormed ∧
    ∀ x ∈ xs, env.entities.ValidRefsFor x
:= by
  intro hwε hvr hI
  replace hI := repair_wf hwε hvr hI
  exact And.intro hI (env_wf_same hwε hvr hI)

theorem extract?_env_wf_same {xs : List Expr} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormed →
  (∀ x ∈ xs, εnv.entities.ValidRefsFor x) →
  I.WellFormed εnv.entities →
  ∃ env : Env,
    εnv.extract? xs I = .some env ∧
    env ∼ εnv.interpret (I.repair xs εnv) ∧
    env.WellFormed ∧
    ∀ x ∈ xs, env.entities.ValidRefsFor x
:= by
  intro hwε hvr hI
  simp only [SymEnv.extract?]
  replace hI := repair_wf hwε hvr hI
  have hlit := interpret_εnv_lit hwε hI
  replace hwε' := interpret_εnv_wf_for_expr (wf_εnv_valid_refs_implies_wf_εnv_for_set hwε hvr) hI
  have ⟨env, h⟩ := concretize?_wfl_implies_some (And.intro hwε' hlit)
  have hwf := concretize?_some_wf hwε' h
  exists env
  simp only [h, concretize?_some_same hwε' h, hwf.left, true_and]
  intro x hin
  exact (wf_env_for_set_implies hwf x hin).right

private theorem footprintAncestors_eq {xs : List Expr} {ety ancTy : EntityType} {f : UUF} {δ : SymEntityData} {εnv : SymEnv} {I : Interpretation}
  (hδ  : Map.find? εnv.entities ety = some δ)
  (hf  : δ.ancestors.find? ancTy = some (UnaryFunction.uuf f)) :
  (Interpretation.repair.footprintAncestors xs εnv I).find? f =
  .some (f.repairAncestors (Interpretation.repair.footprintUIDs xs εnv I) I)
:= by
  simp only [Interpretation.repair.footprintAncestors]
  apply Map.mem_toList_find?
  · simp only [Map.wf_iff_sorted, Map.toList, Map.kvs]
    rw [@List.map_eq_implies_sortedBy _ _ _ _ _ _ id _ εnv.entities.uufAncestors.elts]
    · simp only [SymEntities.uufAncestors, ← Set.wf_iff_sorted, Set.mapUnion_wf]
    · simp only [List.map_map]
      apply List.map_congr
      simp only [Function.comp_apply, id_eq, implies_true]
  · simp only [Map.toList, Map.kvs, List.mem_map, Prod.mk.injEq]
    exists f
    simp only [SymEntities.uufAncestors, Set.in_list_iff_in_set, Set.mem_mapUnion_iff_mem_exists,
      Function.comp_apply, and_self, and_true]
    exists (ety, δ)
    replace hδ := Map.find?_mem_toList hδ
    replace hf := Map.find?_mem_toList hf
    simp only [Map.toList] at hδ hf
    simp only [hδ, SymEntityData.uufAncestors, ← Set.make_mem, List.mem_filterMap,
      Function.comp_apply, true_and]
    exists (ancTy, UnaryFunction.uuf f)

private theorem not_mem_uids_implies_repairAncestors_find?_none {uid : EntityUID} {uids : Set EntityUID} {f : UUF} {I : Interpretation}
  (hft : ¬uid ∈ uids) :
  (f.repairAncestors uids I).table.find? (Term.entity uid) = .none
:= by
  by_contra hc
  simp only [Option.ne_none_iff_isSome, Option.isSome_iff_exists] at hc
  replace ⟨t, hc⟩ := hc
  replace hc := Map.find?_mem_toList hc
  simp only [Map.toList, Map.kvs, UUF.repairAncestors, UUF.repairAncestors.table, List.mem_filterMap,
    UUF.repairAncestors.entry, Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq,
    Term.prim.injEq, TermPrim.entity.injEq] at hc
  replace ⟨uid', hc, _, heq, _⟩ := hc
  subst heq
  simp only [Set.in_list_iff_in_set] at hc
  contradiction

theorem not_mem_footprintUIDs_implies_empty_ancs {uid : EntityUID} {ety : EntityType} {f : UUF} {δ : SymEntityData} {xs : List Expr} {εnv : SymEnv} {I : Interpretation}
  (hwε : εnv.WellFormed)
  (hI  : I.WellFormed εnv.entities)
  (hδ  : Map.find? εnv.entities uid.ty = some δ)
  (hf  : δ.ancestors.find? ety = some (UnaryFunction.uuf f))
  (hft : ¬uid ∈ Interpretation.repair.footprintUIDs xs εnv I) :
  app ((UnaryFunction.uuf f).interpret (I.repair xs εnv)) (Term.entity uid) =
  Term.set Set.empty (TermType.entity ety)
:= by
  simp only [app, UnaryFunction.interpret, Interpretation.repair, Interpretation.repair.funs,
    footprintAncestors_eq hδ hf, term_prim_is_lit, ↓reduceIte,
    not_mem_uids_implies_repairAncestors_find?_none hft]
  simp only [UUF.repairAncestors, UUF.repairAncestors.default]
  replace hwε := (hwε.right.right uid.ty δ hδ).right.right.right.left ety _ hf
  replace hI := (hI.right.left f hwε.left).right.right
  replace hwε := hwε.right.right
  simp only [UnaryFunction.outType] at hwε
  simp only [← hI, hwε]

private theorem mem_uids_implies_repairAncestors_find?_eq {uid : EntityUID} {uids : Set EntityUID} {f : UUF} {I : Interpretation}
  (hwu : uids.WellFormed)
  (hft : uid ∈ uids)
  (hty : (I.funs f).arg = TermType.entity uid.ty) :
  (f.repairAncestors uids I).table.find? (Term.entity uid) =
  app (UnaryFunction.udf (I.funs f)) (Term.entity uid)
:= by
  apply Map.mem_toList_find? (repairAncestors_table_wf hwu)
  simp only [Map.toList, Map.kvs, UUF.repairAncestors.table, List.mem_filterMap]
  exists uid
  simp only [Set.in_list_iff_in_set, hft, UUF.repairAncestors.entry, typeOf_term_prim_entity, hty,
    ↓reduceIte, and_self]

theorem mem_footprintUIDs_implies_eq_ancs {uid : EntityUID} {ety : EntityType} {f : UUF} {δ : SymEntityData} {xs : List Expr} {εnv : SymEnv} {I : Interpretation}
  (hwε : εnv.WellFormed)
  (hI  : I.WellFormed εnv.entities)
  (hδ  : Map.find? εnv.entities uid.ty = some δ)
  (hf  : δ.ancestors.find? ety = some (UnaryFunction.uuf f))
  (hft : uid ∈ Interpretation.repair.footprintUIDs xs εnv I) :
  app ((UnaryFunction.uuf f).interpret (I.repair xs εnv)) (Term.entity uid) =
  app ((UnaryFunction.uuf f).interpret I) (Term.entity uid)
:= by
  rw [app.eq_def]
  simp only [UnaryFunction.interpret, Interpretation.repair, Interpretation.repair.funs,
    footprintAncestors_eq hδ hf, term_prim_is_lit, ↓reduceIte]
  replace hwε := (hwε.right.right uid.ty δ hδ).right.right.right.left ety _ hf
  replace hI := (hI.right.left f hwε.left).right.left
  replace hwε := hwε.right.left
  simp only [UnaryFunction.argType, hI] at hwε
  simp only [mem_uids_implies_repairAncestors_find?_eq footprintUIDs_wf hft hwε]

theorem mem_footprintUIDs_mem_footprints {uid : EntityUID} {xs : List Expr} {εnv : SymEnv} {I : Interpretation}
  (hwε : εnv.WellFormed)
  (hvr : ∀ x ∈ xs, εnv.entities.ValidRefsFor x)
  (hI  : I.WellFormed εnv.entities)
  (hin : uid ∈ Interpretation.repair.footprintUIDs xs εnv I) :
  ∃ t ∈ footprints xs εnv, t.interpret I = Term.some (Term.entity uid)
:= by
  simp only [Interpretation.repair.footprintUIDs, Set.mem_mapUnion_iff_mem_exists,
    Set.in_list_iff_in_set, Function.comp_apply] at hin
  replace ⟨t, hinₜ, hin⟩ := hin
  have hinₜ' := hinₜ
  simp only [mem_footprints_iff] at hinₜ
  replace ⟨x, hinₓ, hinₜ⟩ := hinₜ
  have hwt := mem_footprint_wf (And.intro hwε (hvr x hinₓ)) hinₜ
  have ⟨ety, hty⟩ := mem_footprint_option_entity hinₜ
  have ht := interpret_option_entity_term hI hwt hty
  rcases ht with ht | ⟨uid', ht, _⟩ <;>
  simp only [ht, Term.entityUIDs] at hin
  · simp only [Set.empty_no_elts] at hin
  · simp only [TermPrim.entityUIDs, Set.mem_singleton_iff_eq] at hin
    subst hin
    exists t

theorem mem_mem_footprints_footprintUIDs {t : Term} {uid : EntityUID} {xs : List Expr} {εnv : SymEnv} {I : Interpretation}
  (hin : t ∈ footprints xs εnv)
  (ht  : t.interpret I = Term.some (Term.entity uid)) :
  uid ∈ Interpretation.repair.footprintUIDs xs εnv I
:= by
  simp only [Interpretation.repair.footprintUIDs, Set.mem_mapUnion_iff_mem_exists, Function.comp_apply]
  exists t
  simp only [Set.in_list_iff_in_set, hin, ht, Term.entityUIDs, TermPrim.entityUIDs,
    Set.mem_singleton, and_self]

private theorem interpret_term_isBasic_repair_eq (xs : List Expr) {t : Term} {εnv : SymEnv} (I : Interpretation)
  (hwt : t.WellFormed εnv.entities)
  (hbt : t.isBasic) :
  t.interpret I = t.interpret (I.repair xs εnv)
:= by
  simp only [Term.isBasic] at hbt
  split at hbt
  · simp only [interpret_term_var, Interpretation.repair]
  · simp only [interpret_term_lit_id I (And.intro hwt hbt),
      interpret_term_lit_id (I.repair xs εnv) (And.intro hwt hbt)]

private theorem interpret_request_repair_eq {xs : List Expr} {εnv : SymEnv} {I : Interpretation}
  (hwε : εnv.request.StronglyWellFormed εnv.entities) :
  εnv.request.interpret I = εnv.request.interpret (Interpretation.repair xs εnv I)
:= by
  have ⟨hwtp, _, hwta, _, hwtr, _, hwtc, _⟩ := hwε.left
  have ⟨hbtp, hbta, hbtr, hbtc⟩ := hwε.right
  simp only [SymRequest.interpret,
    interpret_term_isBasic_repair_eq xs I hwtp hbtp,
    interpret_term_isBasic_repair_eq xs I hwta hbta,
    interpret_term_isBasic_repair_eq xs I hwtr hbtr,
    interpret_term_isBasic_repair_eq xs I hwtc hbtc]

private theorem interpret_non_ancestor_uuf_repair_eq {εnv : SymEnv} {f : UUF} (I : Interpretation)
  (hf : ¬ f ∈ εnv.entities.uufAncestors) :
  I.funs f = (Interpretation.repair xs εnv I).funs f
:= by
  simp only [Interpretation.repair, Interpretation.repair.funs, Interpretation.repair.footprintAncestors]
  split <;> try rfl
  rename_i heq
  replace heq := Map.find?_mem_toList heq
  simp only [Map.toList, Map.kvs, List.mem_map, Prod.mk.injEq] at heq
  replace ⟨f', hf', heq, _⟩ := heq
  subst heq
  rw [Set.in_list_iff_in_set] at hf'
  contradiction

private theorem type_of_ancestor_uuf_eq {εnv : SymEnv} {f : UUF}
  (hwε : εnv.entities.WellFormed)
  (hf : f ∈ εnv.entities.uufAncestors) :
  ∃ ety aty, f.arg = .entity ety ∧ f.out = .set (.entity aty)
:= by
  simp only [SymEntities.uufAncestors, Set.in_list_iff_in_set, Set.mem_mapUnion_iff_mem_exists,
    Function.comp_apply] at hf
  replace ⟨(ety, δ), hδ, hf⟩ := hf
  simp only [SymEntityData.uufAncestors, ← Set.make_mem, List.mem_filterMap, Function.comp_apply] at hf
  replace ⟨(aty, f'), hf', hf⟩ := hf
  simp only [UnaryFunction.uuf?] at hf
  split at hf <;> simp only [Option.some.injEq, reduceCtorEq] at hf
  subst hf
  rename_i f
  rw [Map.in_list_iff_find?_some hwε.left] at hδ
  have hwδ := hwε.right ety δ hδ
  rw [Map.in_list_iff_find?_some hwδ.right.right.right.right.left] at hf'
  exists ety, aty
  replace hwδ := (hwδ.right.right.right.left aty (.uuf f) hf').right
  simp only [UnaryFunction.argType, UnaryFunction.outType] at hwδ
  exact hwδ

private theorem interpret_attrs_repair_eq  {εnv : SymEnv} {ety : EntityType} {δ : SymEntityData} (xs : List Expr) (I : Interpretation)
  (hwε : εnv.entities.WellFormed)
  (hδ : Map.find? εnv.entities ety = some δ) :
  δ.attrs.interpret I = δ.attrs.interpret (I.repair xs εnv)
:= by
  cases hf : δ.attrs <;>
  simp only [UnaryFunction.interpret, UnaryFunction.udf.injEq]
  rename_i f
  apply interpret_non_ancestor_uuf_repair_eq I
  by_contra hc
  replace ⟨_, aty, _, hty⟩ := type_of_ancestor_uuf_eq hwε hc
  have hwδ := hwε.right ety δ hδ
  have hty' := hwδ.right.right.left
  have ⟨_, hrty⟩ := isCedarRecordType_implies_term_record_type hty'
  simp only [UnaryFunction.outType, hf, hty, reduceCtorEq] at hty' hrty

private theorem interpret_tags_repair_eq  {εnv : SymEnv} {ety : EntityType} {δ : SymEntityData} {τs : SymTags} (xs : List Expr) (I : Interpretation)
  (hwε : εnv.entities.WellFormed)
  (hδ : Map.find? εnv.entities ety = some δ)
  (hτs : δ.tags = some τs) :
  τs.interpret I = τs.interpret (I.repair xs εnv)
:= by
  simp only [SymTags.interpret, Interpretation.repair, SymTags.mk.injEq]
  have hwδ := hwε.right ety δ hδ
  have hwτ := hwδ.right.right.right.right.right.left τs hτs
  simp [SymTags.WellFormed ] at hwτ
  constructor
  · cases hk : τs.keys <;>
    simp only [UnaryFunction.interpret, UnaryFunction.udf.injEq]
    apply interpret_non_ancestor_uuf_repair_eq I
    by_contra hc
    replace ⟨_, _, _, hty⟩ := type_of_ancestor_uuf_eq hwε hc
    replace hwτ := hwτ.right.right.left
    simp only [UnaryFunction.outType, hk, hty, TermType.set.injEq, TermType.prim.injEq, reduceCtorEq] at hwτ
  · cases hv : τs.vals <;>
    simp only [UnaryFunction.interpret, UnaryFunction.udf.injEq]
    apply interpret_non_ancestor_uuf_repair_eq I
    by_contra hc
    replace ⟨_, _, hty, _⟩ := type_of_ancestor_uuf_eq hwε hc
    replace hwτ := hwτ.right.right.right.right.left
    simp only [UnaryFunction.argType, hv, hty, reduceCtorEq] at hwτ

theorem εnv_same_on_footprints {xs : List Expr} {εnv : SymEnv} {I : Interpretation}
  (hsε : εnv.StronglyWellFormedForAll xs)
  (hI  : I.WellFormed εnv.entities) :
  εnv.SameOn (footprints xs εnv) I (I.repair xs εnv)
:= by
  constructor
  · exact interpret_request_repair_eq hsε.left.left
  · intro ety δ hδ
    simp only [interpret_attrs_repair_eq xs I hsε.left.right.left hδ, true_and]
    constructor
    · intro ancTy ancF hf t hft uid ht hty
      subst hty
      rw [eq_comm]
      cases ancF <;> simp only [UnaryFunction.interpret]
      rename_i f
      apply mem_footprintUIDs_implies_eq_ancs (swf_εnv_implies_wf hsε.left) hI hδ hf
      exact mem_mem_footprints_footprintUIDs hft ht
    · intro τs hτs
      exact interpret_tags_repair_eq xs I hsε.left.right.left hδ hτs

end Cedar.Thm
