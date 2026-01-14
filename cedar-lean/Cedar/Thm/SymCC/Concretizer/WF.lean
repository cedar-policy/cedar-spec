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
import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Concretizer.Util
import Cedar.Thm.SymCC.Concretizer.Same
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Concretizer.WFValue

/-!
The main lemma in this file, `concretize?_some_wf`, proves that
`εnv.concretize? x` produces an environment that is well-formed for `x`.
-/

namespace Cedar.Thm
open Data Spec SymCC Factory

private theorem concretize?_entityData?_implies_fst {uid : EntityUID} {ed : EntityUID × EntityData} {εs : SymEntities} :
  SymEntities.concretize?.entityData? εs uid = some ed →
  ed.fst = uid
:= by
  intro hs
  replace ⟨_, _, _, _, hs⟩ := concretize?_entityData?_some_eq hs
  simp only [← hs]

private theorem concretize?_mapM_entityData?_wf_some_implies_sortedBy {eds : List (EntityUID × EntityData)} {uids : List EntityUID} {εs : SymEntities} :
  uids.Sorted →
  List.mapM (SymEntities.concretize?.entityData? εs) uids = some eds →
  eds.SortedBy Prod.fst
:= by
  intro hsrt hs
  induction hsrt generalizing eds
  case nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hs
    subst hs
    exact List.SortedBy.nil
  case cons_nil =>
    simp only [List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_some_fun,
      Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
    replace ⟨_, _, hs⟩ := hs
    subst hs
    exact List.SortedBy.cons_nil
  case cons_cons uid₁ uid₂ tl hlt htl ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at hs
    replace ⟨_, hs₁, _, ⟨_, hs₂, _, hs, heq⟩, heq'⟩ := hs
    subst heq heq'
    apply List.SortedBy.cons_cons
    · replace hs₁ := concretize?_entityData?_implies_fst hs₁
      replace hs₂ := concretize?_entityData?_implies_fst hs₂
      subst hs₁ hs₂
      simp only [id_eq] at hlt
      exact hlt
    · apply ih
      simp only [List.mapM_cons, hs₂, hs, Option.pure_def, Option.bind_some_fun]

private theorem concretize?_εs_some_implies_closed {uids : Set EntityUID} {εs : SymEntities} {es : Entities} :
  SymEntities.concretize? uids εs = some es →
  es.ClosedFor (uids ∪ εs.entityUIDs)
:= by
  intro hs uid hin
  replace ⟨eds, hs, heq⟩ := concretize?_εs_some_eq hs
  subst heq
  simp only [Map.contains_iff_some_find?]
  have hsrt : eds.SortedBy Prod.fst := by
    apply concretize?_mapM_entityData?_wf_some_implies_sortedBy _ hs
    simp [← Set.wf_iff_sorted]
    apply Set.union_wf
  simp only [Map.find?, Map.kvs, Map.make, List.sortedBy_implies_canonicalize_eq hsrt]
  have hin' : uid ∈ uids ∪ εs.entityUIDs := by
    simp only [hin]
  replace ⟨ed, hin', hs⟩ := List.mapM_some_implies_all_some hs uid hin'
  replace hs := concretize?_entityData?_implies_fst hs
  subst hs
  exists ed.snd
  have hf := List.mem_of_sortedBy_implies_find? hin' hsrt
  split
  · rename_i heq
    simp only [hf, Option.some.injEq] at heq
    simp only [heq]
  · rename_i hc
    specialize hc ed.fst
    simp only [imp_false] at hc
    replace hc : List.find? (λ x => x.fst == ed.fst) eds = .none := by
      rw [← List.not_find?_some_iff_find?_none]
      intro ed' hin''
      cases ed
      specialize hc ed'.snd
      cases ed'
      simp only [hf, Option.some.injEq, Prod.mk.injEq, true_and] at hc
      simp only [hf, hc, Option.some.injEq, Prod.mk.injEq, and_false, not_false_eq_true]
    simp only [hc, reduceCtorEq] at hf

private theorem subset_implies_closed {uids₁ uids₂ : Set EntityUID} {es : Entities} :
  uids₁ ⊆ uids₂ → es.ClosedFor uids₂ → es.ClosedFor uids₁
:= by
  intro hsub hcf uid hin
  exact hcf uid (Set.mem_subset_mem hin hsub)

private theorem concretize?_εs_some_implies_closed_uids {uids : Set EntityUID} {εs : SymEntities} {es : Entities} :
  SymEntities.concretize? uids εs = some es → es.ClosedFor uids
:= by
  intro hs
  replace hs := concretize?_εs_some_implies_closed hs
  exact subset_implies_closed (Set.subset_union uids _) hs

private theorem concretize?_εs_some_implies_closed_εs_entityUIDs {uids : Set EntityUID} {εs : SymEntities} {es : Entities} :
  SymEntities.concretize? uids εs = some es → es.ClosedFor εs.entityUIDs
:= by
  intro hs
  replace hs := concretize?_εs_some_implies_closed hs
  rw [Set.union_comm] at hs
  exact subset_implies_closed (Set.subset_union εs.entityUIDs _) hs

private theorem expr_entityUIDs_valid_refs {x : Expr} {uids : Set EntityUID} {es : Entities} :
  x.entityUIDs ⊆ uids →
  es.ClosedFor uids →
  x.ValidRefs (λ uid => Map.contains es uid = true)
:= by
  intro hsub hs
  induction x using Expr.entityUIDs.induct <;>
  simp only [Expr.entityUIDs] at hsub
  case case1 =>             -- lit
    apply Expr.ValidRefs.lit_valid
    simp only [Prim.ValidRef]
    split <;> try trivial
    simp only [Prim.entityUIDs, Set.subset_def, Set.mem_singleton_iff_eq, forall_eq] at hsub
    exact hs _ hsub
  case case2 =>             -- var
    exact Expr.ValidRefs.var_valid
  case case3 ih₁ ih₂ ih₃ => -- ite
    simp only [Set.union_subset] at hsub
    exact Expr.ValidRefs.ite_valid (ih₁ hsub.left.left) (ih₂ hsub.left.right) (ih₃ hsub.right)
  case case4 ih₁ ih₂ =>     -- and
    rw [Set.union_subset] at hsub
    exact Expr.ValidRefs.and_valid (ih₁ hsub.left) (ih₂ hsub.right)
  case case5 ih₁ ih₂ =>     -- or
    rw [Set.union_subset] at hsub
    exact Expr.ValidRefs.or_valid (ih₁ hsub.left) (ih₂ hsub.right)
  case case6 ih₁ ih₂ =>     -- binaryApp
    rw [Set.union_subset] at hsub
    exact Expr.ValidRefs.binaryApp_valid (ih₁ hsub.left) (ih₂ hsub.right)
  case case7 ih =>          -- unaryApp
    exact Expr.ValidRefs.unaryApp_valid (ih hsub)
  case case8 ih =>          -- getAttr
    exact Expr.ValidRefs.getAttr_valid (ih hsub)
  case case9 ih =>          -- hasAttr
    exact Expr.ValidRefs.hasAttr_valid (ih hsub)
  case case10 ih =>         -- set
    simp only [List.mapUnion₁_eq_mapUnion] at hsub
    apply Expr.ValidRefs.set_valid
    intro xᵢ hᵢ
    have hsubᵢ := List.mem_implies_subset_mapUnion Expr.entityUIDs hᵢ
    replace hsubᵢ := Set.subset_trans hsubᵢ hsub
    exact ih xᵢ hᵢ hsubᵢ
  case case11 ih =>         -- call
    simp only [List.mapUnion₁_eq_mapUnion] at hsub
    apply Expr.ValidRefs.call_valid
    intro xᵢ hᵢ
    have hsubᵢ := List.mem_implies_subset_mapUnion Expr.entityUIDs hᵢ
    replace hsubᵢ := Set.subset_trans hsubᵢ hsub
    exact ih xᵢ hᵢ hsubᵢ
  case case12 ih =>         -- record
    simp only [List.mapUnion₂_eq_mapUnion λ x : Attr × Expr => x.snd.entityUIDs] at hsub
    apply Expr.ValidRefs.record_valid
    intro (aᵢ, xᵢ) hᵢ
    have hsubᵢ := List.mem_implies_subset_mapUnion (λ x : Attr × Expr => x.snd.entityUIDs) hᵢ
    replace hsubᵢ := Set.subset_trans hsubᵢ hsub
    simp only at hsubᵢ
    apply ih aᵢ xᵢ _ hsubᵢ
    simp only
    replace hᵢ := List.sizeOf_lt_of_mem hᵢ
    simp only [Prod.mk.sizeOf_spec] at hᵢ
    omega

private theorem term_entityUID?_some_mem_entityUIDs {t : Term} {uid : EntityUID} :
  t.entityUID? = .some uid → uid ∈ t.entityUIDs
:= by
  intro h
  rw [term_entityUID?_some_iff_eq] at h
  simp only [h, Term.entityUIDs, TermPrim.entityUIDs, Set.mem_singleton]

private theorem concretize?_ρ_implies {ρ : SymRequest} {uids : Set EntityUID} {εs : SymEntities}:
 ρ.WellFormed εs →
 ρ.concretize? = some r →
 ρ.entityUIDs ⊆ uids →
 r.principal ∈ uids ∧ r.action ∈ uids ∧ r.resource ∈ uids ∧
 (Value.record r.context).entityUIDs ⊆ uids ∧
 (Value.record r.context).WellStructured
:= by
  intro hw hr huids
  replace ⟨uidₚ, uidₐ, uidᵣ, ctx, hp, ha, hr, hc, hs⟩ := concretize?_ρ_some_eq hr
  simp only [hs]
  simp only [SymRequest.entityUIDs, Set.union_subset] at huids
  replace ⟨⟨⟨huidsₚ, huidsₐ⟩, huidsᵣ⟩, huids⟩ := huids
  replace hc := term_recordValue?_some_same hc
  simp only [same_values_def] at hc
  rw [term_value?_some_implies_eq_entityUIDs hc] at huids
  replace hw := hw.right.right.right.right.right.right.left
  simp only [
    Set.mem_subset_mem (term_entityUID?_some_mem_entityUIDs hp) huidsₚ,
    Set.mem_subset_mem (term_entityUID?_some_mem_entityUIDs ha) huidsₐ,
    Set.mem_subset_mem (term_entityUID?_some_mem_entityUIDs hr) huidsᵣ,
    term_value?_some_implies_ws hw hc, huids,
    and_true]

private theorem concretize?_ρ_wf {ρ : SymRequest} {r : Request} {uids : Set EntityUID} {εs : SymEntities} {es : Entities} :
  ρ.WellFormed εs →
  ρ.concretize? = some r →
  ρ.entityUIDs ⊆ uids →
  εs.concretize? uids = es →
  r.WellFormed es
:= by
  intro hw hq huids hs
  simp only [Request.WellFormed]
  have ⟨hp, ha, hr, hc, hws⟩ := concretize?_ρ_implies hw hq huids
  replace huids := concretize?_εs_some_implies_closed_uids hs
  simp only [huids r.principal hp, huids r.action ha, huids r.resource hr, true_and]
  apply value_ws_closed_implies_wf hws
  intro uid huid
  exact huids uid (Set.mem_subset_mem huid hc)

private theorem concretize?_εs_some_implies_δ {uids : Set EntityUID} {εs : SymEntities} {uid : EntityUID} {d : EntityData} {es : Entities} :
  SymEntities.concretize? uids εs = some es →
  es.find? uid = some d →
  ∃ δ, εs.find? uid.ty = some δ ∧ δ.concretize? uid = some d
:= by
  intro hs hf
  replace ⟨eds, hs, heq⟩ := concretize?_εs_some_eq hs
  subst heq
  replace hf := Map.find?_mem_toList hf
  simp only [Map.toList, Map.kvs, Map.make] at hf
  replace hf := List.in_canonicalize_in_list hf
  replace ⟨uid', _, hs⟩ := List.mapM_some_implies_all_from_some hs (uid, d) hf
  replace ⟨δ, d', hf', hs, heq⟩ := concretize?_entityData?_some_eq hs
  simp only [Prod.mk.injEq] at heq
  simp only [heq, and_self] at *
  exists δ

private theorem app_value?_some_implies_entityUIDs {f : UnaryFunction} {t : Term} {v : Value} :
  (app f t).value? = some v →
  t.isLiteral →
  v.entityUIDs ⊆ f.entityUIDs
:= by
  intro hv hlit
  simp only [app] at hv
  split at hv <;> try simp only [Term.value?, reduceCtorEq] at hv
  rename_i f
  simp only [hlit, ↓reduceIte] at hv
  simp only [UnaryFunction.entityUIDs, UDF.entityUIDs]
  split at hv <;>
  replace hv := term_value?_some_implies_eq_entityUIDs hv
  · simp only [← hv]
    rename_i t' heq
    rw [Set.union_comm]
    apply Set.subset_trans (s₂ := f.table.kvs.mapUnion (λ x => x.fst.entityUIDs ∪ x.snd.entityUIDs)) _ (Set.subset_union _ _)
    simp only [Set.subset_def]
    intro uid hin
    rw [List.mem_mapUnion_iff_mem_exists]
    exists (t, t')
    constructor
    · exact Map.find?_mem_toList heq
    · simp only [Set.mem_union_iff_mem_or, hin, or_true]
  · simp only [hv, Set.subset_union]

private theorem concretize?_δ_attrs_some_implies_ws_entityUIDs {uid : EntityUID} {attrs : Map Attr Value} {δ : SymEntityData} {εs : SymEntities}
  (hwδ : δ.WellFormed εs uid.ty)
  (hwu : Term.WellFormedLiteral εs (Term.entity uid))
  (hs : (app δ.attrs (Term.entity uid)).recordValue? = some attrs) :
  (Value.record attrs).WellStructured ∧
  (Value.record attrs).entityUIDs ⊆ SymEntityData.entityUIDs.attrs δ
:= by
  replace hs := same_values_def.mp (term_recordValue?_some_same hs)
  have hwa := wf_δ_implies_wf_app_attrs hwδ hwu.left
  have hws := term_value?_some_implies_ws hwa.left hs
  simp only [hws, SymEntityData.entityUIDs.attrs, true_and]
  exact app_value?_some_implies_entityUIDs hs hwu.right

private theorem term_setOfEntityUIDs?_some_value? {t : Term} {uids : Set EntityUID} :
  t.setOfEntityUIDs? = some uids →
  t.value? = Value.set (Set.make (uids.elts.map λ uid => .prim (.entityUID uid)))
:= by
  intro hs
  simp only [Term.setOfEntityUIDs?, Option.bind_eq_bind] at hs
  split at hs <;> simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at hs
  simp only [Term.value?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Value.set.injEq]
  replace ⟨uids', hs, heq⟩ := hs
  exists (List.map (fun uid => Value.prim (Prim.entityUID uid)) uids') -- uids.elts)
  simp only [List.mapM₁_eq_mapM]
  constructor
  · rw [List.mapM_some_iff_forall₂]
    rw [List.mapM_some_iff_forall₂] at hs
    clear heq
    induction hs
    case nil => simp only [List.map_nil, List.Forall₂.nil]
    case cons thd uhd ttl utl h₁ h₂ ih =>
      apply List.Forall₂.cons _ ih
      rw [term_entityUID?_some_iff_eq] at h₁
      simp only [h₁, entity_value?]
  · rw [← Set.eq_means_eqv (Set.make_wf _) (Set.make_wf _)]
    apply List.Equiv.trans Set.elts_make_equiv
    apply List.Equiv.symm
    apply List.Equiv.trans Set.elts_make_equiv
    simp only [List.Equiv, List.subset_def, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Value.prim.injEq, Prim.entityUID.injEq, exists_eq_right]
    subst heq
    constructor <;> intro uid hin
    · rw [Set.in_list_iff_in_set, ← Set.make_mem] at hin
      exact hin
    · rw [Set.in_list_iff_in_set, ← Set.make_mem]
      exact hin

private theorem concretize?_δ_ancs_some_implies_entityUIDs {uid : EntityUID} {δ : SymEntityData} {ancs : List (Set EntityUID)} {εs : SymEntities}
  (hwu : Term.WellFormedLiteral εs (Term.entity uid))
  (hs : List.mapM (λ x => (app x.snd (Term.entity uid)).setOfEntityUIDs?) δ.ancestors.kvs = some ancs) :
  (List.mapUnion id ancs).WellFormed ∧
  List.mapUnion id ancs ⊆ SymEntityData.entityUIDs.ancs δ
:= by
  simp only [List.mapUnion_wf, SymEntityData.entityUIDs.ancs, true_and]
  simp only [← List.mapM_some_eq_filterMap hs, List.mapUnion_filterMap, Set.subset_def]
  intro uid' hin
  rw [List.mem_mapUnion_iff_mem_exists] at hin
  replace ⟨(ety, uf), hin, hinᵤ⟩ := hin
  replace ⟨anc, _, hs⟩ := List.mapM_some_implies_all_some hs _ hin
  simp only at hs
  simp only [hs, Option.mapD_some, id_eq] at hinᵤ
  rw [List.mem_mapUnion_iff_mem_exists]
  exists (ety, uf)
  simp only [hin, true_and]
  replace hs := term_setOfEntityUIDs?_some_value? hs
  apply Set.mem_subset_mem _ (app_value?_some_implies_entityUIDs hs hwu.right)
  unfold Value.entityUIDs
  simp only [List.mapUnion₁_eq_mapUnion]
  rw [List.mapUnion_eq_mapUnion_id_map, List.mem_mapUnion_iff_mem_exists]
  exists (Set.singleton uid')
  simp only [List.mem_map, id_eq, Set.mem_singleton, and_true]
  exists uid'
  simp only [Set.in_list_iff_in_set, ← Set.make_mem, Value.entityUIDs, Prim.entityUIDs, hinᵤ,
    List.mem_map, Value.prim.injEq, Prim.entityUID.injEq, exists_eq_right, and_self]

private theorem term_setOfTags?_some_wf {t : Term} {tags : Set String} :
  t.setOfTags? = some tags → tags.WellFormed
:= by
  intro hs
  simp only [Term.setOfTags?, Option.bind_eq_bind] at hs
  split at hs <;> simp only [Option.bind, reduceCtorEq] at hs
  split at hs <;> simp only [Option.some.injEq, reduceCtorEq] at hs
  subst hs
  exact Set.make_wf _

private theorem mapM_concretize?_taggedValueFor_some_sorted {uid : EntityUID} {τs : SymTags} {tags : List Tag} {tvs : List (Tag × Value)}
  (heq : List.mapM (SymEntityData.concretize?.taggedValueFor τs (Term.entity uid)) tags = some tvs)
  (hsrt : tags.Sorted) :
  List.SortedBy Prod.fst tvs
:= by
  induction tags generalizing tvs
  case nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at heq
    subst heq
    exact List.SortedBy.nil
  case cons hd tl ih =>
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind] at heq
    split at heq <;> simp only [reduceCtorEq] at heq
    rename_i hd' hheq
    split at heq <;> simp only [reduceCtorEq] at heq
    rename_i tl' hteq
    simp only [Option.some.injEq] at heq
    subst heq
    cases tl'
    case nil =>
      exact List.SortedBy.cons_nil
    case cons hd'' tl'' =>
      apply List.SortedBy.cons_cons _ (ih hteq (List.tail_sortedBy hsrt) )
      replace hheq := (concretize?_taggedValueFor_some_implies hheq).left
      subst hheq
      replace hteq := List.mapM_some_implies_all_from_some hteq hd''
      simp only [List.mem_cons, true_or, true_implies] at hteq
      replace ⟨t, hin, hteq⟩ := hteq
      replace hteq := (concretize?_taggedValueFor_some_implies hteq).left
      subst hteq
      cases hd' ; cases hd''
      simp only [gt_iff_lt] at *
      replace hsrt := List.sortedBy_implies_head_lt_tail hsrt _ hin
      simp only [id_eq] at hsrt
      exact hsrt

private theorem concretize?_δ_tags_some_implies_ws_entityUIDs {uid : EntityUID} {tags : Map Tag Value} {δ : SymEntityData} {εs : SymEntities}
  (hwδ : δ.WellFormed εs uid.ty)
  (hwu : Term.WellFormedLiteral εs (Term.entity uid))
  (hs : SymEntityData.concretize?.tags δ (Term.entity uid) = some tags) :
  (Value.record tags).WellStructured ∧
  (Value.record tags).entityUIDs ⊆ SymEntityData.entityUIDs.tags δ
:= by
  simp only [SymEntityData.concretize?.tags, Option.bind_eq_bind] at hs
  cases hτs : δ.tags <;> simp only [hτs, Option.some.injEq] at hs
  case none =>
    subst hs
    simp only [Map.empty, value_record_entityUIDs_def, Map.kvs, List.mapUnion_nil,
      EmptyCollection.emptyCollection, Set.subset_def, Set.empty_no_elts, false_implies,
      implies_true, and_true]
    apply Value.WellStructured.record_ws
    · intro a v hf
      replace hf := Map.find?_mem_toList hf
      simp only [Map.toList, Map.kvs, List.not_mem_nil] at hf
    · simp only [Map.WellFormed, Map.make, Map.toList, Map.kvs, List.canonicalize_nil]
  case some τs =>
    simp only [Option.bind] at hs
    split at hs <;> simp only [reduceCtorEq] at hs
    rename_i tags' hks
    split at hs <;> simp only [reduceCtorEq] at hs
    rename_i tvs htvs
    simp only [Option.some.injEq] at hs
    subst hs
    constructor
    · apply Value.WellStructured.record_ws
      · intro t v hf
        replace hf := Map.find?_mem_toList hf
        simp only [Map.toList, Map.kvs] at hf
        replace ⟨t', htvs, heq⟩ := List.mapM_some_implies_all_from_some htvs (t, v) hf
        replace ⟨heq', heq⟩ := concretize?_taggedValueFor_some_implies heq
        rw [eq_comm] at heq' ; subst heq'
        replace hwδ := hwδ.right.right.right.right.right.left τs hτs
        have hwg := @wf_tags_getTag! εs τs (.entity uid) (.string t) uid.ty hwδ hwu.left
          wf_string typeOf_term_prim_entity typeOf_term_prim_string
        exact term_value?_some_implies_ws hwg.left heq
      · simp only [Map.wf_iff_sorted, Map.toList, Map.kvs]
        have hws := term_setOfTags?_some_wf hks
        rw [Set.wf_iff_sorted] at hws
        exact mapM_concretize?_taggedValueFor_some_sorted htvs hws
    · simp only [value_record_entityUIDs_def, Map.kvs, SymEntityData.entityUIDs.tags, hτs,
        Set.subset_def]
      intro uid' hin
      rw [List.mem_mapUnion_iff_mem_exists] at hin
      replace ⟨(t, v), hin, hin'⟩ := hin
      simp only at hin'
      replace ⟨t', htvs, heq⟩ := List.mapM_some_implies_all_from_some htvs (t, v) hin
      replace ⟨heq', heq⟩ := concretize?_taggedValueFor_some_implies heq
      rw [eq_comm] at heq' ; subst heq'
      simp only [SymTags.getTag!] at heq
      have hsub := app_value?_some_implies_entityUIDs heq (lit_tagOf uid t)
      exact Set.mem_subset_mem hin' hsub

private theorem concretize?_δ_some_implies {uid : EntityUID} {δ : SymEntityData} {d : EntityData} {εs : SymEntities} :
  εs.find? uid.ty = some δ →
  δ.WellFormed εs uid.ty →
  δ.concretize? uid = some d →
  d.entityUIDs ⊆ δ.entityUIDs uid.ty ∧
  d.ancestors.WellFormed ∧
  (Value.record d.attrs).WellStructured ∧
  (Value.record d.tags).WellStructured
:= by
  intro hf hw hs
  simp only [SymEntityData.concretize?, Option.bind_eq_bind, Option.bind_some_fun,
    Option.bind_none_fun] at hs
  split at hs <;> simp only [Option.bind_eq_some_iff, Option.some.injEq, reduceCtorEq] at hs
  rename_i hwu
  replace hwu := concretize?_δ_isValidEntityUID_implies_wfl hf hwu
  replace ⟨attrs, hattrs, ancs, hs, tags, htags, heq⟩ := hs
  subst heq
  replace hattrs := concretize?_δ_attrs_some_implies_ws_entityUIDs hw hwu hattrs
  replace hancs := concretize?_δ_ancs_some_implies_entityUIDs hwu hs
  replace htags := concretize?_δ_tags_some_implies_ws_entityUIDs hw hwu htags
  simp only [EntityData.entityUIDs, SymEntityData.entityUIDs, hancs.left, hattrs.left, htags.left, Set.union_subset,
    and_self, and_true]
  constructor
  · constructor
    · apply Set.subset_trans hancs.right
      rw [Set.union_assoc, Set.union_comm, Set.union_assoc]
      exact Set.subset_union _ _
    · apply Set.subset_trans hattrs.right
      rw [Set.union_assoc, Set.union_assoc, Set.union_comm, Set.union_assoc]
      exact Set.subset_union _ _
  · apply Set.subset_trans htags.right
    rw [Set.union_comm]
    exact Set.subset_union _ _

private theorem δ_entityUIDs_subset_εs_entityUIDs {ety : EntityType} {δ : SymEntityData} {εs : SymEntities} :
  εs.find? ety = some δ →
  δ.entityUIDs ety ⊆ εs.entityUIDs
:= by
  intro hf
  simp only [SymEntities.entityUIDs]
  have h : SymEntityData.entityUIDs ety δ = (λ x => SymEntityData.entityUIDs x.fst x.snd) (ety, δ) := by simp only
  rw [h]
  apply List.mem_implies_subset_mapUnion (λ x : EntityType × SymEntityData => SymEntityData.entityUIDs x.fst x.snd)
  exact Map.find?_mem_toList hf

private theorem concretize?_εs_wf {uids : Set EntityUID} {es : Entities} {εs : SymEntities} :
  εs.WellFormed →
  εs.concretize? uids = es →
  es.WellFormed
:= by
  intro hw hs
  simp only [Entities.WellFormed]
  constructor
  simp only [SymEntities.concretize?, bind, Option.bind] at hs
  split at hs
  contradiction
  simp only [Option.some.injEq] at hs
  simp only [←hs]
  exact Map.make_wf _
  intro uid d hf
  have ⟨δ, hf', hs'⟩ := concretize?_εs_some_implies_δ hs hf
  simp only [EntityData.WellFormed]
  replace hw := hw.right uid.ty δ hf'
  have ⟨huids, hwa, hws, hwt⟩ := concretize?_δ_some_implies hf' hw hs'
  simp only [hwa, true_and]
  replace huids := Set.subset_trans huids (δ_entityUIDs_subset_εs_entityUIDs hf')
  have hcf := concretize?_εs_some_implies_closed_εs_entityUIDs hs
  simp only [EntityData.entityUIDs] at huids
  simp only [Set.union_subset] at huids
  constructor
  · exact value_ws_closed_implies_wf hws (subset_implies_closed huids.left.right hcf)
  · constructor
    · intro anc hin
      exact subset_implies_closed huids.left.left hcf anc hin
    · replace hwt := value_ws_closed_implies_wf hwt (subset_implies_closed huids.right hcf)
      cases hwt
      rename_i hwt₁ hwt₂
      simp only [hwt₂, true_and]
      intro t v hf
      exact hwt₁ t v hf

theorem concretize?_some_wf {x : Expr} {env : Env} {εnv : SymEnv} :
  εnv.WellFormedFor x →
  εnv.concretize? x = .some env →
  env.WellFormedFor x
:= by
  intro hwε hs
  simp only [SymEnv.concretize?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hs
  replace ⟨r, hr, es, hs, heq⟩ := hs
  subst heq
  constructor
  · simp only [Env.WellFormed]
    constructor
    · apply concretize?_ρ_wf hwε.left.left hr _ hs
      rw [Set.union_comm]
      exact Set.subset_union εnv.request.entityUIDs x.entityUIDs
    · exact concretize?_εs_wf hwε.left.right hs
  · simp only
    apply expr_entityUIDs_valid_refs
    · exact Set.subset_union x.entityUIDs εnv.request.entityUIDs
    · intro uid hin
      exact concretize?_εs_some_implies_closed_uids hs uid hin


end Cedar.Thm
