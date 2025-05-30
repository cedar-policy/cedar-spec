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
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.SymCC.Term.Same

/-!
The main lemma in this file, `concretize?_some_same`, proves that succesful
concretization results in a concrete environment that corresponds to the given
literal symbolic environment.
-/

namespace Cedar.Thm

open Data Spec SymCC Factory

theorem term_entityUID?_some_iff_eq {t : Term} {uid : EntityUID} :
  t.entityUID? = some uid ↔ t = Term.prim (TermPrim.entity uid)
:= by
  constructor
  case mp =>
    intro h
    simp only [Term.entityUID?] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl
  case mpr =>
    intro h
    subst h
    simp only [Term.entityUID?]

theorem term_recordValue?_some_same {t : Term} {r : Map Attr Value} :
  t.recordValue? = some r → (Value.record r) ∼ t
:= by
  intro h
  simp only [Term.recordValue?, Option.bind_eq_bind, Option.bind_eq_some] at h
  replace ⟨v, h, hv⟩ := h
  simp only [Value.record?] at hv
  split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
  subst hv
  rw [← same_values_def] at h
  exact h

private theorem term_setOfEntityUIDs?_some_exists {t : Term} {uids : Set EntityUID} {ety : EntityType} {εs : SymEntities} :
  t.WellFormed εs →
  t.typeOf = .set (.entity ety) →
  t.setOfEntityUIDs? = some uids →
  ∃ ts,
    t = Term.set ts (.entity ety) ∧
    ts.elts ≡ uids.elts.map Term.entity ∧
    ∀ uid ∈ uids, uid.ty = ety
:= by
  intro hwt hty hs
  simp only [Term.setOfEntityUIDs?, Option.bind_eq_bind] at hs
  split at hs <;> simp only [Option.bind_eq_some, Option.some.injEq, reduceCtorEq] at hs
  rename_i ts _
  replace ⟨uids, huids, hs⟩ := hs
  exists (Set.mk ts)
  simp only [Term.typeOf, TermType.set.injEq] at hty
  subst hty hs
  simp only [true_and]
  constructor
  case left =>
    have heq := @Set.elts_make_equiv _ _ _ _ uids
    replace heq := List.map_equiv Term.entity _ _ heq
    apply List.Equiv.trans _ (List.Equiv.symm heq)
    simp only [List.Equiv, List.subset_def, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    constructor
    case left =>
      intro t hin
      simp only [Set.elts] at hin
      replace ⟨uid, huids⟩ := List.mapM_some_implies_all_some huids t hin
      rw [term_entityUID?_some_iff_eq, eq_comm] at huids
      exists uid
    case right =>
      intro uid hin
      simp only [Set.elts]
      replace ⟨t, huids, ht⟩ := List.mapM_some_implies_all_from_some huids uid hin
      rw [term_entityUID?_some_iff_eq, eq_comm] at ht
      subst ht
      exact huids
  case right =>
    intro uid hin
    rw [← Set.make_mem] at hin
    replace ⟨t, huids, ht⟩ := List.mapM_some_implies_all_from_some huids uid hin
    rw [term_entityUID?_some_iff_eq] at ht
    subst ht
    replace hwt := wf_term_set_implies_typeOf_elt hwt ((Set.in_list_iff_in_mk _ _).mp huids)
    simp only [Term.typeOf, TermPrim.typeOf, TermType.prim.injEq, TermPrimType.entity.injEq] at hwt
    exact hwt

theorem term_tag?_some_iff_eq {t : Term} {s : String} :
  t.tag? = some s ↔ t = Term.string s
:= by
  simp only [Term.tag?]
  split <;> simp only [Option.some.injEq, Term.prim.injEq, TermPrim.string.injEq, false_iff, reduceCtorEq]
  by_contra hc
  subst hc
  rename_i hn
  apply hn s
  simp only

private theorem term_setOfTags?_some_lit {t : Term} {tags : Set String} :
  t.setOfTags? = some tags →
  t.isLiteral
:= by
  intro hs
  simp only [Term.setOfTags?, Option.bind_eq_bind] at hs
  split at hs <;> try simp only at hs
  rename_i ts ty
  apply lit_term_set_impliedBy_lit_elts
  intro t hin
  rw [← Set.in_list_iff_in_mk] at hin
  simp only [Option.bind] at hs
  split at hs
  all_goals (simp only [Option.some.injEq, reduceCtorEq] at hs)
  rename_i _ heq
  subst hs
  replace ⟨_, _, heq⟩ := List.mapM_some_implies_all_some heq t hin
  rw [term_tag?_some_iff_eq] at heq
  subst heq
  exact term_prim_is_lit

private theorem term_setOfTags?_some_exists {t : Term} {tags : Set String} :
  t.typeOf = .set .string →
  t.setOfTags? = some tags →
  ∃ ts,
    t = Term.set ts .string ∧
    ts.elts ≡ tags.elts.map Term.string
:= by
  intro hty hs
  simp only [Term.setOfTags?, Option.bind_eq_bind] at hs
  split at hs <;> try simp only at hs
  rename_i ts ty
  simp only [Option.bind] at hs
  split at hs
  all_goals (simp only [Option.some.injEq, reduceCtorEq] at hs)
  rename_i ts' heq
  subst hs
  exists (Set.mk ts)
  simp only [Term.typeOf, TermType.set.injEq] at hty
  subst hty
  simp only [true_and]
  constructor <;> simp only [List.subset_def, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂]
  · intro t hin
    rw [Set.in_list_iff_in_set, ← Set.in_list_iff_in_mk] at hin
    replace ⟨s, hin', heq⟩ := List.mapM_some_implies_all_some heq t hin
    rw [term_tag?_some_iff_eq] at heq
    subst heq
    exists s
    simp only [Set.in_list_iff_in_set, ← Set.make_mem, hin', and_self]
  · intro s hin
    rw [Set.in_list_iff_in_set, ← Set.in_list_iff_in_mk]
    rw [Set.in_list_iff_in_set, ← Set.make_mem] at hin
    replace ⟨t, hin', heq⟩ := List.mapM_some_implies_all_from_some heq s hin
    rw [term_tag?_some_iff_eq] at heq
    subst heq
    exact hin'

private theorem concretize?_some_same_requests {r : Request} {ρ : SymRequest} :
  ρ.concretize? = .some r → SameRequests r ρ
:= by
  intro hs
  simp only [SameRequests]
  replace ⟨_, _, _, _, hp, ha, hr, hc, hs⟩ := concretize?_ρ_some_eq hs
  subst hs
  simp only [
    term_entityUID?_some_iff_eq.mp hp,
    term_entityUID?_some_iff_eq.mp ha,
    term_entityUID?_some_iff_eq.mp hr,
    same_implies_same_value (term_recordValue?_some_same hc),
    and_self]

private theorem concretize?_some_InSymAncestors {uid anc : EntityUID} {δ : SymEntityData} {εs : SymEntities} {ancs : List (Set EntityUID)}
  (hwδ : SymEntityData.WellFormed εs uid.ty δ)
  (hwt : Term.WellFormedLiteral εs (Term.entity uid))
  (ha : List.mapM (λ tyf => (app tyf.snd (Term.entity uid)).setOfEntityUIDs?) δ.ancestors.kvs = some ancs)
  (hin : anc ∈ List.mapUnion id ancs) :
  SameEntityData.InSymAncestors uid δ anc
:= by
  simp only [SameEntityData.InSymAncestors]
  simp only [Set.mem_mapUnion_iff_mem_exists, id_eq] at hin
  replace ⟨s, hin⟩ := hin
  replace ha := List.mapM_some_implies_all_from_some ha
  specialize ha s hin.left
  replace ⟨(ancTy, ancUF), hin', ha⟩ := ha
  simp only at ha
  exists ancUF
  replace hin' := Map.mem_toList_find? hwδ.right.right.right.right.left hin'
  replace hwt := wf_δ_implies_wf_app_ancs hwδ hwt.left hin'
  replace ⟨ts, ha, heq, hty⟩ := term_setOfEntityUIDs?_some_exists hwt.left hwt.right ha
  specialize hty anc hin.right
  subst hty
  simp only [hin', true_and]
  exists ts
  simp only [ha, true_and]
  replace heq := heq.right
  simp only [List.subset_def, Set.in_list_iff_in_set, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at heq
  exact heq anc hin.right

private theorem concretize?_some_InAncestors {uid : EntityUID} {δ : SymEntityData} {εs : SymEntities}
  {ancs : List (Set EntityUID)} {attrs : Map Attr Value} {tags : Map String Value}
  {ancTy : EntityType} {ancUF : UnaryFunction}
  (hf : δ.ancestors.find? ancTy = some ancUF)
  (hwδ : SymEntityData.WellFormed εs uid.ty δ)
  (hwt : Term.WellFormedLiteral εs (Term.entity uid))
  (ha : List.mapM (λ tyf => (app tyf.snd (Term.entity uid)).setOfEntityUIDs?) δ.ancestors.kvs = some ancs) :
  SameEntityData.InAncestors uid { attrs := attrs, ancestors := List.mapUnion id ancs, tags := tags } ancUF ancTy
:= by
  simp only [SameEntityData.InAncestors]
  replace hwt := wf_δ_implies_wf_app_ancs hwδ hwt.left hf
  replace hf := Map.find?_mem_toList hf
  simp only [Map.toList] at hf
  replace ⟨s, hs, ha⟩ := List.mapM_some_implies_all_some ha (ancTy, ancUF) hf
  simp only at ha
  replace ⟨ts, ha, heq, _⟩ := term_setOfEntityUIDs?_some_exists hwt.left hwt.right ha
  exists ts
  simp only [ha, true_and]
  intro t ht
  replace heq := heq.left
  simp only [List.subset_def, List.mem_map, Set.in_list_iff_in_set] at heq
  replace ⟨anc, hin, heq⟩ := heq ht
  subst heq
  exists anc
  replace hin : anc ∈ id s := by simp only [id_eq, hin]
  simp only [Set.mem_mem_implies_mem_mapUnion hin hs, and_self]

theorem concretize?_taggedValueFor_some_implies {tuid : Term} {tag tag' : Tag} {v : Value} {τs : SymTags} :
  SymEntityData.concretize?.taggedValueFor τs tuid tag = some (tag', v) →
  tag = tag' ∧ (τs.getTag! tuid (.string tag)).value? = some v
:= by
  intro h
  simp only [SymEntityData.concretize?.taggedValueFor, Option.bind_eq_bind, Option.bind] at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  rename_i _ heq
  simp only [h, and_self, true_and] at *
  exact heq

private theorem mapM_concretize?_taggedValueFor_none_implies_contains_tag_false
  {uid : EntityUID} {τs : SymTags} {τags : Set Term} {ts : Set Tag} {tvs : List (Tag × Value)}
  {tag : Tag}
  (heq : List.mapM (SymEntityData.concretize?.taggedValueFor τs (Term.entity uid)) ts.elts = some tvs)
  (heqv : τags.elts ≡ List.map Term.string ts.elts)
  (hn : (Map.mk tvs).find? tag = none) :
  τags.contains (Term.prim (TermPrim.string tag)) = false
:= by
  by_contra hc
  simp only [ne_eq, Bool.not_eq_false] at hc
  rw [Set.contains_prop_bool_equiv, ← Set.in_list_iff_in_set] at hc
  replace hkeqv := heqv.left
  simp only [List.subset_def, List.mem_map] at hkeqv
  replace ⟨tag, hkeqv⟩ := hkeqv hc
  simp only [Term.prim.injEq, TermPrim.string.injEq] at hkeqv
  replace ⟨hin, hkeqv⟩ := hkeqv
  subst hkeqv
  replace ⟨(tag', val), hin', heq⟩ := List.mapM_some_implies_all_some heq tag hin
  replace heq := (concretize?_taggedValueFor_some_implies heq).left
  subst heq
  replace hn := Map.find?_none_all_absent hn val
  simp only [Map.kvs] at hn
  contradiction

private theorem mapM_concretize?_taggedValueFor_some_implies_contains_tag_true
  {uid : EntityUID} {τs : SymTags} {τags : Set Term} {ts : Set Tag} {tvs : List (Tag × Value)}
  {tag : Tag} {val : Value}
  (heq : List.mapM (SymEntityData.concretize?.taggedValueFor τs (Term.entity uid)) ts.elts = some tvs)
  (heqv : τags.elts ≡ List.map Term.string ts.elts)
  (hs : (Map.mk tvs).find? tag = some val) :
  τags.contains (Term.prim (TermPrim.string tag)) = true
:= by
  simp only [Set.contains_prop_bool_equiv]
  replace hs := Map.find?_mem_toList hs
  simp only [Map.toList, Map.kvs] at hs
  replace ⟨tag', hin', heq⟩ := List.mapM_some_implies_all_from_some heq (tag, val) hs
  replace heq := (concretize?_taggedValueFor_some_implies heq).left
  subst heq
  replace hkeqv := heqv.right
  simp only [List.subset_def, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hkeqv
  specialize hkeqv tag' hin'
  simp only [← Set.in_list_iff_in_set, hkeqv]

private theorem concretize?_some_same_tags {uid : EntityUID} {δ : SymEntityData} {εs : SymEntities}
  {ancs : List (Set EntityUID)} {attrs : Map Attr Value} {tags : Map String Value}
  (hwδ : SymEntityData.WellFormed εs uid.ty δ)
  (hwt : Term.WellFormedLiteral εs (Term.entity uid))
  (ht : SymEntityData.concretize?.tags δ (Term.entity uid) = some tags) :
  SameTags uid { attrs := attrs, ancestors := List.mapUnion id ancs, tags := tags } δ
:= by
  simp only [SameTags]
  cases hδ : δ.tags <;> simp only <;>
  simp only [SymEntityData.concretize?.tags, hδ, Option.some.injEq, Option.bind_eq_bind] at ht
  case none =>
    simp only [ht]
  case some τs =>
    cases hkeys : (app τs.keys (Term.entity uid)).setOfTags? <;>
    simp only [hkeys, Option.none_bind, Option.some_bind, reduceCtorEq] at ht
    rename_i ts
    simp only [Option.bind] at ht
    split at ht <;> simp only [Option.some.injEq, reduceCtorEq] at ht
    rename_i tvs heq
    subst ht
    have hkw := wf_δ_implies_wf_app_tags_keys hwδ hwt.left hδ
    have ⟨τags, hkeq, hkeqv⟩ := term_setOfTags?_some_exists hkw.right hkeys
    have hklit := term_setOfTags?_some_lit hkeys
    rw [hkeq] at hklit
    simp only [SymTags.hasTag, hkeq, pe_set_member hklit term_prim_is_lit, Term.prim.injEq,
      TermPrim.bool.injEq]
    constructor
    · intro tag
      constructor <;> intro hn
      · exact mapM_concretize?_taggedValueFor_none_implies_contains_tag_false heq hkeqv hn
      · by_contra hc
        cases hf : (Map.mk tvs).find? tag <;> try contradiction
        have hn' := mapM_concretize?_taggedValueFor_some_implies_contains_tag_true heq hkeqv hf
        simp only [hn, Term.prim.injEq, TermPrim.bool.injEq, Bool.false_eq_true] at hn'
    · intro tag val hs
      constructor
      · exact mapM_concretize?_taggedValueFor_some_implies_contains_tag_true heq hkeqv hs
      · replace hs := Map.find?_mem_toList hs
        simp [Map.toList, Map.kvs] at hs
        replace ⟨tag', _, heq⟩ := List.mapM_some_implies_all_from_some heq (tag, val) hs
        replace ⟨heq', heq⟩ := concretize?_taggedValueFor_some_implies heq
        subst heq'
        simp only [SameValues, heq]

private theorem concretize?_some_same_entity_data {uid : EntityUID} {d : EntityData} {δ : SymEntityData} {εs : SymEntities} :
  Map.find? εs uid.ty = some δ →
  δ.WellFormed εs uid.ty →
  δ.concretize? uid = some d →
  SameEntityData uid d δ
:= by
  intro hf hwδ hs
  simp only [SameEntityData]
  simp only [SymEntityData.concretize?, Option.bind_eq_bind, Option.bind_some_fun,
    Option.bind_none_fun] at hs
  split at hs <;> simp only [Option.bind_eq_some, Option.some.injEq, reduceCtorEq] at hs
  rename_i hvd
  replace ⟨attrs, hr, ancs, ha, tags, ht, hs⟩ := hs
  subst hs
  simp only [same_implies_same_value (term_recordValue?_some_same hr), true_and]
  have hwt := concretize?_δ_isValidEntityUID_implies_wfl hf hvd
  constructor
  · intro _ hin
    exact concretize?_some_InSymAncestors hwδ hwt ha hin
  · constructor
    · intro ancTy ancUF hf'
      exact concretize?_some_InAncestors hf' hwδ hwt ha
    · exact concretize?_some_same_tags hwδ hwt ht

private theorem concretize?_some_same_entities {uids : Set EntityUID} {es : Entities} {εs : SymEntities} :
  εs.WellFormed →
  εs.concretize? uids = .some es →
  SameEntities es εs
:= by
  intro hwε hs
  simp only [SameEntities]
  intro uid d hf
  simp only [SymEntities.concretize?, Option.bind_eq_bind, Option.bind_eq_some,
    Option.some.injEq] at hs
  replace ⟨es', hs, heq⟩ := hs
  subst heq
  replace hf := Map.find?_mem_toList hf
  simp only [Map.toList, Map.kvs, Map.make] at hf
  replace hf := List.in_canonicalize_in_list hf
  replace ⟨_, _, hs⟩ := List.mapM_some_implies_all_from_some hs (uid, d) hf
  simp only [SymEntities.concretize?.entityData?, Option.bind_eq_bind, Option.bind_eq_some,
    Option.some.injEq, Prod.mk.injEq, exists_eq_right_right] at hs
  replace ⟨δ, hf', hs, heq⟩ := hs
  rw [eq_comm] at heq ; subst heq
  exists δ
  simp only [hf', concretize?_some_same_entity_data hf' (hwε.right uid.ty δ hf') hs, and_self]

theorem concretize?_some_same {x : Expr} {env : Env} {εnv : SymEnv} :
  εnv.WellFormedFor x →
  εnv.concretize? x = .some env →
  env ∼ εnv
:= by
  intro hwε hs
  simp only [Same.same, SameEnvs]
  simp only [SymEnv.concretize?, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at hs
  replace ⟨r, hr, es, hs, henv⟩ := hs
  subst henv
  simp only [
    concretize?_some_same_requests hr,
    concretize?_some_same_entities hwε.left.right hs,
    true_and]

end Cedar.Thm
