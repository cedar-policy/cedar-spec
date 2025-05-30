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
import Cedar.Thm.SymCC.Term.Lit
import Cedar.Thm.SymCC.Term.PE
import Cedar.Thm.SymCC.Term.Same


/-!
The main lemma in this file, `concretize?_wfl_some`, proves that
`εnv.concretize? x` succeeds when `εnv` is a literal symbolic environment that
is well-formed with respect to `x`.
-/

namespace Cedar.Thm

open Data Spec SymCC Factory

private theorem wfl_term_ofStringType_implies_tag?_some {t : Term} {εs : SymEntities} :
  t.WellFormedLiteral εs → t.typeOf = .string →
  ∃ tag, t.tag? = some tag
:= by
  intro hw hty
  simp only [Term.tag?]
  split
  · simp only [Option.some.injEq, exists_eq']
  · rename_i h
    replace ⟨s, hwfl⟩ := wfl_of_type_string_is_string hw hty
    subst hwfl
    simp only [Term.prim.injEq, TermPrim.string.injEq, imp_false, forall_eq'] at h

private theorem wfl_term_isEntityType_implies_entityUID?_some {t : Term} {εs : SymEntities} :
  t.WellFormedLiteral εs → t.typeOf.isEntityType →
  ∃ uid, t.entityUID? = some uid
:= by
  intro hw hty
  simp only [Term.entityUID?]
  split
  · simp only [Option.some.injEq, exists_eq']
  · rename_i h
    replace ⟨ety, hty⟩ := isEntityType_implies_entity_type hty
    replace ⟨uid, heq, _⟩ := wfl_of_type_entity_is_entity hw hty
    simp only [heq, Term.prim.injEq, TermPrim.entity.injEq, imp_false, forall_eq'] at h

private theorem wfl_term_isEntitySetType_implies_setOfEntityUIDs?_some {t : Term} {ety : EntityType} {εs : SymEntities} :
  t.WellFormedLiteral εs →
  t.typeOf = .set (.entity ety) →
  ∃ s, t.setOfEntityUIDs? = some s
:= by
  intro hwl hty
  have ⟨s, hs⟩ := wfl_of_type_set_is_set hwl hty
  subst hs
  simp only [Term.setOfEntityUIDs?, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq]
  have h : ∀ t ∈ s.1, ∃ uid, t.entityUID? = some uid := by
    intro t hin
    replace hty : t.typeOf.isEntityType := by
      simp only [TermType.isEntityType, wf_term_set_implies_typeOf_elt hwl.left hin]
    have hwt := wf_term_set_implies_wf_elt hwl.left hin
    have hlit := lit_term_set_implies_lit_elt hwl.right hin
    exact wfl_term_isEntityType_implies_entityUID?_some (And.intro hwt hlit) hty
  replace ⟨uids, h⟩ := List.all_some_implies_mapM_some h
  exists (Set.make uids), uids

private theorem wfl_term_isCedarRecordType_implies_recordValue?_some {t : Term} {εs : SymEntities} :
  t.WellFormedLiteral εs → t.typeOf.isCedarRecordType →
  ∃ r, t.recordValue? = some r
:= by
  intro hw hty
  have ⟨rty, hrty⟩ := isCedarRecordType_implies_term_record_type hty
  have ⟨r, heq⟩ := wfl_of_type_record_is_record hw hrty
  subst heq
  simp only [TermType.isCedarRecordType] at hty
  split at hty <;> simp only [Bool.false_eq_true] at hty
  rename_i hcty
  have ⟨v, hv⟩ := term_value?_exists hw hcty
  simp only [Term.recordValue?, Option.bind_eq_bind, Option.bind_eq_some]
  replace ⟨rv, hv, hr⟩ := same_record_term_implies (same_values_def.mpr hv)
  exists rv, v
  subst hv
  simp only [hr, Value.record?, and_self]

private theorem wfl_term_isStringSetType_implies_setOfTags?_some {t : Term} {εs : SymEntities} :
  t.WellFormedLiteral εs →
  t.typeOf = .set .string →
  ∃ s, t.setOfTags? = some s
:= by
  intro hwl hty
  have ⟨s, hs⟩ := wfl_of_type_set_is_set hwl hty
  subst hs
  simp only [Term.setOfTags?, Option.bind_eq_bind]
  have h : ∀ t ∈ s.1, ∃ tag, t.tag? = some tag := by
    intro t hin
    have hwt := wf_term_set_implies_wf_elt hwl.left hin
    have hlit := lit_term_set_implies_lit_elt hwl.right hin
    replace hty := wf_term_set_implies_typeOf_elt hwl.left hin
    exact wfl_term_ofStringType_implies_tag?_some (And.intro hwt hlit) hty
  replace ⟨tags, h⟩ := List.all_some_implies_mapM_some h
  simp only [h, Option.some_bind, Option.some.injEq, exists_eq']

private theorem concretize?_wfl_ρ_implies_some {ρ : SymRequest} {εs : SymEntities} :
  ρ.WellFormed εs → ρ.isLiteral →
  ∃ (r : Request), ρ.concretize? = .some r
:= by
  intro hwρ hlit
  simp only [SymRequest.concretize?, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq]
  simp only [SymRequest.isLiteral, Bool.and_eq_true] at hlit
  replace ⟨hw, hty, hwρ⟩ := hwρ
  have ⟨p, hp⟩ := wfl_term_isEntityType_implies_entityUID?_some (And.intro hw hlit.left.left.left) hty
  replace ⟨hw, hty, hwρ⟩ := hwρ
  have ⟨a, ha⟩ := wfl_term_isEntityType_implies_entityUID?_some (And.intro hw hlit.left.left.right) hty
  replace ⟨hw, hty, hwρ⟩ := hwρ
  have ⟨r, hr⟩ := wfl_term_isEntityType_implies_entityUID?_some (And.intro hw hlit.left.right) hty
  replace ⟨hw, hty⟩ := hwρ
  have ⟨c, hc⟩ := wfl_term_isCedarRecordType_implies_recordValue?_some (And.intro hw hlit.right) hty
  simp only [hp, Option.some.injEq, ha, hr, hc, exists_eq_left', exists_eq']

private theorem wf_term_prim_implies_valid_uids {t : TermPrim} {εs : SymEntities} :
  t.WellFormed εs →
  ∀ uid ∈ t.entityUIDs, εs.isValidEntityUID uid
:= by
  intro hwf uid hin
  simp only [TermPrim.entityUIDs] at hin
  split at hin
  · rename_i uid'
    simp only [Set.mem_singleton_iff_eq] at hin
    subst hin
    cases hwf ; rename_i hwf
    exact hwf
  · have _ := Set.empty_no_elts uid
    contradiction

theorem wf_term_implies_valid_uids {t : Term} {εs : SymEntities} :
  t.WellFormed εs →
  ∀ uid ∈ t.entityUIDs, εs.isValidEntityUID uid
:= by
  intro hwf uid hin
  unfold Term.entityUIDs at hin
  cases t <;> simp only at hin
  case var | none =>
    have _ := Set.empty_no_elts uid
    contradiction
  case prim =>
    cases hwf ; rename_i hwf
    exact wf_term_prim_implies_valid_uids hwf uid hin
  case some =>
    replace hwf := wf_term_some_implies hwf
    exact wf_term_implies_valid_uids hwf uid hin
  case set ts _ =>
    cases ts ; rename_i ts
    simp only [List.attach_def, List.mapUnion_pmap_subtype Term.entityUIDs] at hin
    rw [Set.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨t', hin', hin⟩ := hin
    replace hwf := wf_term_set_implies_wf_elt hwf hin'
    exact wf_term_implies_valid_uids hwf uid hin
  case record ats =>
    cases ats ; rename_i ats
    simp only [List.attach₃, List.mapUnion_pmap_subtype λ x : Attr × Term => x.snd.entityUIDs] at hin
    rw [Set.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨at', hin', hin⟩ := hin
    replace hwf := wf_term_record_implies_wf_value hwf hin'
    exact wf_term_implies_valid_uids hwf uid hin
  case app ts _ =>
    simp only [List.attach_def, List.mapUnion_pmap_subtype Term.entityUIDs] at hin
    rw [Set.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨t', hin', hin⟩ := hin
    cases hwf ; rename_i hwf _
    specialize hwf t' hin'
    exact wf_term_implies_valid_uids hwf uid hin
termination_by t
decreasing_by
  all_goals (simp_wf ; clear hin)
  · rename_i h _ ; subst h
    simp only [Term.some.sizeOf_spec]
    omega
  · rename_i h _ _ _ _ _ ; subst h
    rename_i h _ _ _ _ _ _ ; subst h
    have hs := List.sizeOf_lt_of_mem hin'
    simp only [Term.set.sizeOf_spec, Set.mk.sizeOf_spec, gt_iff_lt]
    omega
  · rename_i h _ _ _ _ _ ; subst h
    rename_i h _ _ _ _ _ _ ; subst h
    have hs := List.sizeOf_lt_of_mem hin'
    have hp : at' = (at'.fst, at'.snd) := by simp only
    rw [hp] at hs
    simp only [Prod.mk.sizeOf_spec] at hs
    simp only [Term.record.sizeOf_spec, Map.mk.sizeOf_spec, gt_iff_lt]
    omega
  · rename_i h _ _ _ _ _ _ _ _ _ _ _ _ _ _ ; subst h
    have hs := List.sizeOf_lt_of_mem hin'
    simp only [Term.app.sizeOf_spec]
    omega

private theorem wf_ρ_implies_valid_uids {ρ : SymRequest} {εs : SymEntities} :
  ρ.WellFormed εs →
  ∀ uid ∈ ρ.entityUIDs, εs.isValidEntityUID uid
:= by
  intro hwρ uid hin
  simp only [SymRequest.entityUIDs, Set.mem_union_iff_mem_or] at hin
  have ⟨hp, _, ha, _, hr, _, hc, _⟩ := hwρ
  rcases hin with ((hin | hin) | hin) | hin
  · exact (wf_term_implies_valid_uids hp) uid hin
  · exact (wf_term_implies_valid_uids ha) uid hin
  · exact (wf_term_implies_valid_uids hr) uid hin
  · exact (wf_term_implies_valid_uids hc) uid hin

private theorem valid_refs_implies_valid_uids {x : Expr} {εs : SymEntities} :
  x.ValidRefs (λ y => εs.isValidEntityUID y) →
  ∀ uid ∈ x.entityUIDs, εs.isValidEntityUID uid
:= by
  intro hvr uid hin
  induction hvr <;> simp only [Expr.entityUIDs] at hin
  case var_valid =>
    have _ := Set.empty_no_elts uid
    contradiction
  case lit_valid p h =>
    simp only [Prim.entityUIDs] at hin
    split at hin
    · simp only [Prim.ValidRef] at h
      rw [Set.mem_singleton_iff_eq] at hin
      subst hin
      exact h
    · have _ := Set.empty_no_elts uid
      contradiction
  case and_valid ih₁ ih₂ | or_valid ih₁ ih₂ | binaryApp_valid ih₁ ih₂ =>
    rw [Set.mem_union_iff_mem_or] at hin
    rcases hin with hin | hin
    · exact ih₁ hin
    · exact ih₂ hin
  case unaryApp_valid ih | hasAttr_valid ih | getAttr_valid ih =>
    exact ih hin
  case ite_valid ih₁ ih₂ ih₃ =>
    simp only [Set.mem_union_iff_mem_or] at hin
    rcases hin with (hin | hin) | hin
    · exact ih₁ hin
    · exact ih₂ hin
    · exact ih₃ hin
  case set_valid ih | call_valid ih =>
    simp only [List.attach_def, List.mapUnion_pmap_subtype, Set.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨x', hin', hin⟩ := hin
    exact ih x' hin' hin
  case record_valid ih =>
    simp only [List.attach₂, List.mapUnion_pmap_subtype λ x : Attr × Expr => x.snd.entityUIDs,
      Set.mem_mapUnion_iff_mem_exists] at hin
    replace ⟨ax', hin', hin⟩ := hin
    exact ih ax' hin' hin

private theorem εs_find?_δ_implies_mems_valid_uids {δ : SymEntityData} {ety : EntityType} {εs : SymEntities} :
  Map.find? εs ety = some δ →
  ∀ uid ∈ SymEntityData.entityUIDs.mems ety δ, εs.isValidEntityUID uid
:= by
  intro hf uid hin
  simp only [SymEntityData.entityUIDs.mems] at hin
  split at hin
  · have _ := Set.empty_no_elts uid
    contradiction
  · rename_i hs
    simp only [← Set.make_mem, List.mem_map] at hin
    replace ⟨eid, hin, heq⟩ := hin
    subst heq
    rw [Set.in_list_iff_in_set] at hin
    simp only [SymEntities.isValidEntityUID, hf, hs, Set.contains_prop_bool_equiv, hin]

private theorem wf_uf_implies_valid_uids {uf : UnaryFunction} {εs : SymEntities} :
  uf.WellFormed εs →
  ∀ uid ∈ uf.entityUIDs, εs.isValidEntityUID uid
:= by
  intro hwf uid hin
  simp only [UnaryFunction.entityUIDs] at hin
  split at hin
  · have _ := Set.empty_no_elts uid
    contradiction
  · simp only [UDF.entityUIDs, Set.mem_union_iff_mem_or] at hin
    simp only [UnaryFunction.WellFormed, UDF.WellFormed] at hwf
    rcases hin with hin | hin
    · exact wf_term_implies_valid_uids hwf.left.left _ hin
    · rw [Set.mem_mapUnion_iff_mem_exists] at hin
      replace ⟨(tᵢ, tₒ), hin, hin'⟩ := hin
      simp only [Set.mem_union_iff_mem_or] at hin'
      replace hwf := hwf.right.right.right tᵢ tₒ hin
      rcases hin' with hin' | hin'
      · exact wf_term_implies_valid_uids hwf.left.left _ hin'
      · exact wf_term_implies_valid_uids hwf.right.right.left.left _ hin'

private theorem wf_δ_implies_attrs_valid_uids {δ : SymEntityData} {ety : EntityType} {εs : SymEntities} :
  δ.WellFormed εs ety →
  ∀ uid ∈ SymEntityData.entityUIDs.attrs δ, εs.isValidEntityUID uid
:= by
  intro hwδ uid hin
  simp only [SymEntityData.entityUIDs.attrs] at hin
  exact wf_uf_implies_valid_uids hwδ.left _ hin

private theorem wf_δ_implies_ancs_valid_uids {δ : SymEntityData} {ety : EntityType} {εs : SymEntities} :
  δ.WellFormed εs ety →
  ∀ uid ∈ SymEntityData.entityUIDs.ancs δ, εs.isValidEntityUID uid
:= by
  intro hwδ uid hin
  simp only [SymEntityData.entityUIDs.ancs] at hin
  rw [Set.mem_mapUnion_iff_mem_exists] at hin
  replace ⟨(ancTy, ancF), hin', hin⟩ := hin
  simp only at hin
  rw [Map.in_list_iff_find?_some hwδ.right.right.right.right.left] at hin'
  replace hwδ := hwδ.right.right.right.left ancTy ancF hin'
  exact wf_uf_implies_valid_uids hwδ.left _ hin

private theorem wf_δ_implies_tags_valid_uids {δ : SymEntityData} {ety : EntityType} {εs : SymEntities} :
  δ.WellFormed εs ety →
  ∀ uid ∈ SymEntityData.entityUIDs.tags δ, εs.isValidEntityUID uid
:= by
  intro hwδ uid hin
  simp only [SymEntityData.entityUIDs.tags] at hin
  split at hin
  · simp only [Set.empty_no_elts] at hin
  · rename_i τs hτs
    replace hwδ := hwδ.right.right.right.right.right.left τs hτs
    replace hwδ := hwδ.right.right.right.left
    exact wf_uf_implies_valid_uids hwδ _ hin

private theorem wf_δ_implies_valid_uids {δ : SymEntityData} {ety : EntityType} {εs : SymEntities} :
  Map.find? εs ety = some δ →
  δ.WellFormed εs ety →
  ∀ uid ∈ δ.entityUIDs ety, εs.isValidEntityUID uid
:= by
  intro hf hwδ uid hin
  simp only [SymEntityData.entityUIDs, Set.mem_union_iff_mem_or] at hin
  rcases hin with ((hin | hin) | hin) | hin
  · exact εs_find?_δ_implies_mems_valid_uids hf _ hin
  · exact wf_δ_implies_attrs_valid_uids hwδ _ hin
  · exact wf_δ_implies_ancs_valid_uids hwδ _ hin
  · exact wf_δ_implies_tags_valid_uids hwδ _ hin

private theorem wf_εs_implies_valid_uids {εs : SymEntities} :
  εs.WellFormed →
  ∀ uid ∈ εs.entityUIDs, εs.isValidEntityUID uid
:= by
  intro hwε uid hin
  simp only [SymEntities.entityUIDs] at hin
  rw [Set.mem_mapUnion_iff_mem_exists] at hin
  replace ⟨(ety, δ), hin', hin⟩ := hin
  simp at hin
  replace ⟨hwm, hwε⟩ := hwε
  rw [Map.in_list_iff_find?_some hwm] at hin'
  specialize hwε ety δ hin'
  exact wf_δ_implies_valid_uids hin' hwε _ hin

private theorem UF_isLiteral_implies_UDF_isLiteral {f : UnaryFunction} :
  f.isLiteral ↔ ∃ g, f = .udf g ∧ g.isLiteral
:= by
  simp only [UnaryFunction.isLiteral]
  split <;>
  simp only [UnaryFunction.udf.injEq, exists_eq_left', Bool.false_eq_true, false_and, exists_const, reduceCtorEq]

private theorem pe_app_wfl' {εs : SymEntities} {f : UnaryFunction} {t : Term} :
  Term.WellFormedLiteral εs t →
  f.WellFormed εs →
  f.isLiteral →
  Term.isLiteral (app f t) = true
:= by
  intro hwt hwf hlit
  rw [UF_isLiteral_implies_UDF_isLiteral] at hlit
  replace ⟨g, heq, _⟩ := hlit
  subst heq
  simp only [UnaryFunction.WellFormed] at hwf
  exact pe_app_wfl hwt hwf

private theorem wfl_τs_getTag!_value?_some {uid : EntityUID} {τs : SymTags} {εs : SymEntities} (k : String) :
  τs.WellFormed εs uid.ty →
  τs.vals.isLiteral →
  (Term.entity uid).WellFormedLiteral εs →
  ∃ v, (τs.getTag! (.entity uid) (.string k)).value? = .some v
:= by
  intro hwτs hwl hwt₁
  have hwt₂ : (tagOf (Term.entity uid) (Term.string k)).WellFormed εs := by
    simp only [wf_tagOf hwt₁.left wf_string typeOf_term_prim_entity typeOf_term_prim_string]
  have hlit : (τs.getTag! (Term.entity uid) (Term.string k)).isLiteral := by
    simp only [SymTags.getTag!]
    exact pe_app_wfl' (And.intro hwt₂ (lit_tagOf uid k)) hwτs.right.right.right.left hwl
  have hwt₃ := @wf_tags_getTag! εs τs (.entity uid) (.string k) uid.ty hwτs hwt₁.left
    wf_string typeOf_term_prim_entity typeOf_term_prim_string
  have ⟨_, hty⟩ : ∃ ty, (τs.getTag! (.entity uid) (.string k)).typeOf.cedarType? = .some ty := by
    have hty := hwτs.right.right.right.right.right
    simp only [TermType.isCedarType, Option.isSome_iff_exists] at hty
    rw [← hwt₃.right] at hty
    exact hty
  exact term_value?_exists (And.intro hwt₃.left hlit) hty

private theorem concretize?_wfl_τs_vals_implies_some {uid : EntityUID} {τs : SymTags} {εs : SymEntities} (keys : List String) :
  τs.WellFormed εs uid.ty →
  τs.vals.isLiteral →
  (Term.entity uid).WellFormedLiteral εs →
  ∃ tvs,
    (keys.mapM (SymEntityData.concretize?.taggedValueFor τs (Term.entity uid))) =
    some tvs
:= by
  intro hwτs hlit hwt
  have h : ∀ k ∈ keys,
    ∃ kv, (do .some (k, ← (τs.getTag! (.entity uid) (.string k)).value?)) = .some kv
  := by
    intro k _
    have ⟨_, heq⟩ := wfl_τs_getTag!_value?_some k hwτs hlit hwt
    simp only [heq, Option.bind_some_fun, Option.some.injEq, exists_eq']
  replace ⟨kvs, _⟩ := List.all_some_implies_mapM_some h
  exists kvs

private theorem concretize?_wfl_δ_implies_some {uid : EntityUID} {δ : SymEntityData} {εs : SymEntities} :
  Map.find? εs uid.ty = some δ →
  δ.WellFormed εs uid.ty →
  δ.isLiteral →
  SymEntityData.concretize?.isValidEntityUID uid δ →
  ∃ d, δ.concretize? uid = some d
:= by
  intro hf hwδ hlit hvu
  simp only [SymEntityData.concretize?, hvu, ↓reduceIte, Option.bind_eq_bind, Option.bind_some_fun,
    Option.bind_eq_some, Option.some.injEq]
  replace hvu := concretize?_δ_isValidEntityUID_implies_wfl hf hvu
  have ⟨hwf₁, hty₁⟩ := wf_δ_implies_wf_app_attrs hwδ hvu.left
  replace hty₁ : (Factory.app δ.attrs (Term.entity uid)).typeOf.isCedarRecordType := by
    simp only [hty₁, hwδ.right.right.left]
  simp only [SymEntityData.isLiteral, Bool.and_eq_true, List.all_eq_true] at hlit
  have hlit₁ := pe_app_wfl' hvu hwδ.left hlit.left.left
  have ⟨r, hr⟩ := wfl_term_isCedarRecordType_implies_recordValue?_some (And.intro hwf₁ hlit₁) hty₁
  have h : ∀ anc ∈ δ.ancestors.kvs, ∃ uids, (app anc.snd (.entity uid)).setOfEntityUIDs? = some uids := by
    intro (ancTy, ancF) hin
    have hlit₂ := hlit.left.right (ancTy, ancF) hin
    simp only at hlit₂
    rw [Map.in_list_iff_find?_some hwδ.right.right.right.right.left] at hin
    have ⟨hwf₂, hty₂⟩ := wf_δ_implies_wf_app_ancs hwδ hvu.left hin
    simp [SymEntityData.WellFormed] at hwδ
    replace hlit₂ := pe_app_wfl' hvu (hwδ.right.right.right.left ancTy ancF hin).left hlit₂
    simp [wfl_term_isEntitySetType_implies_setOfEntityUIDs?_some (And.intro hwf₂ hlit₂) hty₂]
  replace ⟨ancs, h⟩ := List.all_some_implies_mapM_some h
  simp only [hr, Option.some.injEq, h, exists_eq_left']
  simp only [SymEntityData.concretize?.tags]
  split
  · simp only [Option.some.injEq, exists_eq_left', exists_eq']
  · rename_i τs hτs
    have ⟨hwf₂, hty₂⟩ := wf_δ_implies_wf_app_tags_keys hwδ hvu.left hτs
    replace hwδ := hwδ.right.right.right.right.right.left τs hτs
    replace hlit := hlit.right
    simp only [hτs, Option.all_some, SymTags.isLiteral, Bool.and_eq_true] at hlit
    have hlit₂ := pe_app_wfl' hvu hwδ.left hlit.left
    have ⟨keys, hts⟩ := wfl_term_isStringSetType_implies_setOfTags?_some (And.intro hwf₂ hlit₂) hty₂
    simp only [hts, Option.bind_some_fun]
    replace ⟨_, hts⟩ := concretize?_wfl_τs_vals_implies_some keys.elts hwδ hlit.right hvu
    rw [hts]
    simp only [Option.bind_some_fun, Option.some.injEq, exists_eq_left', exists_eq']

private theorem concretize?_wfl_εs_implies_entityData?_some {uid : EntityUID} {εs : SymEntities} :
  εs.WellFormed →
  εs.isLiteral →
  εs.isValidEntityUID uid →
  ∃ ed, SymEntities.concretize?.entityData? εs uid = some ed
:= by
  intro hwε hlit hvu
  simp only [SymEntities.concretize?.entityData?, Option.bind_eq_bind, Option.bind_eq_some,
    Option.some.injEq]
  simp only [SymEntities.isValidEntityUID] at hvu
  split at hvu <;> try simp only [Bool.false_eq_true] at hvu
  rename_i δ hf
  replace hvu : SymEntityData.concretize?.isValidEntityUID uid δ := by
    simp only [SymEntityData.concretize?.isValidEntityUID]
    exact hvu
  replace hwε := hwε.right uid.ty δ hf
  simp only [SymEntities.isLiteral, List.all_eq_true] at hlit
  specialize hlit (uid.ty, δ) (Map.find?_mem_toList hf)
  simp only at hlit
  have ⟨d, h⟩ := concretize?_wfl_δ_implies_some hf hwε hlit hvu
  simp only [hf, Option.some.injEq, exists_eq_left', h, exists_eq']

private theorem concretize?_wfl_εs_implies_some {εs : SymEntities} {uids : Set EntityUID} :
  εs.WellFormed → εs.isLiteral →
  (∀ uid ∈ uids, εs.isValidEntityUID uid) →
  ∃ (es : Entities), εs.concretize? uids = .some es
:= by
  intro hwε hlit hvu
  replace hvu := (Set.prop_union_iff_prop_and _ _ _).mp (And.intro hvu (wf_εs_implies_valid_uids hwε))
  have h : ∀ uid ∈ (uids ∪ εs.entityUIDs).1, ∃ tyd, SymEntities.concretize?.entityData? εs uid = some tyd := by
    intro uid hin
    rw [Set.in_list_iff_in_set] at hin
    specialize hvu uid hin
    exact concretize?_wfl_εs_implies_entityData?_some hwε hlit hvu
  replace ⟨es, h⟩ := List.all_some_implies_mapM_some h
  simp only [Union.union] at h
  simp only [SymEntities.concretize?]
  exists (Map.make es)
  simp only [h, Option.bind_some_fun]

theorem concretize?_wfl_implies_some {x : Expr} {εnv : SymEnv} :
  εnv.WellFormedLiteralFor x →
  ∃ (env : Env), εnv.concretize? x = .some env
:= by
  intro hwε
  simp only [SymEnv.concretize?]
  replace ⟨hwε, hlit⟩ := hwε
  simp only [SymEnv.isLiteral, Bool.and_eq_true] at hlit
  have ⟨_, hρ⟩ := concretize?_wfl_ρ_implies_some hwε.left.left hlit.left
  have hvρ := wf_ρ_implies_valid_uids hwε.left.left
  have hvx := valid_refs_implies_valid_uids hwε.right
  have hvu := (Set.prop_union_iff_prop_and _ _ _).mp (And.intro hvx hvρ)
  have ⟨_, hεs⟩ := concretize?_wfl_εs_implies_some hwε.left.right hlit.right hvu
  simp only [hρ, hεs, Option.bind_some_fun, Option.some.injEq, exists_eq']

end Cedar.Thm
