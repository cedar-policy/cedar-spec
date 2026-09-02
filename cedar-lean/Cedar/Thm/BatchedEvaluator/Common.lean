import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.Attrs

/-!
Shared definitions and lemmas for batched evaluator theorems.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- A well behaved entity loader refines the backing entity store on every
requested slice.

(A convergence-oriented "loads all the requested entities" condition is not
included here: it is required only for a batched-evaluation convergence proof
that has not been done and is unused elsewhere.)
-/
abbrev EntityLoader.WellBehaved (ets : EntitySchema) (store: Entities) (loader: EntityLoader) : Prop :=
  ∀ s, EntitiesRefine store (SlicedEntities.asPartial ets (loader s))

/-- `Schema.environment?` carries the schema's entity and action types through unchanged. -/
theorem environment?_schema {schema : Schema} {pty rty : EntityType} {act : EntityUID}
  {env : TypeEnv} (h : schema.environment? pty rty act = .some env) :
  env.ets = schema.ets ∧ env.acts = schema.acts
:= by
  simp only [Schema.environment?] at h
  cases h_find : schema.acts.find? act <;>
    simp only [h_find, Option.bind_none_fun, Option.bind_some_fun, reduceCtorEq] at h
  split at h <;> simp only [reduceCtorEq, Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

theorem actionEntities_refines {env : TypeEnv} {es : Entities}
  (hwf : env.WellFormed) (hinst : InstanceOfSchema es env) :
  EntitiesRefine es (actionEntities env.acts)
:= by
  intro uid ped hfind
  rw [actionEntities] at hfind
  have hmem := Data.Map.mem_make_mem_list (Data.Map.find?_mem_toList hfind)
  simp only [List.mem_map, Prod.mk.injEq] at hmem
  obtain ⟨p, hp, huid, hped⟩ := hmem
  subst huid
  subst hped
  have hact : env.acts.find? p.fst = .some p.snd :=
    (Data.Map.in_list_iff_find?_some hwf.2.1.1).mp hp
  obtain ⟨data, hdata⟩ := hinst.2 p.fst p.snd hact
  rcases hinst.1 p.fst data hdata with hentity | haction
  · exfalso
    obtain ⟨entry, hentry, _⟩ := hentity
    refine hwf.2.1.2.2.1 p.fst ?_ ?_
    · show (env.acts.find? p.fst).isSome = true
      simp only [hact, Option.isSome_some]
    · show (env.ets.find? p.fst.ty).isSome = true
      simp only [hentry, Option.isSome_some]
  · obtain ⟨hattrs, htags, entry, hentry, hanc⟩ := haction
    have hentry' : entry = p.snd := by
      rw [hact] at hentry
      simpa only [Option.some.injEq] using hentry.symm
    subst hentry'
    -- `EntitiesRefine` now states the three components independently, and an empty partial record
    -- claims nothing, so it is consistent with whatever the concrete entity carries.
    have hempty : ∀ (m : Data.Map Attr Value), PartialRecordConsistent Map.empty m := by
      intro m a
      simp only [PartialRecord.attr, Data.Map.find?_empty, Option.getD_none]
      exact .unknown
    have hanc' : p.snd.ancestors = es.ancestorsOrEmpty p.fst := by
      simp only [Entities.ancestorsOrEmpty, hdata]
      exact hanc.symm
    exact ⟨.some _ rfl ⟨data, hdata, hempty _⟩, .some _ rfl hanc',
      .some _ rfl ⟨data, hdata, hempty _⟩⟩

/--
A partial record built from a concrete record by `PartialRecord.ofConcrete`
claims nothing about that record that isn't true.
-/
theorem of_concrete_consistent {m : Data.Map Attr Value} {rty : RecordType} :
  PartialRecordConsistent (PartialRecord.ofConcrete m rty) m
:= by
  intro a
  rw [ofConcrete_attr]
  cases hm : m.find? a with
  | some v => simp only; exact .value
  | none =>
    cases (rty.find? a).isSome
    · simp only [Bool.false_eq_true, if_false]; exact .unknown
    · simp only [if_true]; exact .absent

/-- A partial record built from concrete tags claims nothing about them that isn't true. -/
theorem of_concrete_tags_consistent {m : Data.Map Tag Value} :
  PartialRecordConsistent (PartialRecord.ofConcreteTags m) m
:= by
  intro a
  simp only [PartialRecord.attr, PartialRecord.ofConcreteTags, Map.find?_mapOnValues]
  cases hm : m.find? a with
  | none => simp only [Option.map_none, Option.getD_none]; exact .unknown
  | some v => simp only [Option.map_some, Option.getD_some]; exact .value

/-- Validity of the partial record built from a concrete record implies full
`instanceOfType` conformance: the closed-record absent-marking recovers the
"required attributes present" and "no undeclared attributes" checks. -/
theorem instanceOfType_of_ofConcrete_valid {schema : Schema} {m : Data.Map Attr Value} {rty : RecordType}
  (hmwf : m.WellFormed)
  (h : partialRecordIsValid schema (PartialRecord.ofConcrete m rty) rty = true) :
  instanceOfType (.record m) (.record rty) schema = true
:= by
  obtain ⟨hA, hB⟩ := partialRecordIsValid_inv h
  simp only [instanceOfType, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- present attributes are declared
    intro (k, v) hmem
    have hw : m.find? k = some v := (Data.Map.in_list_iff_find?_some hmwf).mp hmem
    have hattr : (PartialRecord.ofConcrete m rty).attr k = .value v := by
      rw [ofConcrete_attr, hw]
    have := hB k (by rw [hattr]; rfl)
    simpa only [Map.contains] using this
  · -- present attributes have the declared type
    intro ⟨(k, v), hsz⟩ hmem
    simp only [List.attach₂, List.mem_pmap_subtype] at hmem
    cases hrf : rty.find? k with
    | none => simp []
    | some qty =>
      simp only
      have hw : m.find? k = some v := (Data.Map.in_list_iff_find?_some hmwf).mp hmem
      have hAentry := hA k qty hrf
      rw [ofConcrete_attr, hw] at hAentry
      exact hAentry
  · -- required attributes are present
    intro (k, qty) hmem
    simp only [requiredAttributePresent]
    cases hrf : rty.find? k with
    | none => simp
    | some qty' =>
      by_cases hreq : qty'.isRequired
      · simp only [hreq, if_true]
        have hAentry := hA k qty' hrf
        rw [ofConcrete_attr] at hAentry
        cases hm : m.find? k with
        | some w => simp only [Map.contains, hm, Option.isSome_some]
        | none =>
          rw [hm] at hAentry
          simp only [hrf, Option.isSome_some, if_true] at hAentry
          simp only [hreq, Bool.true_eq_false] at hAentry
      · simp [hreq]

theorem as_partial_request_refines {req : Request} {ctxTy : RecordType}
  (hwf : req.context.WellFormed) :
  RequestRefines req (req.asPartialRequest ctxTy) := by
  simp only [Request.asPartialRequest, RequestRefines, PartialEntityUID.asEntityUID, Option.map_some]
  refine ⟨by apply PartialIsValid.some <;> rfl, trivial,
          by apply PartialIsValid.some <;> rfl, ?_, trivial, trivial⟩
  exact .some _ rfl ⟨Map.make_wf _, hwf, of_concrete_consistent⟩

theorem any_refines_empty_entities :
  EntitiesRefine es Data.Map.empty := by
  simp only [EntitiesRefine, Data.Map.empty, Data.Map.find?, Map.toList]
  intro a e₂ h₁
  contradiction

theorem entities_refine_append (es : Entities) (m1 m2 : PartialEntities) :
  EntitiesRefine es m1 → EntitiesRefine es m2 → EntitiesRefine es (m2 ++ m1) := by
  intro h1 h2
  unfold EntitiesRefine
  intro a e₂ h_find
  rw [Map.find?_append] at h_find
  cases h_case : m2.find? a with
  | some e₂' =>
    have h_eq : e₂ = e₂' := by
      rw [h_case] at h_find
      simp only [Option.some_or, Option.some.injEq] at h_find
      rw [h_find]
    rw [h_eq]
    exact h2 a e₂' h_case
  | none =>
    have h_find1 : m1.find? a = some e₂ := by
      rw [h_case] at h_find
      simp only [Option.none_or] at h_find
      rw [h_find]
    exact h1 a e₂ h_find1

theorem direct_request_and_entities_refine (ets : EntitySchema) (req : Request) (es : Entities) (ctxTy : RecordType)
  (hwf : req.context.WellFormed) :
  RequestAndEntitiesRefine req es (req.asPartialRequest ctxTy) (Entities.asPartial ets es) := by
  constructor
  · exact as_partial_request_refines hwf
  · unfold EntitiesRefine
    intro uid data₂ h_find
    rw [find?_as_partial] at h_find
    cases h_find₁ : es.find? uid with
    | none => rw [h_find₁] at h_find; simp at h_find
    | some data₁ =>
      rw [h_find₁] at h_find
      simp only [Option.map_some, Option.some.injEq] at h_find
      subst h_find
      simp only [EntityData.asPartial]
      refine ⟨?_, ?_, ?_⟩
      · exact .some _ rfl ⟨data₁, h_find₁, of_concrete_consistent⟩
      · exact .some _ rfl (by
          simp only [Entities.ancestorsOrEmpty, h_find₁])
      · exact .some _ rfl ⟨data₁, h_find₁, of_concrete_tags_consistent⟩

end Cedar.Thm
