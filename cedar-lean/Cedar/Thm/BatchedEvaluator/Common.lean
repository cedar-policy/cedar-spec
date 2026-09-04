import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Thm.TPE.Input

/-!
Shared definitions and lemmas for batched evaluator theorems.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- A well behaved entity loader
1. Loads all the requested entities, returning none for missing entities
2. Refines the backing entity store

The first condition is required for convergence of
batched evaluation, which has not been proven. It is unused
in the code base at the moment.
-/
abbrev EntityLoader.WellBehaved (store: Entities) (loader: EntityLoader) : Prop :=
  ∀ s, s ⊆ (loader s).keys ∧
       EntitiesRefine store ((loader s).mapOnValues MaybeEntityData.asPartial)

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
    exact ⟨data, hdata, .some _ rfl hattrs.symm, .some _ rfl hanc.symm, .some _ rfl htags.symm⟩

theorem as_partial_request_refines {req : Request} :
  RequestRefines req req.asPartialRequest := by
  simp only [Request.asPartialRequest, RequestRefines, PartialEntityUID.asEntityUID, Option.map_some]
  constructor
  · apply PartialIsValid.some <;> rfl
  constructor
  · trivial
  constructor
  · apply PartialIsValid.some <;> rfl
  constructor
  · apply PartialIsValid.some <;> rfl
  constructor <;> trivial

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

theorem direct_request_and_entities_refine (req : Request) (es : Entities) :
  RequestAndEntitiesRefine req es req.asPartialRequest es.asPartial := by
  constructor
  · exact as_partial_request_refines
  · unfold EntitiesRefine Entities.asPartial
    intro uid data₂ h_find
    have h_mapOnValues := Map.find?_mapOnValues_some' EntityData.asPartial h_find
    obtain ⟨data₁, h_find₁, h_eq⟩ := h_mapOnValues
    exists data₁
    exact ⟨h_find₁,
           by rw [h_eq]; apply PartialIsValid.some <;> rfl,
           by rw [h_eq]; apply PartialIsValid.some <;> rfl,
           by rw [h_eq]; apply PartialIsValid.some <;> rfl⟩

end Cedar.Thm
