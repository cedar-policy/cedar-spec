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

/-- A well behaved entity loader
1. Loads all the requested entities, returning none for missing
entities
2. Refines the backing entity store

The first condition is required for convergence of
batched evaluation, which has not been proven. It is unused
in the code base at the moment.
-/
abbrev EntityLoader.WellBehaved (store: Entities) (loader: EntityLoader) : Prop :=
  ∀ s, s ⊆ (loader s).keys ∧
       EntitiesRefine store ((loader s).mapOnValues MaybeEntityData.asPartial)

theorem as_partial_request_refines {req : Request} :
  RequestRefines req req.asPartialRequest := by
  simp only [Request.asPartialRequest, RequestRefines, PartialEntityUID.asEntityUID, Option.map_some]
  constructor
  · apply PartialIsValid.some
    rfl
  constructor
  · trivial
  constructor
  · apply PartialIsValid.some
    rfl
  constructor
  · apply PartialIsValid.some
    rfl
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
           by rw [h_eq]; apply PartialIsValid.some; rfl,
           by rw [h_eq]; apply PartialIsValid.some; rfl,
           by rw [h_eq]; apply PartialIsValid.some; rfl⟩

end Cedar.Thm
