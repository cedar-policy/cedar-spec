import Cedar.TPE.Input
import Cedar.TPE.BatchedEvaluator
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation
import Cedar.Thm.TPE

/-!
This file defines theorems related to the batched evaluator
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm
open Cedar.Data


theorem as_partial_request_refines {req : Request} :
  RequestRefines req (Request.asPartialRequest req) := by
  simp only [Request.asPartialRequest, RequestRefines, PartialEntityUID.asEntityUID, Option.map_some]
  constructor
  · apply PartialIsValid.some
    rfl
  constructor
  · trivial
  constructor
  · apply PartialIsValid.some
    rfl
  · apply PartialIsValid.some
    rfl

theorem any_refines_empty_entities :
  EntitiesRefine es Data.Map.empty := by
  simp only [EntitiesRefine, Data.Map.empty, Data.Map.find?, Map.kvs]
  intro a e₂ h₁
  contradiction

-- Helper lemma for entityLoaderFor refinement
theorem entityLoaderFor_refines (es : Entities) (toLoad : Set EntityUID) :
  EntitiesRefine es (entityLoaderFor es toLoad) := by
  unfold EntitiesRefine entityLoaderFor
  intro uid data₂ h_find
  rw [← Map.list_find?_iff_make_find?] at h_find
  have h_mem := List.mem_of_find?_eq_some h_find
  simp only [List.mem_map] at h_mem
  obtain ⟨uid', h_mem_toLoad, h_eq⟩ := h_mem

  cases h_case : es.find? uid' with
  | some data₁ =>
    -- Case: entity exists in es
    have h_simplified : (uid', data₁.asPartial) = (uid, data₂) := by
      rw [h_case] at h_eq
      exact h_eq
    have h_uid_eq : uid = uid' := by
      injection h_simplified with h_uid_eq _
      exact h_uid_eq.symm
    have h_data_eq : data₂ = data₁.asPartial := by
      injection h_simplified with _ h_data_eq
      exact h_data_eq.symm
    right
    exists data₁
    constructor
    · rw [h_uid_eq]
      exact h_case
    constructor
    · -- attrs refine
      rw [h_data_eq]
      simp only [EntityData.asPartial, PartialEntityData.attrs]
      constructor
      rfl
    constructor
    · -- ancestors refine
      rw [h_data_eq]
      simp only [EntityData.asPartial, PartialEntityData.ancestors]
      constructor
      rfl
    · -- tags refine
      rw [h_data_eq]
      simp only [EntityData.asPartial, PartialEntityData.tags]
      constructor
      rfl
  | none =>
    -- Case: entity doesn't exist in es
    have h_simplified : (uid', PartialEntityData.absent) = (uid, data₂) := by
      rw [h_case] at h_eq
      exact h_eq
    have h_uid_eq : uid = uid' := by
      injection h_simplified with h_uid_eq _
      exact h_uid_eq.symm
    have h_data_eq : data₂ = PartialEntityData.absent := by
      injection h_simplified with _ h_data_eq
      exact h_data_eq.symm
    left
    constructor
    · exact h_data_eq
    · rw [h_uid_eq]
      exact h_case

-- Helper lemma for map append refinement
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
  RequestAndEntitiesRefine req es (Request.asPartialRequest req) (Entities.asPartial es) := by
  constructor
  · exact as_partial_request_refines
  · unfold EntitiesRefine Entities.asPartial
    intro uid data₂ h_find
    have h_mapOnValues := Map.find?_mapOnValues_some' EntityData.asPartial h_find
    obtain ⟨data₁, h_find₁, h_eq⟩ := h_mapOnValues
    right
    exists data₁
    exact ⟨h_find₁,
           by rw [h_eq]; apply PartialIsValid.some; rfl,
           by rw [h_eq]; apply PartialIsValid.some; rfl,
           by rw [h_eq]; apply PartialIsValid.some; rfl⟩




theorem batched_eval_loop_eq_evaluate
  {x : Residual}
  {req : Request}
  (es : Entities)
  {current_store : PartialEntities}
  {env : TypeEnv} :
  let loader := entityLoaderFor es
  Residual.WellTyped env x →
  RequestAndEntitiesRefine req es req.asPartialRequest current_store →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvalLoop x req loader current_store iters) req es).toOption = (Residual.evaluate x req es).toOption := by
  simp only
  intro h₁ h₂ h₃
  unfold batchedEvalLoop
  split
  case h_1 => simp only
  case h_2 iters n=>
    let toLoad := (Set.filter (fun uid => (Map.find? current_store uid).isNone) x.allLiteralUIDs)
    let newStore := entityLoaderFor es toLoad ++ current_store
    have h₄ : RequestAndEntitiesRefine req es req.asPartialRequest newStore := by
      unfold RequestAndEntitiesRefine
      constructor
      · exact as_partial_request_refines
      · apply entities_refine_append
        · unfold RequestAndEntitiesRefine at h₂
          exact h₂.right
        · exact entityLoaderFor_refines es toLoad
    let newRes := TPE.evaluate x req.asPartialRequest newStore
    have h₅ : (Residual.evaluate newRes req es).toOption = (Residual.evaluate x req es).toOption := by
      subst newRes
      rw [← partial_evaluate_is_sound h₁ h₃ h₄]

    simp only
    split
    case h_1 h₆ =>
      rw [← h₆]
      subst toLoad newStore newRes
      exact h₅
    case h_2 =>
      subst toLoad newStore newRes
      rw [batched_eval_loop_eq_evaluate]
      . exact h₅
      . exact env
      . apply partial_eval_preserves_well_typed h₃ h₄ h₁
      . exact h₄
      . exact h₃




/--
The main correctness theorem for batched evaluation:
Batched evaluation with an entity loader produces the same result
as normal evaluation with the complete entity store.
-/
theorem batched_eval_eq_evaluate
  {x : TypedExpr}
  {req : Request}
  {es : Entities}
  {env : TypeEnv} :
  let loader := entityLoaderFor es
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluate x req loader iters) req es).toOption = (evaluate x.toExpr req es).toOption := by
  simp only [batchedEvaluate]
  intro h₁ h₂
  have h₃ := (direct_request_and_entities_refine req es)

  let first_partial := (TPE.evaluate (TypedExpr.toResidual x) (Request.asPartialRequest req) (Entities.asPartial (Data.Map.mk [])))
  let h₅ : Residual.WellTyped env (TypedExpr.toResidual x) := by {
    apply conversion_preserves_typedness
    exact h₁
  }
  have conversion_sound := conversion_preserves_evaluation x req es
  rw [conversion_sound]
  have partial_sound := partial_evaluate_is_sound h₅ h₂ h₃
  rw [partial_sound]

  have h₆ : Residual.WellTyped env (TPE.evaluate x.toResidual req.asPartialRequest Map.empty) := by
    apply partial_eval_preserves_well_typed h₂
    . unfold RequestAndEntitiesRefine
      constructor
      . apply as_partial_request_refines
      . apply any_refines_empty_entities
    . exact h₅
  have h₇: RequestAndEntitiesRefine req es req.asPartialRequest Map.empty := by
    constructor
    . apply as_partial_request_refines
    . apply any_refines_empty_entities

  rw [batched_eval_loop_eq_evaluate es h₆ h₇ h₂]
  rw [←partial_evaluate_is_sound h₅ h₂ h₇]
  rw [←partial_evaluate_is_sound h₅ h₂ h₃]

end Cedar.Thm
