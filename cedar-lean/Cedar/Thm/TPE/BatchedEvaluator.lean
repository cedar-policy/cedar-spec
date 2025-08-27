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


theorem as_partial_request_refines
  {req: Request}
  : RequestRefines req (Request.asPartialRequest req)
  := by
  dsimp [RequestRefines, Request.asPartialRequest]
  constructor
  . simp [PartialEntityUID.asEntityUID]
    apply PartialIsValid.some
    simp
  . constructor
    simp
    constructor
    all_goals {
      dsimp [PartialEntityUID.asEntityUID]
      apply PartialIsValid.some
      simp
    }

theorem any_refines_empty_entities:
  EntitiesRefine es Data.Map.empty
:= by
  simp [EntitiesRefine]
  intro a e₂ h₁
  simp [Data.Map.empty, Data.Map.find?, Map.kvs] at h₁

-- Helper lemma for entityLoaderFor refinement
theorem entityLoaderFor_refines (es : Entities) (toLoad : Set EntityUID) :
  EntitiesRefine es (entityLoaderFor es toLoad) := by
  sorry

-- Helper lemma for map append refinement
theorem entities_refine_append (es : Entities) (m1 m2 : PartialEntities) :
  EntitiesRefine es m1 → EntitiesRefine es m2 → EntitiesRefine es (m2 ++ m1) := by
  intro h1 h2
  unfold EntitiesRefine
  intro a e₂ h_find
  -- We know that (m2 ++ m1).find? a = some e₂
  -- The append operation is defined as Map.make (m2.kvs ++ m1.kvs)
  -- We need to show that either m1 or m2 refines es for this key-value pair

  -- The key insight is that we can use the existing lemmas about map append
  -- Let's check if the key exists in m2 first
  cases h_case : m2.find? a with
  | some e₂' =>
    -- If m2 contains the key, then by the properties of map append,
    -- the result should come from m2 (since m2 comes first in the append)
    have h_eq : e₂ = e₂' := by
      sorry
    rw [h_eq]
    exact h2 a e₂' h_case
  | none =>
    -- If m2 doesn't contain the key, then the result must come from m1
    have h_find1 : m1.find? a = some e₂ := by
      sorry
    exact h1 a e₂ h_find1


theorem direct_request_and_entities_refine
  (req : Request)
  (es : Entities) :
  RequestAndEntitiesRefine req es (Request.asPartialRequest req) (Entities.asPartial es) := by
  unfold RequestAndEntitiesRefine
  constructor
  · -- Prove RequestRefines req (Request.asPartialRequest req)
    exact as_partial_request_refines
  · -- Prove EntitiesRefine es (Entities.asPartial es)
    unfold EntitiesRefine Entities.asPartial
    intro uid data₂ h_find
    -- data₂ comes from (es.mapOnValues EntityData.asPartial)
    have h_mapOnValues := Map.find?_mapOnValues_some' EntityData.asPartial h_find
    obtain ⟨data₁, h_find₁, h_eq⟩ := h_mapOnValues
    right
    exists data₁
    constructor
    · exact h_find₁
    constructor
    · -- attrs refine
      rw [h_eq]
      simp [EntityData.asPartial, PartialEntityData.attrs]
      apply PartialIsValid.some
      rfl
    constructor
    · -- ancestors refine
      rw [h_eq]
      simp [EntityData.asPartial, PartialEntityData.ancestors]
      apply PartialIsValid.some
      rfl
    · -- tags refine
      rw [h_eq]
      simp [EntityData.asPartial, PartialEntityData.tags]
      apply PartialIsValid.some
      rfl




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
  simp
  intro h₁ h₂ h₃
  unfold batchedEvalLoop
  split
  case h_1 => simp
  case h_2 iters n=>
    let toLoad := (Set.filter (fun uid => (Map.find? current_store uid).isNone) x.allLiteralUIDs)
    let newStore := entityLoaderFor es toLoad ++ current_store
    have h₄ : RequestAndEntitiesRefine req es req.asPartialRequest newStore := by
      unfold RequestAndEntitiesRefine
      constructor
      · -- RequestRefines part is the same
        exact as_partial_request_refines
      · -- EntitiesRefine es newStore
        -- Use the helper lemmas
        apply entities_refine_append
        · -- current_store refines es
          unfold RequestAndEntitiesRefine at h₂
          exact h₂.right
        · -- entityLoaderFor es toLoad refines es
          exact entityLoaderFor_refines es toLoad
    let newRes := TPE.evaluate x req.asPartialRequest newStore
    have h₅ : (Residual.evaluate newRes req es).toOption = (Residual.evaluate x req es).toOption := by
      subst newRes
      rw [← partial_evaluate_is_sound h₁ h₃ h₄]

    simp
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
  simp [batchedEvaluate]
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
  rw [batched_eval_loop_eq_evaluate]
  rw [←partial_evaluate_is_sound]
  rw [←partial_evaluate_is_sound]
  exact h₅
  exact h₂
  exact h₃
  exact h₅
  exact h₂
  unfold RequestAndEntitiesRefine
  constructor
  . apply as_partial_request_refines
  . unfold EntitiesRefine
    intro uid
    intro pd
    dsimp [Data.Map.find?, Data.Map.kvs]
    intro h_contra
    contradiction
  . exact env
  case a =>
   apply partial_eval_preserves_well_typed h₂
   . unfold RequestAndEntitiesRefine
     constructor
     . apply as_partial_request_refines
     . apply any_refines_empty_entities
   . exact h₅
  . unfold RequestAndEntitiesRefine
    constructor
    . apply as_partial_request_refines
    . apply any_refines_empty_entities
  . exact h₂

end Cedar.Thm
