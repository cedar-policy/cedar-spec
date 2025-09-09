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
       EntitiesRefine store ((loader s).mapOnValues EntityDataOption.asPartial)

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
  · apply PartialIsValid.some
    rfl

theorem any_refines_empty_entities :
  EntitiesRefine es Data.Map.empty := by
  simp only [EntitiesRefine, Data.Map.empty, Data.Map.find?, Map.kvs]
  intro a e₂ h₁
  contradiction

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
  RequestAndEntitiesRefine req es req.asPartialRequest es.asPartial := by
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
  EntityLoader.WellBehaved es loader →
  Residual.WellTyped env x →
  RequestAndEntitiesRefine req es req.asPartialRequest current_store →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvalLoop x req loader current_store iters) req es).toOption = (Residual.evaluate x req es).toOption := by
  intro h₀ h₁ h₂ h₃
  unfold batchedEvalLoop
  split
  case h_1 => simp only
  case h_2 iters n=>
    let toLoad := (Set.filter (fun uid => (Map.find? current_store uid).isNone) x.allLiteralUIDs)
    let newEntities := ((loader toLoad).mapOnValues EntityDataOption.asPartial)
    let newStore := newEntities ++ current_store

    have h₀₂ := h₀
    specialize h₀₂ toLoad
    obtain ⟨h₄, h₅⟩ := h₀₂

    have h₆ : RequestAndEntitiesRefine req es req.asPartialRequest newStore := by
      unfold RequestAndEntitiesRefine
      constructor
      · exact as_partial_request_refines
      · apply entities_refine_append
        · unfold RequestAndEntitiesRefine at h₂
          exact h₂.right
        · apply h₅
    let newRes := TPE.evaluate x req.asPartialRequest newStore
    have h₇ : (Residual.evaluate newRes req es).toOption = (Residual.evaluate x req es).toOption := by
      subst newRes
      rw [← partial_evaluate_is_sound h₁ h₃ h₆]

    simp only
    split
    case h_1 h₆ =>
      rw [← h₆]
      subst toLoad newStore newRes
      exact h₇
    case h_2 =>
      subst toLoad newStore newRes
      have h₈ := (partial_eval_preserves_well_typed h₃ h₆ h₁)

      rw [batched_eval_loop_eq_evaluate es h₀ h₈ h₆ h₃]
      exact h₇

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
  EntityLoader.WellBehaved es loader →
  TypedExpr.WellTyped env x →
  InstanceOfWellFormedEnvironment req es env →
  (Residual.evaluate (batchedEvaluate x req loader iters) req es).toOption = (evaluate x.toExpr req es).toOption := by
  simp only [batchedEvaluate]
  intro h₁ h₂ h₃
  have h₄ := (direct_request_and_entities_refine req es)

  let first_partial := (TPE.evaluate x.toResidual req.asPartialRequest (Entities.asPartial (Data.Map.mk [])))
  let h₅ : Residual.WellTyped env (TypedExpr.toResidual x) := by {
    apply conversion_preserves_typedness
    exact h₂
  }
  rw [conversion_preserves_evaluation x req es]
  rw [partial_evaluate_is_sound h₅ h₃ h₄]

  have h₆ : Residual.WellTyped env (TPE.evaluate x.toResidual req.asPartialRequest Map.empty) := by
    apply partial_eval_preserves_well_typed h₃ _ h₅
    . unfold RequestAndEntitiesRefine
      constructor
      . apply as_partial_request_refines
      . apply any_refines_empty_entities
  have h₇: RequestAndEntitiesRefine req es req.asPartialRequest Map.empty := by
    constructor
    . apply as_partial_request_refines
    . apply any_refines_empty_entities

  rw [batched_eval_loop_eq_evaluate es h₁ h₆ h₇ h₃]
  rw [←partial_evaluate_is_sound h₅ h₃ h₇]
  rw [←partial_evaluate_is_sound h₅ h₃ h₄]

end Cedar.Thm
