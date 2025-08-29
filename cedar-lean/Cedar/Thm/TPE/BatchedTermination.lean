

import Cedar.TPE.BatchedEvaluator
import Cedar.Thm.TPE.BatchedEvaluator
import Cedar.Data.SizeOf

namespace Cedar.Thm.TPE

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

-- Helper theorem: TPE evaluation doesn't increase size
theorem tpe_evaluate_size_le (r : Residual) (req : PartialRequest) (es : PartialEntities) :
  sizeOf (Cedar.TPE.evaluate r req es) ≤ sizeOf r := by
  sorry

-- Helper theorem: If TPE evaluation produces a different result, size decreases
theorem tpe_evaluate_progress (r : Residual) (req : PartialRequest) (es : PartialEntities) :
  let result := Cedar.TPE.evaluate r req es
  result ≠ r → sizeOf result < sizeOf r := by
  sorry

-- Theorem for unaryApp case in batched evaluation
theorem batched_eval_unaryApp_case
  (op : UnaryOp)
  (expr : Residual)
  (ty : CedarType)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  (ih : expr.asValue.isNone →
    let result := batchedEvalLoop expr req loader store 1
    result.asValue.isSome ∨ sizeOf result < sizeOf expr) :
  let residual := Residual.unaryApp op expr ty
  let result := batchedEvalLoop residual req loader store 1
  result.asValue.isSome ∨ sizeOf result < sizeOf residual := by
  simp only [batchedEvalLoop]

  -- Case analysis on whether the child expression is a value
  cases h : expr.asValue with
  | none =>
    -- Case: child is not a value
    -- Apply inductive hypothesis
    have h_isNone : expr.asValue.isNone = true := by simp [Option.isNone, h]
    have ih_result := ih h_isNone
    -- The batched evaluation will first evaluate the child expression
    -- Since the child is not a value, by IH either we get a value or size decreases
    cases ih_result with
    | inl h_val =>
      right
      simp [batchedEvalLoop]
      apply tpe_evaluate_size_le
    | inr h_size =>
      right
      simp [batchedEvalLoop]
      apply tpe_evaluate_size_le
  | some val =>
    -- Case: child is already a value
    -- We can directly apply the unary operation
    sorry

/--
The main theorem for termination of batched
evaluation-
After one iteration of batched evaluation loop on a residual
which is not a value, either we get a value or the size decreases.
-/
theorem batched_eval_loop_decreases_size_or_unchanged
  (residual : Residual)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  (h_not_val : residual.asValue.isNone) :
  let result := batchedEvalLoop residual req loader store 1
  result.asValue.isSome ∨ sizeOf result < sizeOf residual
  := by
  simp only

  -- The batched evaluation loop loads new entities and evaluates
  let toLoad := residual.allLiteralUIDs.filter (λ uid => (store.find? uid).isNone)
  let newEntities := ((loader toLoad).mapOnValues EntityDataOption.asPartial)
  let newStore := newEntities ++ store

  -- Case analysis on the residual structure
  cases residual with
  | val v ty =>
    -- This contradicts h_not_val
    simp [Residual.asValue] at h_not_val
  | error ty =>
    sorry
  | var v ty =>
    simp [Cedar.TPE.evaluate, Cedar.TPE.varₚ]
    cases v with
    | principal =>
      -- Principal variable
      cases h_prin : req.asPartialRequest.principal.asEntityUID with
      | some uid =>
        simp [batchedEvalLoop, Cedar.TPE.someOrSelf]
        left
        simp [Residual.asValue]
        sorry
      | none =>
        -- should not happen, prove contradiction
        sorry
    | resource =>
      -- Resource variable
      simp [Cedar.TPE.someOrSelf]
      cases h_res : req.asPartialRequest.resource.asEntityUID with
      | some uid =>
        simp [batchedEvalLoop, Cedar.TPE.someOrSelf]
        left
        simp [Residual.asValue]
        sorry
      | none =>
        sorry
    | action =>
      simp [Cedar.TPE.someOrSelf]
      left
      simp [Residual.asValue]
      sorry
    | context =>
      simp [Cedar.TPE.someOrSelf]
      cases h_ctx : req.asPartialRequest.context with
      | some ctx =>
        simp [batchedEvalLoop, Cedar.TPE.someOrSelf]
        sorry
      | none =>
        sorry
  | ite cond thenExpr elseExpr ty =>
    simp [Cedar.TPE.evaluate]
    sorry
  | and a b ty =>
    simp [Cedar.TPE.evaluate, Cedar.TPE.and]
    sorry
  | or a b ty =>
    simp [Cedar.TPE.evaluate]
    sorry
  | unaryApp op expr ty =>
    sorry
  | binaryApp op a b ty =>
    simp [Cedar.TPE.evaluate]
    sorry
  | getAttr expr attr ty =>
    simp [Cedar.TPE.evaluate]
    sorry
  | hasAttr expr attr ty =>
    simp [Cedar.TPE.evaluate]
    sorry
  | set ls ty =>
    simp [Cedar.TPE.evaluate]
    sorry
  | record map ty =>
    simp [Cedar.TPE.evaluate]
    sorry
  | call xfn args ty =>
    simp [Cedar.TPE.evaluate]
    sorry

end Cedar.Thm.TPE
