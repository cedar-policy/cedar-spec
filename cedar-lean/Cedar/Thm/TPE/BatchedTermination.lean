

import Cedar.TPE.BatchedEvaluator
import Cedar.Thm.TPE.BatchedEvaluator
import Cedar.Data.SizeOf

namespace Cedar.Thm.TPE

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Data


theorem tpe_not_value_implies_input_not_value:
  (TPE.evaluate expr req store).asValue = none
  → expr.asValue = none := by
  intro h
  by_contra h_contra
  cases expr with
  | val v ty =>
    simp [TPE.evaluate] at h
    simp [Residual.asValue] at h
  | var v ty =>
    simp [Residual.asValue] at h_contra
  | error ty =>
    simp [Residual.asValue] at h_contra
  | ite cond thenExpr elseExpr ty =>
    simp [Residual.asValue] at h_contra
  | and a b ty =>
    simp [Residual.asValue] at h_contra
  | or a b ty =>
    simp [Residual.asValue] at h_contra
  | unaryApp op expr ty =>
    simp [Residual.asValue] at h_contra
  | binaryApp op a b ty =>
    simp [Residual.asValue] at h_contra
  | getAttr expr attr ty =>
    simp [Residual.asValue] at h_contra
  | hasAttr expr attr ty =>
    simp [Residual.asValue] at h_contra
  | set ls ty =>
    simp [Residual.asValue] at h_contra
  | record map ty =>
    simp [Residual.asValue] at h_contra
  | call xfn args ty =>
    simp [Residual.asValue] at h_contra

theorem tree_size_gt_0 (r: Residual) :
  r.treeSize > 0
:= by
  unfold Residual.treeSize
  split <;> omega

/--
Theorem for unaryApp case: If the child expression evaluates to a smaller size
or produces a value, then the unaryApp either produces a value or has smaller size.
Includes inductive hypothesis about child expr size decreasing.
-/
theorem unaryApp_termination
  (op : UnaryOp)
  (expr : Residual)
  (ty : CedarType)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  (ih :
    expr.asValue = Option.none →
    (batchedEvalLoop expr req loader store 1).treeSize < expr.treeSize) :
  (batchedEvalLoop (Residual.unaryApp op expr ty) req loader store 1).treeSize < (Residual.unaryApp op expr ty).treeSize := by
  unfold batchedEvalLoop
  simp only
  split
  -- expr is a value
  case h_1 x v ty₂ h₁ =>
    -- todo val bigger than expr
    simp [Residual.treeSize]
    have h := tree_size_gt_0 expr
    omega
  case h_2 r₁ h₁ =>
    simp [TPE.evaluate, TPE.apply₁]
    split
    case h_1 r₂ ty₂ h₂ =>
      simp [batchedEvalLoop]
      simp [Residual.treeSize]
      apply tree_size_gt_0
    case h_2 r₂ h₂ =>
      split
      case h_1 =>
        simp [batchedEvalLoop]
        simp [Spec.apply₁]
        split
        any_goals
          simp [someOrError, Except.toOption, Residual.treeSize]
          try omega
        case h_2 =>
          split
          all_goals
            simp [Residual.treeSize]
            have h := tree_size_gt_0 expr
            omega
        all_goals
          apply tree_size_gt_0

      case h_2 h₃ =>
        simp [batchedEvalLoop]
        have h₄ := tpe_not_value_implies_input_not_value h₃
        specialize ih h₄
        simp [batchedEvalLoop] at ih
        split at ih
        case h_1 h₅ =>
          simp [Residual.allLiteralUIDs] at h₃
          rw [h₅] at h₃
          contradiction
        case h_2 =>
          simp [Residual.allLiteralUIDs]
          simp [Residual.treeSize]
          exact ih

/--
Theorem for binaryApp case: If the child expressions evaluate to smaller sizes
or produce values, then the binaryApp either produces a value or has smaller size.
Includes inductive hypotheses about child expr sizes decreasing.
-/
theorem binaryApp_termination
  (op : BinaryOp)
  (a b : Residual)
  (ty : CedarType)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities)
  (ih₁ :
    a.asValue = Option.none →
    (batchedEvalLoop a req loader store 1).treeSize < a.treeSize)
  (ih₂ :
    b.asValue = Option.none →
    (batchedEvalLoop b req loader store 1).treeSize < b.treeSize) :
  (batchedEvalLoop (Residual.binaryApp op a b ty) req loader store 1).treeSize < (Residual.binaryApp op a b ty).treeSize := by
  unfold batchedEvalLoop
  simp only
  split
  -- Case 1: The binaryApp evaluates to a value immediately
  case h_1 x v ty₂ h₁ =>
    -- When evaluation produces a value, the result has size 1, which is less than 2 + a.treeSize + b.treeSize
    simp [Residual.treeSize]
    have h_a := tree_size_gt_0 a
    have h_b := tree_size_gt_0 b
    omega
  case h_2 r₁ h₁ =>
    simp [TPE.evaluate, TPE.apply₂]
    split
    case h_1 r₂ ty₂ h₂ =>
      simp [batchedEvalLoop]
      simp [Residual.treeSize]
      split
      any_goals
        try simp [someOrError]
        have h₃ := tree_size_gt_0 a
        have h₄ := tree_size_gt_0 b
        try split
      any_goals
        simp [Residual.treeSize]
        try omega
      case h_15 =>
        simp [someOrSelf]
        split
        . simp [Residual.treeSize]
          have h₃ := tree_size_gt_0 a
          have h₄ := tree_size_gt_0 b
          omega
        case h_2 h₃ =>
          simp [apply₂.self, Residual.treeSize]
          -- contradicton: we got none for values that we should have loaded
          sorry
      case h_14 h₃ =>
        sorry
      case h_16 h₃ =>
        sorry
      case h_17 h₃ =>
        simp [TPE.getTag]
        sorry
    case h_2 r₂ h₂ =>
      simp [batchedEvalLoop]
      split
      case h_1 =>
        simp [Residual.treeSize]
        have h_a := tree_size_gt_0 a
        have h_b := tree_size_gt_0 b
        omega
      case h_2 h₃ =>
        simp [Residual.treeSize]
        have h_a := tree_size_gt_0 a
        have h_b := tree_size_gt_0 b
        omega
      case h_3 =>
        simp [apply₂.self]
        simp [Residual.treeSize]
        simp at h₂
        sorry


/--
The main theorem for termination of batched
evaluation-
After one iteration of batched evaluation loop on a residual
which is not a value, either we get a value or the size decreases.
-/
theorem batched_eval_loop_decreases_size
  (residual : Residual)
  (req : Request)
  (loader : EntityLoader)
  (store : PartialEntities):
  residual.asValue = Option.none →
  (batchedEvalLoop residual req loader store 1).treeSize < residual.treeSize
  := by
  -- The batched evaluation loop loads new entities and evaluates
  let toLoad := residual.allLiteralUIDs.filter (λ uid => (store.find? uid).isNone)
  let newEntities := ((loader toLoad).mapOnValues EntityDataOption.asPartial)
  let newStore := newEntities ++ store
  intro h₁

  -- Case analysis on the residual structure
  cases residual with
  | val v ty =>
    sorry
  | error ty =>
    sorry
  | var v ty =>
    sorry
  | ite cond thenExpr elseExpr ty =>
    sorry
  | and a b ty =>
    sorry
  | or a b ty =>
    sorry
  | unaryApp op expr ty =>
    have ih := batched_eval_loop_decreases_size expr req loader store
    apply unaryApp_termination op expr ty req loader store ih
  | binaryApp op a b ty =>
    have ih_a := batched_eval_loop_decreases_size a req loader store
    have ih_b := batched_eval_loop_decreases_size b req loader store
    apply binaryApp_termination op a b ty req loader store ih_a ih_b
  | getAttr expr attr ty =>
    sorry
  | hasAttr expr attr ty =>
    sorry
  | set ls ty =>
    sorry
  | record map ty =>
    sorry
  | call xfn args ty =>
    sorry

end Cedar.Thm.TPE
