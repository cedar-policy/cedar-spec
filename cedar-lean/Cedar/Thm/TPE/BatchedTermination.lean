

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


theorem PE_size_decreases_or_returns_same (r rq es)  :
  (TPE.evaluate r rq es).treeSize < r.treeSize ∨
  (TPE.evaluate r rq es) = r
:= by
  sorry

theorem anyM_none_implies_exists_none {α} {f} {ls: List α}:
  ls.anyM f = none → ∃ e, e ∈ ls ∧ (f e) = none
:= by
  intro h
  cases ls
  case nil =>
    simp at h
  case cons hd tl =>
    simp at h
    rcases h with ⟨h₁, h₂⟩
    cases h₃: f hd
    case intro.none =>
      exists hd
      simp
      exact h₃
    case intro.some v =>
      cases v
      case false =>
        specialize h₁ h₃
        have ⟨e, ih₁, ih₂⟩ := anyM_none_implies_exists_none h₁
        exists e
        simp
        constructor
        . right
          assumption
        . assumption
      case true =>
        rw [h₃] at h₂
        contradiction



theorem binaryApp_termination_mem {vs uid} {a b ty} {store: PartialEntities} {req: Request} {loader: EntityLoader} :
  let newStore :=
    (Map.mapOnValues EntityDataOption.asPartial
      (loader
        (Set.filter (fun uid => (Map.find? store uid).isNone)
          (Residual.binaryApp BinaryOp.mem a b ty).allLiteralUIDs)) ++
          store)
  (TPE.evaluate a req.asPartialRequest newStore).asValue =
    some (Value.prim (Prim.entityUID uid)) →
  (TPE.evaluate b req.asPartialRequest newStore).asValue =
    some (Value.set vs) →
  TPE.inₛ uid vs newStore = none →
  (Residual.binaryApp BinaryOp.mem
      (TPE.evaluate a req.asPartialRequest
        newStore)
      (TPE.evaluate b req.asPartialRequest
        newStore)
      ty).treeSize <
  2 + a.treeSize + b.treeSize
:= by
  intro newStore h₁ h₂ h₃
  have h₄ := PE_size_decreases_or_returns_same a req.asPartialRequest newStore
  have h₅ := PE_size_decreases_or_returns_same b req.asPartialRequest newStore
  cases h₄
  case inl h₃ =>
    sorry
  case inr h₄ =>
    cases h₅
    case inl h₅ =>
      sorry
    case inr h₅ =>
      -- here we have a contradiction using h₁ and h₂
      rw [h₄] at h₁
      rw [h₄, h₅]
      clear h₄ h₅
      unfold TPE.inₛ at h₃
      cases h₄: List.mapM (Except.toOption ∘ Value.asEntityUID) vs.toList
      case none =>
        -- TODO need well typedness to say they are all uids
        sorry
      case some ls =>
        rw [h₄] at h₃
        clear h₄
        simp [TPE.inₑ] at h₃
        replace h₃ := anyM_none_implies_exists_none h₃
        rcases h₃ with ⟨e, h₃, h₄⟩
        split at h₄
        . contradiction
        . simp [PartialEntities.ancestors, PartialEntities.get] at h₄
          have ⟨e, h₅⟩: ∃e, newStore.find? uid = some e := by
            sorry
          specialize h₄ e h₅
          rw [← Map.list_find?_some_iff_map_find?_some] at h₅
          rw [← Map.kvs] at h₅
          simp [HAppend.hAppend] at h₅
          -- TODO need invariant that store contains full entities

          --replace h₅ := Map.in_mapOnValues_in_kvs' h₅
          sorry




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
  have newStore := (Map.mapOnValues EntityDataOption.asPartial
      (loader
        (Set.filter (fun uid => (Map.find? store uid).isNone) (Residual.binaryApp op a b ty).allLiteralUIDs)) ++
    store)

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
    case h_1 r₂ a_some h₂ =>
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
          simp [Option.bind] at h₃
          split at h₃
          case h_2 h₃ =>
            simp at h₃
          case h_1 h₃ h₄ =>
            simp [apply₂.self]

            exact binaryApp_termination_mem a_some h₂ h₄
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
