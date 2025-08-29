import Cedar.TPE.BatchedEvaluator
import Cedar.Thm.TPE.BatchedEvaluator
import Cedar.Data.SizeOf
import Cedar.Thm.TPE.BatchedWellTyped

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
  (store : EntitiesWithMissing)
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


theorem residual_asValue_some_value {r: Residual}:
  r.asValue = Option.some v →
  ∃ty, r = Residual.val v ty
:= by
  intro h
  cases r with
  | val v' ty =>
    simp only [Residual.asValue] at h
    have h_eq : v' = v := Option.some.inj h
    subst h_eq
    exact ⟨ty, rfl⟩
  | _ =>
    simp [Residual.asValue] at h


theorem find_entity_in_batched_new_store {store: EntitiesWithMissing}:
  EntityLoader.WellBehaved env loader →
  uid ∈ l →
  ∃ e, (loader (Set.mk (List.filter (fun uid => (Map.find? store uid).isNone) l)) ++ store).find? uid = some e
:= by
  intro h_wb inl
  rw [Map.find?_append]
  cases h_case : Map.find? store uid
  case none =>
    -- uid is not in store, so it should be in the filtered list and loaded by loader
    -- Since uid ∈ l and uid is not in store, uid should be in the filtered list
    have uid_in_filtered : uid ∈ List.filter (fun uid => (Map.find? store uid).isNone) l := by
      rw [List.mem_filter]
      constructor
      · exact inl
      · rw [h_case]
        simp

    -- Convert to set membership
    have uid_in_set : uid ∈ Set.mk (List.filter (fun uid => (Map.find? store uid).isNone) l) := by
      simp [Membership.mem, Set.elts]
      exact uid_in_filtered

    -- Use EntityLoader.WellBehaved property
    simp [EntityLoader.WellBehaved] at h_wb
    specialize h_wb (Set.mk (List.filter (fun uid => (Map.find? store uid).isNone) l))
    rcases h_wb with ⟨h_subset, _⟩

    -- uid is in the keys of the loaded map
    have uid_in_keys : uid ∈ (loader (Set.mk (List.filter (fun uid => (Map.find? store uid).isNone) l))).keys := by
      rw [Set.subset_def] at h_subset
      apply h_subset
      exact uid_in_set

    replace uid_in_keys : uid ∈ (loader (Set.mk (List.filter (fun uid => (Map.find? store uid).isNone) l))) := by
      simp [Membership.mem]
      simp [Membership.mem] at uid_in_keys
      exact uid_in_keys
    -- If uid is in keys, then find? returns some value
    rw [Map.in_keys_iff_find?_some] at uid_in_keys
    rcases uid_in_keys with ⟨v, hv⟩
    exists v
    simp only [Option.or, h_case, Option.none_or]
    rw [hv]
  case some e =>
    cases (Map.find? (loader (Set.mk (List.filter (fun uid => (Map.find? store uid).isNone) l))) uid)
    all_goals
      simp

theorem binaryApp_termination_memₛ {vs uid} {a b ty} {store: EntitiesWithMissing} {req: Request} {loader: EntityLoader} :
  let newStore: EntitiesWithMissing :=
    (loader
          (Set.filter (fun uid => (Map.find? store uid).isNone)
            (Residual.binaryApp BinaryOp.mem a b ty).allLiteralUIDs) ++
        store)
  let newA := (TPE.evaluate a req.asPartialRequest newStore.asPartial)
  let newB := (TPE.evaluate b req.asPartialRequest newStore.asPartial)
  EntityLoader.WellBehaved es loader →
  newA.asValue = some (Value.prim (Prim.entityUID uid)) →
  newB.asValue = some (Value.set vs) →
  TPE.inₛ uid vs newStore.asPartial = none →
  Residual.WellTyped env
    (Residual.binaryApp BinaryOp.mem newA newB ty) →
  (Residual.binaryApp BinaryOp.mem newA newB ty).treeSize <
    2 + a.treeSize + b.treeSize
:= by
  intro newStore newA newB h_wb h₁ h₂ h₃ h_wt
  subst newA
  subst newB
  have h₄ := PE_size_decreases_or_returns_same a req.asPartialRequest newStore.asPartial
  have h₅ := PE_size_decreases_or_returns_same b req.asPartialRequest newStore.asPartial
  cases h₄
  case inl h₃ =>
    simp [Residual.treeSize]
    cases h₅
    . omega
    case inr h₄ =>
      rw [h₄]
      omega
  case inr h₄ =>
    cases h₅
    case inl h₅ =>
      rw [h₄]
      simp [Residual.treeSize]
      omega
    case inr h₅ =>
      -- here we have a contradiction using h₁ and h₂
      rw [h₄] at h₁
      rw [h₄, h₅]
      rw [h₄, h₅] at h_wt
      rw [h₅] at h₂

      clear h₄ h₅
      unfold TPE.inₛ at h₃
      cases h₄: List.mapM (Except.toOption ∘ Value.asEntityUID) vs.toList
      case none =>
        clear h₃
        cases h_wt; rename_i h_wt₁ h_wt₂ h_wt₃
        cases h_wt₃ <;> rename_i h_wt₄ h_wt₅
        case binaryApp.memₑ =>
          -- contradiction: we got a set not an entity
          simp [Residual.asValue] at h₂
          split at h₂
          case h_2 => contradiction
          case h_1 r₂ v₂ ty₂ =>
            injection h₂; rename_i h₂
            subst h₂
            simp [Residual.typeOf] at h_wt₅
            cases h_wt₂
            rename_i h_wt₂
            rw [h_wt₅] at h_wt₂
            cases h_wt₂

        case binaryApp.memₛ ety₁ ety₂ =>
        simp [Residual.asValue] at h₂
        split at h₂
        case h_2 => contradiction
        case h_1 r₂ v₂ ty =>
        injection h₂; rename_i h₂
        subst h₂
        cases h_wt₂; rename_i h_wt₂
        cases h_wt₂; rename_i ty₂ h_wt₂
        simp [Residual.typeOf] at h_wt₅

        subst h_wt₅
        replace ⟨v, h₄, h₅⟩ := List.mapM_none_iff_exists_none.mp h₄
        specialize h_wt₂ v h₄
        cases h_wt₂
        simp [Value.asEntityUID, Except.toOption] at h₅
      case some ls =>
        rw [h₄] at h₃
        clear h₄
        simp [TPE.inₑ] at h₃
        replace h₃ := anyM_none_implies_exists_none h₃
        rcases h₃ with ⟨e, h₃, h₄⟩
        split at h₄
        . contradiction
        . rename_i h₅
          simp [PartialEntities.ancestors, PartialEntities.get] at h₄


          replace ⟨ty₂, h₁⟩ := residual_asValue_some_value h₁
          subst h₁
          replace ⟨ty₃, h₂⟩ := residual_asValue_some_value h₂
          subst h₂

          -- can find an entity e for uid from a
          have ⟨e, h₆⟩: ∃e, newStore.find? uid = some e := by
            subst newStore
            simp [Residual.allLiteralUIDs, Set.filter, Set.singleton, Set.elts, Union.union, Set.union, Set.make, List.canonicalize, Set.empty, List.insertCanonical, List.filter]
            split
            case h_1 b h₆ =>
              -- TODO
              simp [EntityLoader.WellBehaved] at h_wb
              specialize h_wb (Set.mk [uid])
              rcases h_wb with ⟨h_wb₁, h_wb₂⟩
              rw [← Option.isSome_iff_exists]
              rw [Map.find?_append]
              simp [Option.or]
              rw [Option.isSome_iff_exists]
              -- Since uid ∈ keys of loader map, find? must return some
              have h_in_keys : uid ∈ (loader (Set.mk [uid])) := by
                rw [Set.subset_def] at h_wb₁
                apply h_wb₁
                simp [Membership.mem, Set.elts]
                apply List.Mem.head
              have ⟨v, h₇⟩ := Map.in_keys_iff_find?_some.mp h_in_keys
              rw [h₇]
              exists v
            case h_2 h₅ =>
              rw [Map.find?_append]
              cases (Map.find? (loader (Set.mk [])) uid)
              case none =>
                simp
                simp [Option.isSome] at h₅
                split at h₅
                case h_1 =>
                  rename_i e h₇
                  rw [h₇]
                  exists e
                case h_2 =>
                  contradiction
              case some e =>
                exists e
          have h₇ : newStore.asPartial.find? uid = some e.asPartial := by
            unfold EntitiesWithMissing.asPartial
            exact Map.find?_mapOnValues_some EntityOrMissing.asPartial h₆
          specialize h₄ e.asPartial h₇
          rw [← Map.list_find?_some_iff_map_find?_some] at h₆
          rw [← Map.kvs] at h₆
          simp [HAppend.hAppend] at h₆
          simp [EntityOrMissing.asPartial] at h₄
          split at h₄
          . simp [PartialEntityData.ancestors] at h₄
          . simp [EntityData.asPartial, PartialEntityData.ancestors] at h₄


theorem binaryApp_termination_memₑ {uid2 uid} {a b ty} {store: EntitiesWithMissing} {req: Request} {loader: EntityLoader} :
  let newStore: EntitiesWithMissing :=
    (loader
          (Set.filter (fun uid => (Map.find? store uid).isNone)
            (Residual.binaryApp BinaryOp.mem a b ty).allLiteralUIDs) ++
        store)
  let newA := (TPE.evaluate a req.asPartialRequest newStore.asPartial)
  let newB := (TPE.evaluate b req.asPartialRequest newStore.asPartial)
  EntityLoader.WellBehaved es loader →
  newA.asValue = some (Value.prim (Prim.entityUID uid)) →
  newB.asValue = some (Value.prim (Prim.entityUID uid2)) →
  TPE.inₑ uid uid2 newStore.asPartial = none →
  Residual.WellTyped env
    (Residual.binaryApp BinaryOp.mem newA newB ty) →
  (Residual.binaryApp BinaryOp.mem newA newB ty).treeSize <
    2 + a.treeSize + b.treeSize
:= by
  intro newStore newA newB h_wb h₁ h₂ h₃ h_wt
  subst newA
  subst newB
  have h₄ := PE_size_decreases_or_returns_same a req.asPartialRequest newStore.asPartial
  have h₅ := PE_size_decreases_or_returns_same b req.asPartialRequest newStore.asPartial
  cases h₄
  case inl h₃ =>
    simp [Residual.treeSize]
    cases h₅
    . omega
    case inr h₄ =>
      rw [h₄]
      omega
  case inr h₄ =>
    cases h₅
    case inl h₅ =>
      rw [h₄]
      simp [Residual.treeSize]
      omega
    case inr h₅ =>
      -- here we have a contradiction using h₁ and h₂
      rw [h₄] at h₁
      rw [h₄, h₅]
      rw [h₄, h₅] at h_wt
      rw [h₅] at h₂

      clear h₄ h₅
      unfold TPE.inₑ at h₃
      split at h₃
      case isTrue => contradiction
      -- contradiction: .ancestors was none at h₃
      simp [EntitiesWithMissing.asPartial, PartialEntities.ancestors, PartialEntities.get] at h₃
      replace ⟨ty₂, h₁⟩ := residual_asValue_some_value h₁
      subst h₁
      replace ⟨ty₃, h₂⟩ := residual_asValue_some_value h₂
      subst h₂
      -- can find an entity e for uid from a
      have ⟨e, h₆⟩: ∃e, newStore.find? uid = some e := by
        subst newStore
        simp [Residual.allLiteralUIDs, Set.filter, Set.singleton, Set.elts, Union.union, Set.union, Set.make, List.canonicalize, List.insertCanonical]
        split
        case isTrue =>
          apply find_entity_in_batched_new_store h_wb
          simp
        case isFalse =>
          split
          case isTrue =>
            apply find_entity_in_batched_new_store h_wb
            simp
          case isFalse =>
            apply find_entity_in_batched_new_store h_wb
            simp

      simp [Residual.treeSize]

      have h₇ := Map.find?_mapOnValues_some EntityOrMissing.asPartial h₆
      specialize h₃ e.asPartial h₇
      simp [EntityOrMissing.asPartial, EntityData.asPartial] at h₃
      split at h₃
      . simp [PartialEntityData.ancestors] at h₃
      . simp [PartialEntityData.ancestors] at h₃

theorem binaryApp_termination_hasTag {uid tag} {a b ty} {store: EntitiesWithMissing} {req: Request} {loader: EntityLoader} :
  let newStore: EntitiesWithMissing :=
    (loader
          (Set.filter (fun uid => (Map.find? store uid).isNone)
            (Residual.binaryApp BinaryOp.hasTag a b ty).allLiteralUIDs) ++
        store)
  let newA := (TPE.evaluate a req.asPartialRequest newStore.asPartial)
  let newB := (TPE.evaluate b req.asPartialRequest newStore.asPartial)
  EntityLoader.WellBehaved es loader →
  newA.asValue = some (Value.prim (Prim.entityUID uid)) →
  newB.asValue = some (Value.prim (Prim.string tag)) →
  TPE.hasTag uid tag newStore.asPartial = none →
  Residual.WellTyped env
    (Residual.binaryApp BinaryOp.hasTag newA newB ty) →
  (Residual.binaryApp BinaryOp.hasTag newA newB ty).treeSize <
    2 + a.treeSize + b.treeSize
:= by
  intro newStore newA newB h_wb h₁ h₂ h₃ h_wt
  subst newA
  subst newB
  have h₄ := PE_size_decreases_or_returns_same a req.asPartialRequest newStore.asPartial
  have h₅ := PE_size_decreases_or_returns_same b req.asPartialRequest newStore.asPartial
  cases h₄
  case inl h₃ =>
    simp [Residual.treeSize]
    cases h₅
    . omega
    case inr h₄ =>
      rw [h₄]
      omega
  case inr h₄ =>
    cases h₅
    case inl h₅ =>
      rw [h₄]
      simp [Residual.treeSize]
      omega
    case inr h₅ =>
      -- here we have a contradiction using h₁ and h₂
      rw [h₄] at h₁
      rw [h₄, h₅]
      rw [h₄, h₅] at h_wt
      rw [h₅] at h₂

      clear h₄ h₅
      unfold TPE.hasTag at h₃
      simp [EntitiesWithMissing.asPartial, PartialEntities.tags] at h₃

      replace ⟨ty₂, h₁⟩ := residual_asValue_some_value h₁
      subst h₁
      replace ⟨ty₃, h₂⟩ := residual_asValue_some_value h₂
      subst h₂

      -- can find an entity e for uid from a
      have ⟨e, h₆⟩: ∃e, newStore.find? uid = some e := by
        subst newStore
        simp [Residual.allLiteralUIDs, Set.filter, Set.singleton, Set.elts, Union.union, Set.union, Set.make, List.canonicalize]
        apply find_entity_in_batched_new_store h_wb
        simp [List.insertCanonical, List.canonicalize, Set.empty]
      simp [Residual.treeSize]
      simp [PartialEntities.get] at h₃
      have h₇ : (Map.mapOnValues EntityOrMissing.asPartial newStore).find? uid = some e.asPartial := by
        exact Map.find?_mapOnValues_some EntityOrMissing.asPartial h₆
      specialize h₃ e.asPartial h₇
      simp [EntityOrMissing.asPartial] at h₃
      split at h₃
      . simp [PartialEntityData.tags] at h₃
      . simp [EntityData.asPartial, PartialEntityData.tags] at h₃



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
  (store : EntitiesWithMissing)
   :
  EntityLoader.WellBehaved es loader →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es (req.asPartialRequest) pes →
  Residual.WellTyped env (Residual.binaryApp op a b ty) →
  (batchedEvalLoop (Residual.binaryApp op a b ty) req loader store 1).treeSize < (Residual.binaryApp op a b ty).treeSize := by
  intro h_wb h_wf h_ref h_wt

  have new_wt := batched_eval_loop_preserves_well_typed loader store 1 h_wf h_ref h_wt
  unfold batchedEvalLoop
  unfold batchedEvalLoop at new_wt
  simp only at new_wt


  simp only

  have newStore := (loader (Set.filter (fun uid => (Map.find? store uid).isNone) (Residual.binaryApp op a b ty).allLiteralUIDs) ++
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
    split at new_wt
    case h_1 v ty h₂ =>
      rw [h₂] at h₁
      specialize h₁ v ty
      simp at h₁
    case h_2 dup =>
    clear dup

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
            clear h₃
            simp [apply₂.self]
            simp [batchedEvalLoop, TPE.evaluate, TPE.apply₂] at new_wt
            rw [a_some] at new_wt
            rw [h₂] at new_wt
            simp [someOrSelf, apply₂.self] at new_wt
            rw [h₄] at new_wt
            simp at new_wt

            exact binaryApp_termination_memₛ h_wb a_some h₂ h₄ new_wt
      case h_14 h₃ =>
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
            clear h₃
            simp [apply₂.self]
            simp [batchedEvalLoop, TPE.evaluate, TPE.apply₂] at new_wt
            rw [a_some] at new_wt
            rw [h₂] at new_wt
            simp [someOrSelf, apply₂.self] at new_wt
            rw [h₄] at new_wt
            simp at new_wt

            exact binaryApp_termination_memₑ h_wb a_some h₂ h₄ new_wt
      case h_16 h₃ =>
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
            clear h₃
            simp [apply₂.self]
            simp [batchedEvalLoop, TPE.evaluate, TPE.apply₂] at new_wt
            rw [a_some] at new_wt
            rw [h₂] at new_wt
            simp [someOrSelf, apply₂.self] at new_wt
            rw [h₄] at new_wt
            simp at new_wt

            exact binaryApp_termination_hasTag h_wb a_some h₂ h₄ new_wt
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
  (store : EntitiesWithMissing):
  EntityLoader.WellBehaved es loader →
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es (req.asPartialRequest) pes →
  Residual.WellTyped env residual →
  residual.asValue = Option.none →
  (batchedEvalLoop residual req loader store 1).treeSize < residual.treeSize
  := by
  -- The batched evaluation loop loads new entities and evaluates
  let toLoad := residual.allLiteralUIDs.filter (λ uid => (store.find? uid).isNone)
  let newEntities: EntitiesWithMissing := (loader toLoad)
  let newStore := newEntities ++ store
  intro h_wb h_wf h_ref h_wt h₁

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
    cases h_wt; rename_i h_wt₁ h_wt₂
    have ih := batched_eval_loop_decreases_size expr req loader store h_wb h_wf h_ref h_wt₁
    apply unaryApp_termination op expr ty req loader store ih
  | binaryApp op a b ty =>
    apply binaryApp_termination op a b ty req loader store h_wb h_wf h_ref h_wt
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
