import Cedar.Thm.Validation.Levels.CheckLevel

namespace Cedar.Thm

open Cedar.Data Cedar.Spec Cedar.Validation

/--
Combined chain step: decomposes the chain check AND gives the cost monotonicity.
-/
theorem chain_step_full
  (a : Attr) (rest : List Attr) (env : TypeEnv) (ty : CedarType)
  (hchain : checkExtHasAttrChainTy env ty (a :: rest)
    (extHasAttrChainCostTy env ty (a :: rest)) = true) :
  ∃ nextTy : CedarType,
    checkExtHasAttrChainTy env nextTy rest
      (extHasAttrChainCostTy env nextTy rest) = true ∧
    extHasAttrChainCostTy env nextTy rest ≤ extHasAttrChainCostTy env ty (a :: rest) := by
  cases rest with
  | nil =>
    -- With [a] (single element), both cost and check are trivial
    refine ⟨.int, ?_, ?_⟩
    · simp [checkExtHasAttrChainTy]
    · simp [extHasAttrChainCostTy]
  | cons b bs =>
    -- With a :: b :: bs, unfold both definitions
    simp only [checkExtHasAttrChainTy, extHasAttrChainCostTy] at hchain ⊢
    cases ty with
    | entity ety =>
      cases h1 : env.ets.attrs? ety with
      | none =>
        refine ⟨.int, ?_, ?_⟩
        · cases bs <;> simp [checkExtHasAttrChainTy]
        · cases bs <;> simp [extHasAttrChainCostTy]
      | some rty =>
        simp only [h1] at hchain ⊢
        cases h2 : rty.find? a with
        | none =>
          refine ⟨.int, ?_, ?_⟩
          · cases bs <;> simp [checkExtHasAttrChainTy]
          · cases bs <;> simp [extHasAttrChainCostTy]
        | some qty =>
          simp only [h2] at hchain ⊢
          cases hty : qty.getType <;> simp only [hty] at hchain ⊢
          all_goals first
            | (rename_i nextEty
               simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq] at hchain
               have h := hchain.2
               have heq : 1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs) - 1 =
                   extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by omega
               rw [heq] at h
               exact ⟨.entity nextEty, h, by omega⟩)
            | exact ⟨_, hchain, Nat.le_refl _⟩
    | record rty =>
      cases h2 : rty.find? a with
      | none =>
        refine ⟨.int, ?_, ?_⟩
        · cases bs <;> simp [checkExtHasAttrChainTy]
        · cases bs <;> simp [extHasAttrChainCostTy]
      | some qty =>
        simp only [h2] at hchain ⊢
        cases hty : qty.getType <;> simp only [hty] at hchain ⊢
        all_goals first
          | (rename_i nextEty
             simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq] at hchain
             have h := hchain.2
             have heq : 1 + extHasAttrChainCostTy env (.entity nextEty) (b :: bs) - 1 =
                 extHasAttrChainCostTy env (.entity nextEty) (b :: bs) := by omega
             rw [heq] at h
             exact ⟨.entity nextEty, h, by omega⟩)
          | exact ⟨_, hchain, Nat.le_refl _⟩
    | _ =>
      refine ⟨.int, ?_, ?_⟩
      · cases bs <;> simp [checkExtHasAttrChainTy]
      · cases bs <;> simp [extHasAttrChainCostTy]

end Cedar.Thm
