import Cedar.Thm.Validation.Levels.CheckLevel

namespace Cedar.Thm

open Cedar.Data Cedar.Spec Cedar.Validation

/--
Combined chain step: decomposes the chain check AND gives the cost monotonicity.
-/
theorem chain_step_full
  (a : Attr) (rest : List Attr) (env : TypeEnv) (ty : CedarType)
  (hchain : checkExtHasAttrChain env ty (a :: rest)
    (extHasAttrChainCost env ty (a :: rest)) = true) :
  ∃ nextTy : CedarType,
    checkExtHasAttrChain env nextTy rest
      (extHasAttrChainCost env nextTy rest) = true ∧
    extHasAttrChainCost env nextTy rest ≤ extHasAttrChainCost env ty (a :: rest) := by
  cases rest with
  | nil =>
    -- With [a] (single element), both cost and check are trivial
    refine ⟨.int, ?_, ?_⟩
    · simp [checkExtHasAttrChain]
    · simp [extHasAttrChainCost]
  | cons b bs =>
    -- With a :: b :: bs, unfold both definitions
    simp only [checkExtHasAttrChain, extHasAttrChainCost] at hchain ⊢
    cases ty with
    | entity ety =>
      cases h₁ : env.ets.attrs? ety with
      | none =>
        refine ⟨.int, ?_, ?_⟩
        all_goals { cases bs <;> simp [checkExtHasAttrChain, extHasAttrChainCost] }
      | some rty =>
        simp only [h₁] at hchain ⊢
        cases h₂ : rty.find? a with
        | none =>
          refine ⟨.int, ?_, ?_⟩
          · cases bs <;> simp [checkExtHasAttrChain]
          · cases bs <;> simp [extHasAttrChainCost]
        | some qty =>
          simp only [h₂] at hchain ⊢
          cases h₅ : qty.getType <;> simp only [h₅] at hchain ⊢
          all_goals first
            | (rename_i x₁
               simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq] at hchain
               have h := hchain.2
               have heq : 1 + extHasAttrChainCost env (.entity x₁) (b :: bs) - 1 =
                   extHasAttrChainCost env (.entity x₁) (b :: bs) := by omega
               rw [heq] at h
               exact ⟨.entity x₁, h, by omega⟩)
            | exact ⟨_, hchain, Nat.le_refl _⟩
    | record rty =>
      cases h2 : rty.find? a with
      | none =>
        refine ⟨.int, ?_, ?_⟩
        · cases bs <;> simp [checkExtHasAttrChain]
        · cases bs <;> simp [extHasAttrChainCost]
      | some qty =>
        simp only [h2] at hchain ⊢
        cases h₅ : qty.getType <;> simp only [h₅] at hchain ⊢
        all_goals first
          | (rename_i x₁
             simp only [gt_iff_lt, Bool.and_eq_true, decide_eq_true_eq] at hchain
             have h₆ := hchain.2
             have heq : 1 + extHasAttrChainCost env (.entity x₁) (b :: bs) - 1 =
                 extHasAttrChainCost env (.entity x₁) (b :: bs) := by omega
             rw [heq] at h₆
             exact ⟨.entity x₁, h₆, by omega⟩)
          | exact ⟨_, hchain, Nat.le_refl _⟩
    | _ =>
      refine ⟨.int, ?_, ?_⟩ <;> cases bs <;> simp [checkExtHasAttrChain, extHasAttrChainCost]

end Cedar.Thm
