/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.TPE
import Cedar.Thm.TPE.Input
import Cedar.Thm.Validation.WellTyped.ResidualDefinition

/-!
This file contains theorems about partial evaluation preserving well-typedness of residuals.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

/--
Helper theorem: Partial evaluation preserves well-typedness for variable residuals.
-/
theorem partial_evaluation_preserves_var_well_typedness
  {env : TypeEnv}
  {v : Var}
  {ty : CedarType}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestRefines req preq →
  Residual.WellTyped env (Residual.var v ty) →
  Residual.WellTyped env (varₚ preq v ty) := by
  intro h_wf h_rref h_wt
  unfold varₚ
  cases v with
  | principal =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    cases h : preq.principal.asEntityUID
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_pv
      apply Residual.WellTyped.val
      cases h_pv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | principal =>
            apply InstanceOfType.instance_of_entity req.principal env.reqty.principal
            rcases h_wf with ⟨_, ⟨h_principal, _, _, _⟩, _⟩
            exact h_principal
  | resource =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    cases h : preq.resource.asEntityUID
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_rv
      apply Residual.WellTyped.val
      cases h_rv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | resource =>
            apply InstanceOfType.instance_of_entity req.resource env.reqty.resource
            rcases h_wf with ⟨_, ⟨_, _, h_resource, _⟩, _⟩
            exact h_resource
  | action =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    -- Action is always concrete in partial requests
    dsimp [varₚ.varₒ, someOrSelf]
    apply Residual.WellTyped.val
    cases h_wt with
    | var h₄ =>
      cases h₄ with
      | action =>
        rw [←h_av]
        apply InstanceOfType.instance_of_entity req.action env.reqty.action.ty
        rcases h_wf with ⟨hwf, ⟨_, h_action, _, _⟩, _⟩
        rw [h_action]
        have : InstanceOfEntityType env.reqty.action env.reqty.action.ty env := by
          have ⟨_, _, ⟨_, hwf_act, _⟩⟩ := hwf
          simp [
            InstanceOfEntityType, EntityUID.WellFormed,
            ActionSchema.contains, hwf_act,
          ]
        exact this
  | context =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    cases h : preq.context
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_cv
      apply Residual.WellTyped.val
      cases h_cv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | context =>
            rcases h_wf with ⟨_, ⟨_, _, _, h_context⟩, _⟩
            exact type_lifting_preserves_instance_of_type h_context

/--
Theorem: TPE.evaluate preserves the typeOf property.

If a residual has a certain type, then partially evaluating it produces
a residual with the same type. This is a key property for type preservation
in partial evaluation.
-/
theorem tpe_evaluate_preserves_type
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  (TPE.evaluate res preq pes).typeOf = res.typeOf := by
  intro h_wf h_ref h_wt
  have h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩
  -- Proof by cases on the structure of the residual
  cases res with
  | val v ty =>
    -- Case: .val v ty
    -- TPE.evaluate (.val v ty) = .val v ty, so typeOf is preserved
    simp [TPE.evaluate, Residual.typeOf]
  | var v ty =>
    -- Case: .var v ty
    -- This case is more complex as varₚ can return different residuals
    simp [TPE.evaluate, Residual.typeOf]
    unfold varₚ
    cases v with
    | principal =>
      -- For each variable case, we need to show that varₚ preserves the type
      -- This requires analyzing the someOrSelf function
      dsimp [varₚ.varₒ]
      cases h: preq.principal.asEntityUID
      . dsimp [someOrSelf, Option.bind]
      . dsimp [someOrSelf]
    | resource | action =>
      dsimp [varₚ.varₒ]
      cases h: preq.resource.asEntityUID
      . dsimp [someOrSelf, Option.bind]
      . dsimp [someOrSelf]
    | context =>
      dsimp [varₚ.varₒ]
      dsimp [someOrSelf, Option.bind]
      cases h: preq.context
      . simp
      . simp
  | and a b ty =>
    simp [TPE.evaluate, Residual.typeOf]
    . cases h_wt with
      | and h₁ h₂ h₃ h₄ =>
        split
        repeat case _ =>
          rename Residual => x
          rename CedarType => ty
          rename_i heq
          unfold TPE.and at heq
          split at heq

          . have h₅ := tpe_evaluate_preserves_type h_wf h_ref h₂
            rw [heq] at h₅
            rw [h₄] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . (first
             | contradiction
             | injection heq with h₅ h₆
               rw [h₆])
          . first
            | contradiction
            | injection heq
              rename_i heq
              rw [heq]
          . have h₅ := tpe_evaluate_preserves_type h_wf h_ref h₁
            rw [h₃] at h₅
            rw [heq] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . first
            | contradiction
            | injection heq with h₅ h₆ h₇
              rw [h₇]
  | error ty =>
    -- Case: .error ty
    -- TPE.evaluate (.error ty) = .error ty, so typeOf is preserved
    simp [TPE.evaluate, Residual.typeOf]
  | _ =>
    -- Other cases to be implemented
    sorry

/--
Theorem: Partial evaluation preserves well-typedness of residuals.

If a residual is well-typed in some type environment, then partially evaluating it
with a partial request and partial entities produces another well-typed residual
in the same type environment.

This is a fundamental property ensuring that the partial evaluation process
maintains type safety throughout the computation.
-/
theorem partial_evaluation_preserves_residual_well_typedness
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  Residual.WellTyped env (TPE.evaluate res preq pes) := by
  intro h_wf h_ref h_wt
  unfold RequestAndEntitiesRefine at h_ref
  rcases h_ref with ⟨h_rref, h_eref⟩
  -- Proof by cases on the structure of the residual
  cases res with
  | val v ty =>
    -- Case: .val v ty
    -- TPE.evaluate (.val v ty) req es = .val v ty
    simp [TPE.evaluate]
    exact h_wt
  | var v ty =>
    -- Case: .var v ty
    -- Use the helper theorem for variable cases
    simp [TPE.evaluate]
    exact partial_evaluation_preserves_var_well_typedness h_wf h_rref h_wt
  | and a b ty =>
    -- Case: .and a b ty
    -- TPE.evaluate (.and a b ty) preq pes = TPE.and (TPE.evaluate a preq pes) (TPE.evaluate b preq pes) ty
    simp [TPE.evaluate]
    -- We need to prove that TPE.and preserves well-typedness
    -- This requires analyzing the cases in TPE.and
    cases h_wt with
    | and h_a h_b h_ty_a h_ty_b =>
      let a_eval := TPE.evaluate a preq pes
      let b_eval := TPE.evaluate b preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_a_wt : Residual.WellTyped env a_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_a
      have h_b_wt : Residual.WellTyped env b_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_b
      -- TPE.and has several cases - we need to handle each one
      unfold TPE.and
      split
      . -- Case: first operand is .val true, so TPE.and returns the second operand
        -- Goal: Residual.WellTyped env (TPE.evaluate b preq pes)
        exact h_b_wt
      . -- Case: first operand is .val false, so TPE.and returns false
        -- Goal: Residual.WellTyped env (Residual.val (Value.prim (Prim.bool false)) (CedarType.bool BoolType.anyBool))
        apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool false BoolType.anyBool
        simp [InstanceOfBoolType]
      . -- Case: first operand is .error, so TPE.and returns .error ty
        -- Goal: Residual.WellTyped env (Residual.error ty)
        apply Residual.WellTyped.error
      . -- Case: second operand is .val true, so TPE.and returns the first operand
        -- Goal: Residual.WellTyped env (TPE.evaluate a preq pes)
        exact h_a_wt
      . -- Case: default case, TPE.and returns .and a_eval b_eval ty
        -- Goal: Residual.WellTyped env (Residual.and (TPE.evaluate a preq pes) (TPE.evaluate b preq pes) ty)
        apply Residual.WellTyped.and
        · exact h_a_wt
        · exact h_b_wt
        · -- Need to show a_eval.typeOf = CedarType.bool BoolType.anyBool
          -- This follows from the fact that a has boolean type and TPE preserves types
          have h_a_type : a.typeOf = CedarType.bool BoolType.anyBool := h_ty_a
          -- Use the type preservation theorem
          rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_a]
          exact h_a_type
        · -- Need to show b_eval.typeOf = CedarType.bool BoolType.anyBool
          -- This follows from the fact that b has boolean type and TPE preserves types
          have h_b_type : b.typeOf = CedarType.bool BoolType.anyBool := h_ty_b
          -- Use the type preservation theorem
          rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_b]
          exact h_b_type
  | error ty =>
    -- Case: .error ty
    -- TPE.evaluate (.error ty) req es = .error ty
    simp [TPE.evaluate]
    exact h_wt
  | _ => sorry
end Cedar.Thm
