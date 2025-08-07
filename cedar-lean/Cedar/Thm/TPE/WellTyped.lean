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

def PEWellTyped (env : TypeEnv)
  (r₁ r₂ : Residual)
  (req : Request)
  (preq : PartialRequest)
  (es : Entities) : Prop :=
  InstanceOfWellFormedEnvironment req es env →
  RequestRefines req preq →
  Residual.WellTyped env r₁ →
  Residual.WellTyped env r₂

/--
Helper theorem: Partial evaluation preserves well-typedness for variable residuals.
-/
theorem partial_evaluation_preserves_var_well_typedness      {env : TypeEnv}
  {v : Var}
  {ty : CedarType}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  :
  PEWellTyped env (Residual.var v ty) (varₚ preq v ty) req preq es := by
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
        any_goals (
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
          )
  | or a b ty =>
    simp [TPE.evaluate, Residual.typeOf]
    . cases h_wt with
      | or h₁ h₂ h₃ h₄ =>
        split
        repeat case _ =>
          rename Residual => x
          rename CedarType => ty
          rename_i heq
          unfold TPE.or at heq
          split at heq

          . injection heq
            try rename_i heq
            try rw [heq]
          . have h₅ := tpe_evaluate_preserves_type h_wf h_ref h₂
            rw [heq] at h₅
            rw [h₄] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . (first
             | contradiction
             | injection heq with h₅
               rw [h₅])
          . have h₅ := tpe_evaluate_preserves_type h_wf h_ref h₁
            rw [heq] at h₅
            rw [h₃] at h₅
            simp [Residual.typeOf] at h₅
            exact h₅
          . first
            | contradiction
            | injection heq with h₅ h₆ h₇
              rw [h₇]
  | ite c t e ty =>
    -- Case: .ite c t e ty
    -- TPE.evaluate (.ite c t e ty) = TPE.ite (TPE.evaluate c) (TPE.evaluate t) (TPE.evaluate e) ty
    simp [TPE.evaluate, Residual.typeOf]
    cases h_wt with
    | ite h_c h_t h_e h_ty_c h_ty_t =>
      -- h_ty_t : t.typeOf = e.typeOf
      -- The result type is t.typeOf
      -- We need to use the same pattern as and/or cases
      split
      repeat case _ =>
        rename Residual => x
        rename CedarType => result_ty
        rename_i heq
        unfold TPE.ite at heq
        split at heq
        · split at heq
          · -- b = true case
            have h_t_type := tpe_evaluate_preserves_type h_wf h_ref h_t
            rw [heq] at h_t_type
            simp [Residual.typeOf] at h_t_type
            exact h_t_type
          · -- b = false case
            have h_e_type := tpe_evaluate_preserves_type h_wf h_ref h_e
            rw [heq] at h_e_type
            rw [h_ty_t]
            rw [← h_e_type]
            simp [Residual.typeOf]
        · first
          | contradiction
          | injection heq with h₁
            rw [h₁]
        · first
          | contradiction
          | have heq' := congr_arg (·.typeOf) heq
            simp [Residual.typeOf] at heq'
            unfold Residual.typeOf
            rw [heq']
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
  | or a b ty =>
    simp [TPE.evaluate]
    cases h_wt with
    | or h_a h_b h_ty_a h_ty_b =>
      let a_eval := TPE.evaluate a preq pes
      let b_eval := TPE.evaluate b preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_a_wt : Residual.WellTyped env a_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_a
      have h_b_wt : Residual.WellTyped env b_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_b
      unfold TPE.or
      split
      . apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool true BoolType.anyBool
        simp [InstanceOfBoolType]
      . exact h_b_wt
      . apply Residual.WellTyped.error
      . exact h_a_wt
      . apply Residual.WellTyped.or
        · exact h_a_wt
        · exact h_b_wt
        · rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_a]
          exact h_ty_a
        · rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_b]
          exact h_ty_b
  | ite c t e ty =>
    simp [TPE.evaluate]
    cases h_wt with
    | ite h_c h_t h_e h_ty_c h_ty_t =>
      let c_eval := TPE.evaluate c preq pes
      let t_eval := TPE.evaluate t preq pes
      let e_eval := TPE.evaluate e preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_c_wt : Residual.WellTyped env c_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_c
      have h_t_wt : Residual.WellTyped env t_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_t
      have h_e_wt : Residual.WellTyped env e_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_e
      unfold TPE.ite
      split
      . split
        · exact h_t_wt
        · exact h_e_wt
      . apply Residual.WellTyped.error
      . have h_t_type_eq : t.typeOf = t_eval.typeOf := (tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_t).symm
        rw [h_t_type_eq]
        apply Residual.WellTyped.ite
        · exact h_c_wt
        · exact h_t_wt
        · exact h_e_wt
        · rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_c]
          exact h_ty_c
        · rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_t]
          rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_e]
          exact h_ty_t
  | unaryApp op expr ty =>
    simp [TPE.evaluate]
    cases h_wt with
    | unaryApp h_expr h_op =>
      let expr_eval := TPE.evaluate expr preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_expr_wt : Residual.WellTyped env expr_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_expr
      unfold TPE.apply₁
      split
      . apply Residual.WellTyped.error
      . cases h : expr_eval.asValue with
        | some v =>
          unfold someOrError
          split
          . split
            . rename_i r v₂ ov v₁ v2v ty ox x v heq
              injection v2v with hᵥ
              unfold Spec.apply₁ at heq
              apply Residual.WellTyped.val
              split at heq
              . cases h_op
                simp [Except.toOption] at heq
                rw [← heq]
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . cases h_op
                simp [Except.toOption, intOrErr] at heq
                rename Int64 => i
                cases h₂: i.neg?
                . rw [h₂] at heq
                  simp at heq
                . rw [h₂] at heq
                  simp at heq
                  rw [← heq]
                  apply InstanceOfType.instance_of_int
              . cases h_op
                simp [Except.toOption] at heq
                rw [← heq]
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . simp [Except.toOption] at heq
                rw [← heq]
                cases h_op
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . cases h_op
                simp [Except.toOption] at heq
                rw [← heq]
                apply InstanceOfType.instance_of_bool
                simp [InstanceOfBoolType]
              . contradiction
            . apply Residual.WellTyped.error
          . contradiction
        | none =>
          apply Residual.WellTyped.unaryApp
          · exact h_expr_wt
          · cases h_op with
            | not h_ty =>
              apply UnaryResidualWellTyped.not
              rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | neg h_ty =>
              apply UnaryResidualWellTyped.neg
              rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | isEmpty h_ty =>
              apply UnaryResidualWellTyped.isEmpty
              rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | like h_ty =>
              apply UnaryResidualWellTyped.like
              rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_expr]
              exact h_ty
            | is h_ty =>
              apply UnaryResidualWellTyped.is
              rw [tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_expr]
              exact h_ty
  | binaryApp op expr1 expr2 ty =>
    simp [TPE.evaluate]
    cases h_wt with
    | binaryApp h_expr1 h_expr2 h_op =>
      let expr1_eval := TPE.evaluate expr1 preq pes
      let expr2_eval := TPE.evaluate expr2 preq pes
      have h_ref_reconstructed : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩
      have h_expr1_wt : Residual.WellTyped env expr1_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_expr1
      have h_expr2_wt : Residual.WellTyped env expr2_eval := partial_evaluation_preserves_residual_well_typedness h_wf h_ref_reconstructed h_expr2
      unfold TPE.apply₂
      split
      . simp
        split
        repeat case _ =>
          apply Residual.WellTyped.val
          cases h_op
          all_goals {
            apply InstanceOfType.instance_of_bool
            unfold InstanceOfBoolType
            split <;> try simp
            contradiction
          }
        . rename_i i j h₁ h₂
          cases (i.add? j) <;> simp [someOrError]
          . apply Residual.WellTyped.error
          . apply Residual.WellTyped.val
            cases h_op
            all_goals {
              apply InstanceOfType.instance_of_int
            }
        . rename_i i j h₁ h₂
          cases (i.sub? j) <;> simp [someOrError]
          . apply Residual.WellTyped.error
          . apply Residual.WellTyped.val
            cases h_op
            all_goals {
              apply InstanceOfType.instance_of_int
            }
        . rename_i i j h₁ h₂
          cases (i.mul? j) <;> simp [someOrError]
          . apply Residual.WellTyped.error
          . apply Residual.WellTyped.val
            cases h_op
            all_goals {
              apply InstanceOfType.instance_of_int
            }
        . rename_i i j h₁ h₂
          apply Residual.WellTyped.val
          cases h_op
          all_goals {
            apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
          }
        repeat case _ =>
          apply Residual.WellTyped.val
          cases h_op
          all_goals {
            apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
          }
        . rename_i v1 v2 id1 id2 h₁ h₂
          cases (TPE.inₑ id1 id2 pes)
          . simp [someOrSelf]
            unfold TPE.apply₂.self
            unfold Residual.asValue at h₁
            unfold Residual.asValue at h₂
            split at h₁
            . split at h₂
              . injection h₁
                injection h₂
                rename_i x v ty₁ h₃ h₄ h₅ ty₂ h₇ h₈ h₉
                rw [h₃]
                rw [h₇]
                apply Residual.WellTyped.binaryApp
                . apply Residual.WellTyped.val
                  subst expr1_eval
                  subst expr2_eval
                  rw [h₃] at h_expr1_wt
                  rw [h₇] at h_expr2_wt
                  cases h_expr1_wt
                  rename_i h₈
                  exact h₈
                . apply Residual.WellTyped.val
                  subst expr1_eval
                  subst expr2_eval
                  rw [h₃] at h_expr1_wt
                  rw [h₇] at h_expr2_wt
                  cases h_expr2_wt
                  rename_i h₈
                  exact h₈
                . rw [h₈]
                  rw [h₉]
                  cases h_op
                  . apply BinaryResidualWellTyped.memₑ
                    . simp [Residual.typeOf]
                      rename_i ety₁ ety₂ eq₁ eq₂
                      have hᵣ : (ty₁ = CedarType.entity ety₁) := by {
                        subst expr1_eval
                        subst expr2_eval
                        have h₁₀ := tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_expr1
                        rw [← h₁₀] at eq₁
                        rw [h₃] at eq₁
                        simp [Residual.typeOf] at eq₁
                        exact eq₁
                      }
                      exact hᵣ
                    . simp [Residual.typeOf]
                      rename_i ety₁ ety₂ eq₁ eq₂
                      have hᵣ : (ty₂ = CedarType.entity ety₂) := by {
                        subst expr1_eval
                        subst expr2_eval
                        have h₁₀ := tpe_evaluate_preserves_type h_wf h_ref_reconstructed h_expr2
                        rw [← h₁₀] at eq₂
                        rw [h₇] at eq₂
                        simp [Residual.typeOf] at eq₂
                        exact eq₂
                      }
                      exact hᵣ
                  . sorry
              . contradiction
            . contradiction
          . simp [someOrSelf]
            apply Residual.WellTyped.val
            cases h_op
            . apply InstanceOfType.instance_of_bool
              simp [InstanceOfBoolType]
            . apply InstanceOfType.instance_of_bool
              simp [InstanceOfBoolType]
        repeat case _ => sorry
      . sorry
  | error ty =>
    simp [TPE.evaluate]
    exact h_wt
  | _ => sorry
end Cedar.Thm
