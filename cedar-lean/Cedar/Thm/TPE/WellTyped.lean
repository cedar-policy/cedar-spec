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
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.WellTypedCases
import Cedar.Thm.Validation.WellTyped.ResidualDefinition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

/-!
This file contains theorems about partial evaluation preserving well-typedness of residuals.
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE


/--
Helper theorem: Partial evaluation preserves well-typedness for variable residuals.
-/
theorem partial_evaluation_well_typed_var {pes}      {env : TypeEnv}
  {v : Var}
  {ty : CedarType}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  :
  PEWellTyped env (Residual.var v ty) (varₚ preq v ty) req preq es pes := by
  intro h_wf h_ref h_wt
  rcases h_ref with ⟨h_rref, h_eref⟩
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
          have ⟨_, _, _, hwf_act, _⟩ := hwf
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
Theorem: Partial evaluation preserves well-typedness of residuals.

If a residual is well-typed in some type environment, then partially evaluating it
with a partial request and partial entities produces another well-typed residual
in the same type environment.

This is a fundamental property ensuring that the partial evaluation process
maintains type safety throughout the computation.
-/
theorem partial_eval_preserves_well_typed
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
  have h_ref : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩

  cases hᵣ : res <;> rw [hᵣ] at h_wt
  case val v ty =>
    exact partial_eval_well_typed_val h_wf h_ref h_wt
  case var v ty =>
    exact partial_eval_well_typed_var h_wf h_ref h_wt
  case and a b ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | and h_a h_b h_ty_a h_ty_b =>
      have ih_a : Residual.WellTyped env (TPE.evaluate a preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_a
      have ih_b : Residual.WellTyped env (TPE.evaluate b preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_b
      exact partial_eval_well_typed_and ih_a ih_b h_wf h_ref h_wt
  case or a b ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | or h_a h_b h_ty_a h_ty_b =>
      have ih_a : Residual.WellTyped env (TPE.evaluate a preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_a
      have ih_b : Residual.WellTyped env (TPE.evaluate b preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_b
      exact partial_eval_well_typed_or ih_a ih_b h_wf h_ref h_wt
  case ite c t e ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | ite h_c h_t h_e h_ty_c h_ty_t =>
      have ih_c : Residual.WellTyped env (TPE.evaluate c preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_c
      have ih_t : Residual.WellTyped env (TPE.evaluate t preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_t
      have ih_e : Residual.WellTyped env (TPE.evaluate e preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_e
      exact partial_eval_well_typed_ite ih_c ih_t ih_e h_wf h_ref h_wt
  case unaryApp op expr ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | unaryApp h_expr h_op =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr
      exact partial_eval_well_typed_unaryApp ih_expr h_wf h_ref h_wt
  case binaryApp op expr1 expr2 ty =>
    simp [TPE.evaluate]
    have h_wt₂ := h_wt
    cases h_wt with
    | binaryApp h_expr1 h_expr2 h_op =>
      have ih1 : Residual.WellTyped env (TPE.evaluate expr1 preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr1
      have ih2 : Residual.WellTyped env (TPE.evaluate expr2 preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr2

      apply partial_eval_well_typed_app₂ ih1 ih2 h_wf h_ref h_wt₂
  case error ty =>
    exact partial_eval_well_typed_error h_wf h_ref h_wt
  case set ls ty =>
    let h_wt₂ := h_wt
    cases h_wt₂
    rename_i ty₁ h₀ h₁ h₂
    have ih_ls : ∀ r ∈ ls, Residual.WellTyped env (TPE.evaluate r preq pes) := by
      intros r h_mem
      specialize h₀ r h_mem
      exact partial_eval_preserves_well_typed h_wf h_ref h₀
    exact partial_eval_well_typed_set ih_ls h_wf h_ref h_wt
  case record ls ty =>
    let h_wt₂ := h_wt
    cases h_wt₂
    rename_i ty₁ h₀ h₁
    have ih_ls : ∀ k v, (k, v) ∈ ls → Residual.WellTyped env (TPE.evaluate v preq pes) := by
      intros k v h_mem
      specialize h₀ k v h_mem
      have termination : sizeOf v < sizeOf res := by {
        sorry
      }
      exact partial_eval_preserves_well_typed h_wf h_ref h₀
    exact partial_eval_well_typed_record ih_ls h_wf h_ref h_wt
  case getAttr expr attr ty =>
    let h_wt₂ := h_wt
    cases h_wt₂
    case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h₅
      exact partial_eval_well_typed_getAttr ih_expr h_wf h_ref h_wt
    case getAttr_record rty h₄ h₅ h₆ =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h₄
      exact partial_eval_well_typed_getAttr ih_expr h_wf h_ref h_wt
  case hasAttr expr attr ty =>
    let h_wt₂ := h_wt
    cases h_wt₂
    case hasAttr_entity ety h₅ h₆ =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h₅
      exact partial_eval_well_typed_hasAttr ih_expr h_wf h_ref h_wt
    case hasAttr_record rty h₆ h₇ =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h₆
      exact partial_eval_well_typed_hasAttr ih_expr h_wf h_ref h_wt
  case call xfn args ty =>
    let h_wt₂ := h_wt
    cases h_wt₂
    rename_i h₁ h₂
    have ih_args : ∀ r ∈ args, Residual.WellTyped env (TPE.evaluate r preq pes) := by
      intros r h_mem
      specialize h₁ r h_mem
      exact partial_eval_preserves_well_typed h_wf h_ref h₁
    exact partial_eval_well_typed_call ih_args h_wf h_ref h_wt
termination_by (sizeOf res)


end Cedar.Thm
