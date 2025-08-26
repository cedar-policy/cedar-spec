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


-- TODO super ugly theorem for sizeOf
theorem sizeOf_Residual_rec2_eq_ls_sizeOf (ls: List (Attr × Residual)) :
  let rec2: Nat := (Residual.rec_2 (fun v ty => 1 + v._sizeOf_1 + ty._sizeOf_1) (fun v ty => 1 + v._sizeOf_1 + ty._sizeOf_1)
        (fun cond thenExpr elseExpr ty cond_ih thenExpr_ih elseExpr_ih =>
          1 + cond_ih + thenExpr_ih + elseExpr_ih + ty._sizeOf_1)
        (fun a b ty a_ih b_ih => 1 + a_ih + b_ih + ty._sizeOf_1)
        (fun a b ty a_ih b_ih => 1 + a_ih + b_ih + ty._sizeOf_1)
        (fun op expr ty expr_ih => 1 + op._sizeOf_1 + expr_ih + ty._sizeOf_1)
        (fun op a b ty a_ih b_ih => 1 + op._sizeOf_1 + a_ih + b_ih + ty._sizeOf_1)
        (fun expr attr ty expr_ih => 1 + expr_ih + String._sizeOf_1 attr + ty._sizeOf_1)
        (fun expr attr ty expr_ih => 1 + expr_ih + String._sizeOf_1 attr + ty._sizeOf_1)
        (fun ls ty ls_ih => 1 + ls_ih + ty._sizeOf_1) (fun map ty map_ih => 1 + map_ih + ty._sizeOf_1)
        (fun xfn args ty args_ih => 1 + xfn._sizeOf_1 + args_ih + ty._sizeOf_1) (fun ty => 1 + ty._sizeOf_1) 1
        (fun head tail head_ih tail_ih => 1 + head_ih + tail_ih) 1
        (fun head tail head_ih tail_ih => 1 + head_ih + tail_ih)
        (fun fst snd snd_ih => 1 + String._sizeOf_1 fst + snd_ih) ls)
  ls._sizeOf_1 = rec2
  := by
  intro rec2
  subst rec2
  cases ls
  case nil => simp [List._sizeOf_1]
  case cons hd tl =>
    simp [List._sizeOf_1, Residual.rec]
    have ih := sizeOf_Residual_rec2_eq_ls_sizeOf tl
    simp [sizeOf, Prod._sizeOf_1]
    -- tmp to unfold just this instance of _sizeOf_1
    let tmp : hd.snd._sizeOf_1 = (Residual.rec (fun v ty => 1 + sizeOf v + sizeOf ty) (fun v ty => 1 + sizeOf v + sizeOf ty)
    (fun cond thenExpr elseExpr ty cond_ih thenExpr_ih elseExpr_ih =>
      1 + cond_ih + thenExpr_ih + elseExpr_ih + sizeOf ty)
    (fun a b ty a_ih b_ih => 1 + a_ih + b_ih + sizeOf ty) (fun a b ty a_ih b_ih => 1 + a_ih + b_ih + sizeOf ty)
    (fun op expr ty expr_ih => 1 + sizeOf op + expr_ih + sizeOf ty)
    (fun op a b ty a_ih b_ih => 1 + sizeOf op + a_ih + b_ih + sizeOf ty)
    (fun expr attr ty expr_ih => 1 + expr_ih + sizeOf attr + sizeOf ty)
    (fun expr attr ty expr_ih => 1 + expr_ih + sizeOf attr + sizeOf ty) (fun ls ty ls_ih => 1 + ls_ih + sizeOf ty)
    (fun map ty map_ih => 1 + map_ih + sizeOf ty) (fun xfn args ty args_ih => 1 + sizeOf xfn + args_ih + sizeOf ty)
    (fun ty => 1 + sizeOf ty) 1 (fun head tail head_ih tail_ih => 1 + head_ih + tail_ih) 1
    (fun head tail head_ih tail_ih => 1 + head_ih + tail_ih) (fun fst snd snd_ih => 1 + sizeOf fst + snd_ih) hd.snd) := by
      simp [Residual._sizeOf_1]
    rw [tmp]
    simp at ih
    rw [← ih]
    congr


theorem sizeOf_Residual_record_elems_lt {ls ty} :
  sizeOf ls < sizeOf (Residual.record ls (CedarType.record ty))
  := by
  simp [sizeOf, Residual._sizeOf_1]
  rw [sizeOf_Residual_rec2_eq_ls_sizeOf]
  omega

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
      have termination : sizeOf v <= sizeOf ls := by
        -- Use the existing lemma for list member size
        have h_snd_lt : sizeOf (k, v).snd < 1 + sizeOf ls := List.sizeOf_snd_lt_sizeOf_list h_mem
        simp at h_snd_lt
        omega

      have termination₂ : sizeOf ls < sizeOf (Residual.record ls (CedarType.record ty₁)) := by
        exact sizeOf_Residual_record_elems_lt
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
