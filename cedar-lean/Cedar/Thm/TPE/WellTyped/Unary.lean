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
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

import Cedar.Thm.TPE.WellTyped.Basic

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

private theorem apply₁_some_wt {env : TypeEnv} {op : UnaryOp} {rv : ResidualValue} {rty ty : CedarType}
  (h_op : UnaryResidualWellTyped op (Residual.val rv rty) ty) :
  Residual.WellTyped env
    (match op, rv with
     | .not, .prim (.bool b) => Residual.val (↑(!b) : Value).asResidualValue ty
     | .neg, .prim (.int i) => someOrError (i.neg?) ty
     | .isEmpty, .set s => Residual.val (↑s.isEmpty : Value).asResidualValue ty
     | .like p, .prim (.string s) => Residual.val (↑(wildcardMatch s p) : Value).asResidualValue ty
     | .is ety, .prim (.entityUID uid) => Residual.val (↑(ety == uid.ty) : Value).asResidualValue ty
     | _, _ => .error ty) := by
  -- Case split on rv first to reduce the match
  cases rv with
  | prim p =>
    cases p with
    | bool b =>
      cases h_op with
      | not => simp [Value.asResidualValue, well_typed_bool]
      | neg => exact .error
      | isEmpty => exact .error
      | like => exact .error
      | is => exact .error
    | int i =>
      cases h_op
      case not => exact .error
      case neg =>
        cases h : i.neg? with
        | none => simp [someOrError, h]; exact .error
        | some j => simp [someOrError, h, Value.asResidualValue, well_typed_int]
      case isEmpty => exact .error
      case like => exact .error
      case is => exact .error
    | string s =>
      cases h_op with
      | not => exact .error
      | neg => exact .error
      | isEmpty => exact .error
      | like => simp [Value.asResidualValue, well_typed_bool]
      | is => exact .error
    | entityUID uid =>
      cases h_op with
      | not => exact .error
      | neg => exact .error
      | isEmpty => exact .error
      | like => exact .error
      | is => simp [Value.asResidualValue, well_typed_bool]
  | set s =>
    cases h_op with
    | not => exact .error
    | neg => exact .error
    | isEmpty => simp [Value.asResidualValue, well_typed_bool]
    | like => exact .error
    | is => exact .error
  | record m => cases h_op <;> exact .error
  | ext x => cases h_op <;> exact .error

theorem partial_eval_well_typed_unaryApp {env : TypeEnv} {op : UnaryOp} {expr : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.unaryApp op expr ty) (TPE.evaluate (Residual.unaryApp op expr ty) preq pes) req preq es pes
:= by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | unaryApp h_expr h_op =>
    unfold TPE.apply₁
    split
    · -- some rv case
      rename_i rv heq
      have ⟨rty, hrty⟩ : ∃ rty, TPE.evaluate expr preq pes = .val rv rty := by
        cases h : TPE.evaluate expr preq pes <;> simp [Residual.asResidualValue, h] at heq
        exact ⟨_, by rw [heq]⟩
      have hty : rty = expr.typeOf := by
        have := partial_eval_preserves_typeof expr h_expr preq pes
        rw [hrty] at this; simp [Residual.typeOf] at this; exact this
      -- Now case split on rv to reduce the match
      cases h_op with
      | not h₁ =>
        cases rv with
        | prim p => cases p with
          | bool b => simp [Value.asResidualValue, well_typed_bool]
          | _ => exact .error
        | _ => exact .error
      | neg h₁ =>
        cases rv with
        | prim p => cases p with
          | int i =>
            cases h : i.neg? with
            | none => simp [someOrError, h]; exact .error
            | some j => simp [someOrError, h, Value.asResidualValue, well_typed_int]
          | _ => exact .error
        | _ => exact .error
      | isEmpty h₁ =>
        cases rv with
        | set s => simp [Value.asResidualValue, well_typed_bool]
        | _ => exact .error
      | like h₁ =>
        cases rv with
        | prim p => cases p with
          | string s => simp [Value.asResidualValue, well_typed_bool]
          | _ => exact .error
        | _ => exact .error
      | is h₁ =>
        cases rv with
        | prim p => cases p with
          | entityUID uid => simp [Value.asResidualValue, well_typed_bool]
          | _ => exact .error
        | _ => exact .error
    · have h_op' : UnaryResidualWellTyped op (TPE.evaluate expr preq pes) ty := by
        have hty := partial_eval_preserves_typeof expr h_expr preq pes
        cases h_op with
        | not h₁ => exact .not (by rw [hty]; exact h₁)
        | neg h₁ => exact .neg (by rw [hty]; exact h₁)
        | isEmpty h₁ => exact .isEmpty (by rw [hty]; exact h₁)
        | like h₁ => exact .like (by rw [hty]; exact h₁)
        | is h₁ => exact .is (by rw [hty]; exact h₁)
      split
      · exact .error
      · exact .unaryApp h_expr_wt h_op'

end Cedar.Thm
