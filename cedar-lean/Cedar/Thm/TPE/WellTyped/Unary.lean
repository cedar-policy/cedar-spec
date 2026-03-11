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


/--
Helper theorem: Partial evaluation preserves well-typedness for unary application residuals.
-/
theorem partial_eval_well_typed_unaryApp {env : TypeEnv} {op : UnaryOp} {expr : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.unaryApp op expr ty) (TPE.evaluate (Residual.unaryApp op expr ty) preq pes) req preq es pes
:= by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | unaryApp h_expr h_op =>
    let expr_eval := TPE.evaluate expr preq pes
    unfold TPE.apply₁
    sorry
    /-
    split
    case h_1 => apply Residual.WellTyped.error
    case h_2 =>
      cases h : expr_eval.asValue with
      | some v =>
        simp only [someOrError]
        split
        case h_2 =>
          apply Residual.WellTyped.error
        case h_1 v ty ox x v₂ heq =>
          unfold Spec.apply₁ at heq
          split at heq
          any_goals
            cases h_op
            simp only [Except.toOption, Option.some.injEq] at heq
            rw [← heq]
            exact well_typed_bool
          case h_2 =>
            simp only [Except.toOption, intOrErr] at heq
            rename Int64 => i
            cases h₂: i.neg?
            . rw [h₂] at heq
              simp at heq
            . rw [h₂] at heq
              simp only [Option.some.injEq] at heq
              rw [← heq]
              cases h_op
              exact well_typed_int
          case h_6 =>
           contradiction
      | none =>
        apply Residual.WellTyped.unaryApp
        case none.h₁ =>
          exact h_expr_wt
        case none.h₂ =>
          cases h_op
          all_goals
            first
            | apply UnaryResidualWellTyped.not
            | apply UnaryResidualWellTyped.neg
            | apply UnaryResidualWellTyped.isEmpty
            | apply UnaryResidualWellTyped.like
            | apply UnaryResidualWellTyped.is
            rw [partial_eval_preserves_typeof _ h_expr]
            assumption
            -/
