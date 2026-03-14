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
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

import Cedar.Thm.TPE.Soundness.Basic

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

set_option maxRecDepth 1024 in
theorem partial_evaluate_is_sound_unary_app
{x₁ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{op₁ : UnaryOp}
{ty : CedarType}
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es)) :
  Except.toOption ((Residual.unaryApp op₁ x₁ ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.unaryApp op₁ x₁ ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.apply₁]
  split
  case _ rv heq =>
    have heval := asResidualValue_evaluate heq req es
    rw [heval] at hᵢ₁
    -- LHS: (x₁.evaluate >>= Spec.apply₁ op₁).toOption
    -- RHS: (TPE.apply₁ op₁ (.val rv _) ty).evaluate.toOption
    -- = (match (op₁, rv) with ... | _ => .error ty).evaluate.toOption
    -- By hᵢ₁: x₁.evaluate.toOption = rv.evaluate.toOption
    -- Strategy: case split on x₁.evaluate
    simp only [Residual.evaluate, Except.toOption]
    cases hx : x₁.evaluate req es with
    | error =>
      simp only [Except.bind_err, Except.toOption]
      -- Goal: none = (match (op₁, rv) with ...).evaluate.toOption
      -- From hᵢ₁ and hx: none = rv.evaluate.toOption (via heval)
      -- Case split on rv:
      -- prim/set/ext: rv.evaluate = .ok _, so rv.evaluate.toOption = some _ ≠ none → contradiction
      -- record: all (op₁, .record m) → .error ty → toOption = none ✓
      have h_none : (rv.evaluate req es).toOption = none := by
        rw [hx] at hᵢ₁; simp only [Except.toOption] at hᵢ₁
        simp only [Except.toOption]; exact hᵢ₁.symm
      cases rv with
      | prim p =>
        have := @evaluate_asResidualValue (.prim p) req es
        simp [Value.asResidualValue, Except.toOption] at this h_none
      | set s =>
        have := @evaluate_asResidualValue (.set s) req es
        simp [Value.asResidualValue, Except.toOption] at this h_none
      | ext x =>
        have := @evaluate_asResidualValue (.ext x) req es
        simp [Value.asResidualValue, Except.toOption] at this h_none
      | record m => cases op₁ <;> simp [Residual.evaluate, Except.toOption]
    | ok v =>
      simp only [Except.bind_ok]
      -- From hᵢ₁: some v = rv.evaluate.toOption
      have hrv : rv.evaluate req es = .ok v := by
        simp only [hx, Except.toOption] at hᵢ₁
        cases h : rv.evaluate req es <;> simp_all
      -- Now show: (Spec.apply₁ op₁ v).toOption = (TPE result).evaluate.toOption
      -- The TPE result depends on (op₁, rv). Since rv.evaluate = .ok v,
      -- rv determines v. Case split on rv to determine v.
      cases rv with
      | prim p =>
        simp [ResidualValue.evaluate] at hrv; subst hrv
        cases op₁ <;> cases p <;>
          simp_all [Spec.apply₁, someOrError, Residual.evaluate, ResidualValue.evaluate,
            Except.toOption]
        -- neg.int case: someOrError (i.neg?) ty vs intOrErr (i.neg?)
        · rename_i i; cases h : i.neg? <;>
            simp [someOrError, intOrErr, Residual.evaluate, ResidualValue.evaluate, evaluate_asResidualValue, Except.toOption]
      | set s =>
        simp [ResidualValue.evaluate] at hrv; subst hrv
        cases op₁ <;> simp_all [Spec.apply₁, Residual.evaluate, ResidualValue.evaluate, Except.toOption]
      | ext x =>
        simp [ResidualValue.evaluate] at hrv; subst hrv
        cases op₁ <;> simp_all [Spec.apply₁, Residual.evaluate, ResidualValue.evaluate, Except.toOption]
      | record m =>
        have hv_rec : ∃ kvs, v = .record kvs := by
          simp only [ResidualValue.evaluate] at hrv
          cases hm : m.mapMKVsIntoValues₂ (fun x => ResidualValue.evaluateAttr x.val req es) with
          | error => simp [hm] at hrv
          | ok kvs => simp [hm] at hrv; exact ⟨kvs, hrv.symm⟩
        rcases hv_rec with ⟨kvs, hv_rec⟩; subst hv_rec
        cases op₁ <;> simp [Residual.evaluate, Spec.apply₁, Except.toOption]
  case _ =>
    split
    case _ heq =>
      -- error case
      simp only [Residual.evaluate, Except.toOption]
      rw [heq] at hᵢ₁
      simp only [Residual.evaluate, Except.toOption] at hᵢ₁
      cases hx : x₁.evaluate req es <;> simp_all
    case _ =>
      simp [Residual.evaluate]
      generalize h₅ : x₁.evaluate req es = res₁
      cases res₁ <;> simp [h₅] at hᵢ₁
      case error =>
        rcases to_option_left_err hᵢ₁ with ⟨_, hᵢ₁⟩
        simp [hᵢ₁, Except.toOption]
      case ok =>
        replace hᵢ₃ := to_option_left_ok' hᵢ₁
        simp [hᵢ₃]

end Cedar.Thm
