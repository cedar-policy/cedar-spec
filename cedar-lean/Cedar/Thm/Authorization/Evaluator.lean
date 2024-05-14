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

import Cedar.Spec
import Cedar.Thm.Data.Control

/-!
This file contains useful lemmas about the `Evaluator` functions.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Data


theorem and_true_implies_left_true {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate (Expr.and e₁ e₂) request entities = .ok true →
  evaluate e₁ request entities = .ok true
:= by
  intro h₁
  simp [evaluate, Result.as] at h₁
  generalize h₂ : (evaluate e₁ request entities) = r₁
  simp [h₂] at h₁
  cases r₁ <;> simp at h₁
  case ok v₁ =>
    generalize h₃ : (Coe.coe v₁ : Result Bool) = rb
    simp [h₃] at h₁
    cases rb <;> simp at h₁
    case ok b =>
      cases b <;> simp at h₁
      simp [Coe.coe, Value.asBool] at h₃
      cases v₁ <;> try simp at h₃
      case _ p₁ =>
        cases p₁ <;> simp at h₃
        simp [h₃]

theorem and_true_implies_right_true {e₁ e₂ : Expr} {request : Request} {entities : Entities} :
  evaluate (Expr.and e₁ e₂) request entities = .ok true →
  evaluate e₂ request entities = .ok true
:= by
  intro h₁
  have h₂ := and_true_implies_left_true h₁
  simp [evaluate, h₂, Result.as, Coe.coe, Value.asBool] at h₁
  generalize h₃ : (evaluate e₂ request entities) = r₂
  simp [h₃] at h₁
  cases r₂ <;> simp only [Except.bind_err] at h₁
  case ok v₂ =>
    cases v₂ <;> try simp only [Except.bind_err] at h₁
    case _ p₂ =>
      cases p₂ <;> simp only [Except.bind_ok, Except.bind_err] at h₁
      case _ b =>
        cases b
        case false =>
          simp only [pure, Except.pure, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq] at h₁
        case true => rfl

/- some shorthand to make things easier to read and write -/
/--
  `producesBool` means the expression evaluates to a bool (and not an error)
-/
def producesBool (e : Expr) (request : Request) (entities : Entities) : Prop :=
  match (evaluate e request entities) with
  | .ok (.prim (.bool _)) => true
  | _ => false
/--
  `producesNonBool` means the expression evaluates to a non-bool (and not an error)
-/
def producesNonBool (e : Expr) (request : Request) (entities : Entities) : Prop :=
  match (evaluate e request entities) with
  | .ok (.prim (.bool _)) => false
  | .error _ => false
  | _ => true

/--
  If an `and` expression results in an error, it's because either:
  - the left subexpression had that error
  - the right subexpression had that error (and the left subexpression evaluated to .ok true)
  - the left subexpression evaluated to .ok with a non-bool
  - the right subexpression evaluated to .ok with a non-bool (and the left subexpression evaluated to .ok true)
-/
theorem ways_and_can_error {e₁ e₂ : Expr} {request : Request} {entities : Entities} {err : Error} :
  evaluate (Expr.and e₁ e₂) request entities = .error err →
  evaluate e₁ request entities = .error err ∨
  (evaluate e₁ request entities = .ok true ∧ evaluate e₂ request entities = .error err) ∨
  (err = Error.typeError ∧ producesNonBool e₁ request entities) ∨
  (err = Error.typeError ∧ evaluate e₁ request entities = .ok true ∧ producesNonBool e₂ request entities)
:= by
  intro h₁
  cases h_e₁ : (evaluate e₁ request entities) <;> simp [h_e₁, producesNonBool]
  case ok val =>
    cases val <;>
    simp [h_e₁, evaluate, Result.as, Coe.coe, Value.asBool] at h₁ <;>
    simp [h₁]
    case prim prim =>
      cases prim <;>
      simp [h_e₁] at h₁ <;>
      simp [h₁]
      case bool b =>
        cases b with
        | true =>
          simp only [true_and]
          simp only [h_e₁] at h₁
          cases h_e₂ : (evaluate e₂ request entities) with
          | ok val =>
            cases val <;>
            simp [h_e₂, evaluate, Result.as, Value.asBool, pure, Except.pure] at h₁ <;>
            simp [h₁]
            case prim prim =>
              cases prim <;>
              simp [h_e₂] at h₁ <;>
              simp [h₁]
          | error e =>
            simp only [h_e₂, ↓reduceIte, Except.bind_err, Except.error.injEq] at h₁
            simp [h₁]
        | false => simp [h_e₁] at h₁
  case error e =>
    simp [h_e₁, evaluate, Result.as, Coe.coe, Value.asBool] at h₁
    simp [h₁]

/--
  Every `and` expression produces either .ok bool or .error
-/
theorem and_produces_bool_or_error (e₁ e₂ : Expr) (request : Request) (entities : Entities) :
  match (evaluate (Expr.and e₁ e₂) request entities) with
  | .ok (.prim (.bool _)) => true
  | .error _ => true
  | _ => false
:= by
  cases h : evaluate (Expr.and e₁ e₂) request entities <;> simp
  case ok val =>
    cases val
    <;> simp only [evaluate, Result.as, Coe.coe, Value.asBool, Bool.not_eq_true', pure, Except.pure] at h
    <;> generalize (evaluate e₁ request entities) = r₁ at h
    <;> generalize (evaluate e₂ request entities) = r₂ at h
    case prim prim =>
      cases prim <;> simp
      case int | string | entityUID =>
        split at h <;> split at h <;> simp only [Except.bind_ok, Except.bind_err] at h
        split at h
        case _ => simp only [Except.ok.injEq, Value.prim.injEq] at h
        case _ =>
          split at h
          case _ => split at h <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Value.prim.injEq] at h
          case _ => simp only [Except.bind_err] at h
    case set | record | ext =>
      exfalso
      split at h <;> split at h <;> simp only [Except.bind_ok, Except.bind_err] at h
      split at h
      case _ => simp only [Except.ok.injEq] at h
      case _ =>
        split at h
        case _ => split at h <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq] at h
        case _ => simp only [Except.bind_err] at h

/--
  Corollary of the above:
  Evaluating a policy produces either .ok bool or .error
-/
theorem policy_produces_bool_or_error (p : Policy) (request : Request) (entities : Entities) :
  match (evaluate p.toExpr request entities) with
  | .ok (.prim (.bool _)) => true
  | .error _ => true
  | _ => false
:= by
  unfold Policy.toExpr
  apply and_produces_bool_or_error

end Cedar.Thm
