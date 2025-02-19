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
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Set
import Cedar.Thm.Data.Map
import Cedar.Thm.Data.LT
import Cedar.Data.SizeOf

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
  simp only [evaluate, Result.as, h₂, Coe.coe, Value.asBool, Bool.not_eq_eq_eq_not, Bool.not_true,
    bind_pure_comp, Except.bind_ok, Bool.true_eq_false, ↓reduceIte] at h₁
  generalize h₃ : (evaluate e₂ request entities) = r₂
  simp only [h₃] at h₁
  cases r₂
  case error => simp only [Except.map_error, reduceCtorEq] at h₁
  case ok v₂ =>
    cases v₂ <;> try simp only [Except.map_error, reduceCtorEq] at h₁
    case _ p₂ =>
      cases p₂ <;> simp only [Except.map_error, Except.bind_ok, Except.bind_err, reduceCtorEq] at h₁
      case bool b =>
        cases b
        case false =>
          simp only [Except.map_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
            Bool.false_eq_true] at h₁
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
          simp only [h_e₁, reduceCtorEq] at h₁
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
            simp only [↓reduceIte, h_e₂, Except.map_error, Except.error.injEq] at h₁
            simp only [h₁, and_false, or_false]
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
        split at h <;> split at h <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at h
        split at h
        case _ => simp only [Except.ok.injEq, Value.prim.injEq, reduceCtorEq] at h
        case _ =>
          split at h
          case _ => split at h <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, Value.prim.injEq, reduceCtorEq] at h
          case _ => simp only [Except.bind_err, reduceCtorEq] at h
    case set | record | ext =>
      exfalso
      split at h <;> split at h <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at h
      split at h
      · simp only [Except.ok.injEq, reduceCtorEq] at h
      · split at h
        · split at h <;> simp only [Except.bind_ok, Except.bind_err, Except.ok.injEq, reduceCtorEq] at h
        · simp only [Except.bind_err, reduceCtorEq] at h

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

def Value.toExpr : Value → Expr
  | .prim p => .lit p
  | .set s => .set $ s.elts.map₁ λ ⟨v, _⟩ ↦ Value.toExpr v
  | .record m => .record $ m.kvs.attach₂.map λ ⟨(k, v), _⟩ ↦ (k, Value.toExpr v)
  | .ext e => .ext e
decreasing_by
  all_goals simp_wf
  case _ h₁ => -- set
    have := Set.sizeOf_lt_of_mem h₁
    omega
  case _ h₁ => -- record
    simp only at h₁
    have := Map.sizeOf_lt_of_kvs m
    omega

inductive Value.WellFormed : Value -> Prop
  | prim_wf (p : Prim) : Value.WellFormed (.prim p)
  | ext_wf (e : Ext) : Value.WellFormed (.ext e)
  | set_wf (s : Set Value)
    (h₁ : ∀ t, t ∈ s → Value.WellFormed t)
    (h₂ : s.WellFormed) :
    Value.WellFormed (.set s)
  | record_wf (m : Map Attr Value)
    (h₁ : ∀ t, (a, t) ∈ m.kvs → Value.WellFormed t)
    (h₂ : m.WellFormed):
    Value.WellFormed (.record m)

theorem evaluate_value_roundtrip (v : Value) {req : Request} {es : Entities} :
  Value.WellFormed v → evaluate (Value.toExpr v) req es = .ok v
:= by
  cases v <;> intro h
  case prim | ext =>
    simp only [Value.toExpr, evaluate]
  case set =>
    simp only [Value.toExpr, evaluate]
    rename_i s
    cases h with
    | set_wf _ hₐ hₛ =>
    have h₁ : ∀ (x : { x : Value // x ∈ s.elts }),
      evaluate (Value.toExpr x.val) req es = Except.ok x.val := by
      intro x
      have hₜ : sizeOf x.val < 1 + sizeOf s := by
        have := Set.sizeOf_lt_of_mem x.property
        omega
      exact evaluate_value_roundtrip x.val (hₐ x.val x.property)
    have h₂ : ((s.elts.map₁ fun x => Value.toExpr x.val).mapM₁ fun x => evaluate x.val req es)
             = Except.ok s.elts := by
      apply List.map₁_mapM₁_chain s.elts Value.toExpr (λ x => evaluate x req es)
      intro x
      exact h₁ x
    rw [h₂]
    simp
    simp only [Set.WellFormed, Set.toList] at hₛ
    symm
    exact hₛ
  case record =>
    simp only [Value.toExpr, evaluate, bindAttr]
    rename_i m
    cases h with
    | record_wf _ hₐ hₘ =>
    rename_i a

    have hₑ : (List.map (fun x => (x.1.fst, Value.toExpr x.1.snd)) m.kvs.attach₂) = m.kvs.map (λ x => (x.fst, Value.toExpr x.snd)) := by
      exact List.map_attach₂ (fun x => (x.fst, Value.toExpr x.snd))
    rw [hₑ]
    have hₑ₁ : ((List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs).mapM₂ fun x => do
          let v ← evaluate x.1.snd req es
          Except.ok (x.1.fst, v)) =
          ((List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs).mapM fun x => do
          let v ← evaluate x.snd req es
          Except.ok (x.fst, v)) := by

      have hₓ := List.mapM₂_eq_mapM (fun x : Attr × Expr => do
          let v ← evaluate x.snd req es
          Except.ok (x.fst, v))
      have hₖ := hₓ (List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs)

      rw [hₖ]



      --have hₑ₂ : x ∈ List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs →
    --sizeOf x.snd < 1 + sizeOf (List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs) := by
      --sorry

      simp only [List.mapM₂, List.attach₂]
      --have hₓ : (List { x : Attr × Expr // sizeOf x.snd < 1 + sizeOf (List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs) }) := ((List.pmap Subtype.mk (List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs) (fun x => List.sizeOf_snd_lt_sizeOf_list : ∀ (x : Attr × Expr),
  --x ∈ List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs →
    --sizeOf x.snd < 1 + sizeOf (List.map (fun x => (x.fst, Value.toExpr x.snd)) m.kvs))))
    rw [hₑ₁]
    have h₁ : ∀ (x : { x // (a, x) ∈ m.kvs }),
      evaluate (Value.toExpr x.val) req es = Except.ok x.val := by
      intro x
      have hₜ : sizeOf x.val < 1 + sizeOf m := by
        have hₜ₁ := Map.sizeOf_lt_of_value x.property
        simp only [Map.WellFormed, Map.toList] at hₘ
        have hₜ₂ : sizeOf m = sizeOf (Map.mk m.kvs) := by
          rw [hₘ]
        omega
      exact evaluate_value_roundtrip x.val (hₐ x.val x.property)

    sorry
termination_by sizeOf v

end Cedar.Thm
