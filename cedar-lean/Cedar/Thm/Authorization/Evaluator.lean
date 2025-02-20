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
  | .ext e => .ext e
  | .set (.mk vs) => .set (vs.map₁ λ ⟨v, _⟩ => Value.toExpr v)
  | .record (.mk avs) => .record (avs.attach₃.map λ ⟨(k, v), _⟩ => (k, Value.toExpr v))

inductive Value.WellFormed : Value -> Prop
  | prim_wf (p : Prim) : Value.WellFormed (.prim p)
  | ext_wf (e : Ext) : Value.WellFormed (.ext e)
  | set_wf (s : Set Value)
    (h₁ : ∀ t, t ∈ s → Value.WellFormed t)
    (h₂ : s.WellFormed) :
    Value.WellFormed (.set s)
  | record_wf (m : Map Attr Value)
    (h₁ : ∀ a t, (a, t) ∈ m.kvs → Value.WellFormed t)
    (h₂ : m.WellFormed):
    Value.WellFormed (.record m)

theorem evaluate_value_toExpr_eq (v : Value) {req : Request} {es : Entities} :
  Value.WellFormed v → evaluate (Value.toExpr v) req es = .ok v
:= by
  intro h₁
  induction v using Value.toExpr.induct
  case case1 | case2 =>
    simp [Value.toExpr, evaluate]
  case case3 vs ih =>
    simp only [Value.toExpr, evaluate]
    cases h₁
    rename_i h₁ h₂
    have h₃ : ((vs.map₁ λ x => Value.toExpr x.val).mapM₁ λ x => evaluate x.val req es) = .ok vs := by
      rw [List.mapM₁_eq_mapM λ x => evaluate x req es]
      simp only [List.map₁, List.map_subtype, List.unattach_attach, List.mapM_map_eq_mapM]
      rw [List.mapM_ok_iff_forall₂, List.forall₂_iff_map_eq, List.map_eq_map_iff]
      intro v hv
      specialize h₁ v
      rw [← Set.in_list_iff_in_mk] at h₁
      exact ih v hv (h₁ hv)
    simp only [h₃, Except.bind_ok, Except.ok.injEq, Value.set.injEq]
    simp only [Set.WellFormed] at h₂
    rw [h₂]
    simp only [Set.toList]
  case case4 avs ih =>
    simp only [Value.toExpr, evaluate]
    cases h₁
    rename_i h₁ h₂
    have h₃ : ((List.map (λ x => (x.1.fst, Value.toExpr x.1.snd)) avs.attach₃).mapM₂
      λ x => bindAttr x.1.fst (evaluate x.1.snd req es)) = .ok avs := by
      rw [List.attach₃, List.map_pmap_subtype λ (x : Attr × Value) => (x.fst, Value.toExpr x.snd)]
      rw [List.mapM₂, List.attach₂, List.mapM_pmap_subtype λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd req es)]
      rw [List.mapM_map_eq_mapM, List.mapM_ok_iff_forall₂, List.forall₂_iff_map_eq,  List.map_eq_map_iff]
      intro (a, v) hv
      specialize h₁ a v
      simp only [Map.kvs, hv, forall_const] at h₁
      replace hv := List.sizeOf_snd_lt_sizeOf_list hv
      simp only at hv
      specialize ih a v (by simp only; omega) h₁
      simp only [bindAttr, ih, Except.bind_ok]
    simp only [h₃, Except.bind_ok, Except.ok.injEq, Value.record.injEq]
    simp only [Map.WellFormed] at h₂
    rw [h₂]
    simp only [Map.toList]

end Cedar.Thm
