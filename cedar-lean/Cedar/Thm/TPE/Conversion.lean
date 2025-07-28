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

import Cedar.Spec.Evaluator
import Cedar.TPE.Residual
import Cedar.TPE.Evaluator
import Cedar.Validation.TypedExpr
import Cedar.Thm.Data.List.Lemmas

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
Theorem stating that converting a TypedExpr to a Residual preserves evaluation semantics.
That is, evaluating the original TypedExpr (converted to Expr) gives the same result
as evaluating the converted Residual.
-/
theorem conversion_preserves_evaluation (te : TypedExpr) (req : Request) (es : Entities) :
  Spec.evaluate te.toExpr req es = (TypedExpr.toResidual te).evaluate req es := by
  cases te with
  | lit p ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
  | var v ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    cases v <;> simp [Spec.evaluate, Residual.evaluate]
  | ite cond thenExpr elseExpr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_cond := conversion_preserves_evaluation cond req es
    have ih_then := conversion_preserves_evaluation thenExpr req es
    have ih_else := conversion_preserves_evaluation elseExpr req es
    rw [←ih_cond]
    simp [Result.as, Value.asBool]
    rw [←ih_then, ←ih_else]
    cases Spec.evaluate cond.toExpr req es
    case ite.error =>
      simp
    case ite.ok =>
      simp
      rename_i a
      cases a
      case prim =>
        simp [bind, Coe.coe, Value.asBool]
      all_goals {
        simp [Coe.coe, Value.asBool]
      }
  | and a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | or a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | unaryApp op expr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | binaryApp op a b ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih_a := conversion_preserves_evaluation a req es
    have ih_b := conversion_preserves_evaluation b req es
    rw [←ih_a, ←ih_b]
  | getAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | hasAttr expr attr ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    have ih := conversion_preserves_evaluation expr req es
    rw [←ih]
  | set ls ty =>
    unfold TypedExpr.toExpr
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    rw [List.map₁_eq_map, List.map₁_eq_map]
    have h : (fun x : { x // x ∈ List.map TypedExpr.toExpr ls } => Spec.evaluate x.val req es) = (fun x => ((fun y => Spec.evaluate y req es) x.val)) := by {
      simp
    }
    rw [h]
    rw [List.mapM₁_eq_mapM (fun y => Spec.evaluate y req es)]
    have h₂ : (List.map TypedExpr.toResidual ls).mapM₁ (fun x => x.val.evaluate req es) = (List.map TypedExpr.toResidual ls).mapM₁ (fun x => ((fun y => y.evaluate req es) x.val)) := by simp
    rw [List.mapM₁_eq_mapM (fun y => Residual.evaluate y req es)]
    rw [List.mapM_then_map_combiner, List.mapM_then_map_combiner]
    rw [List.forall₂_implies_mapM_eq]
    induction ls
    case set.e_a.a.nil =>
      simp
    case _ ih =>
      simp
      constructor
      case left =>
        apply conversion_preserves_evaluation
      case right =>
        apply ih
        simp
        simp
  | record map ty =>
    unfold TypedExpr.toExpr
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    unfold List.attach₂
    rw [List.map_pmap_subtype (fun y => (y.fst, y.snd.toExpr)) map]
    unfold List.mapM₂
    unfold List.attach₂
    unfold bindAttr
    simp
    rw [List.mapM_pmap_subtype (fun x => Prod.mk x.fst <$> Spec.evaluate x.snd req es) (List.map (fun y => (y.fst, y.snd.toExpr)) map)]
    rw [List.mapM_pmap_subtype (fun x => Prod.mk x.fst <$> x.snd.evaluate req es) (List.map (fun x => (x.1.fst, TypedExpr.toResidual x.1.snd)) (List.pmap Subtype.mk map _))]
    rw [List.map_pmap_subtype (fun x => (x.fst, TypedExpr.toResidual x.snd)) map]
    rw [List.mapM_then_map_combiner, List.mapM_then_map_combiner]
    simp
    rw [List.forall₂_implies_mapM_eq]
    induction map
    case _ =>
      simp
    case _ ih =>
      simp
      constructor
      case left =>
        apply conversion_preserves_evaluation
      case right =>
        apply ih
  | call xfn args ty =>
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    sorry

end Cedar.TPE
