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
import Lean
import Lean.Elab
import Lean.Elab.Term
import Lean.Meta.Basic

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Lean Elab Tactic Meta
open Lean.Elab.Term
open Lean.Elab.Tactic

def replaceValProjRec (e: Lean.Expr) : MetaM Lean.Expr :=
do
  match e with
  | .proj _name 0 (.bvar 0) =>
    return (.bvar 0)
  | (.app (.app (.app (.const ``Subtype.val _) _) _) (.bvar 0)) =>
    return (.bvar 0)
  | .proj name id child =>
  let child' ← replaceValProjRec child
  return (.proj name id child')
  | .app f a =>
      let f' ← replaceValProjRec f
      let a' ← replaceValProjRec a
      return (.app f' a')
  | _ =>  return e



def fixupPmapType (ty : Lean.Expr) : Lean.Expr :=
  match ty with
  | (.app (.app (.const ``Subtype _) ty1) _ty2) =>
    ty1
  | _ =>
    ty


def replaceValProj (e : Lean.Expr) : MetaM Lean.Expr := do
  match e with
  | .lam n t b d => do
    let t' := fixupPmapType t
    let b' ← replaceValProjRec b
    return .lam n t' b' d
  | e' => return e'

def findMapPmapPattern (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  dbg_trace "{toString e}"
  match e with
  | (.app (.app (.app (.app (.const ``List.map _) _) _) f)
          (.app (.app (.app (.app (.app (.app (.const ``List.pmap _) _) _) _) _) _ls) _)) => do
    return f
  | (.app (.app (.app (.app (.app (.app (.const ``List.mapM _) _) _) _) _) f)
          (.app (.app (.app (.app (.app (.app (.const ``List.pmap _) _) _) _) _) _ls) _)) => do
    return f
  | .app f a => do
    if let some res ← findMapPmapPattern f then return res
    if let some res ← findMapPmapPattern a then return res
    return none
  | .mdata _data expr => do
    if let some res ← findMapPmapPattern expr then return res
    return none
  | _ => return none


elab "find_pmap_func" x:ident : tactic => do
  let target ← getMainTarget
  match (← withMainContext <| findMapPmapPattern target) with
  | some f => do
    let body' ← replaceValProj f
    let inferred ← Lean.Meta.inferType body'
    liftMetaTactic fun mvarId => do
      let mvarIdNew ← mvarId.define x.getId inferred body'
      let (_, mvarIdNew) ← mvarIdNew.intro1P
      return [mvarIdNew]
  | none => throwError "No subexpression of the form 'List.map (fun x => ...) (List.pmap Subtype.mk ...)' found (nor using List.mapM)"


/--
  A tactic that automatically converts calls like `map₁`,
  `map₂`, `mapM₁`, `mapM₂` to corresponding `map` or `mapM`
  calls. This helps proofs ignore annotations used
  for termination proofs.

  The tactic works by
  1. Unfolding things like mapM₁, mapM₂, attach, ect
  2. Finding an opportunity for simplification (a map on a pmap)
  3. Rewritting using List.map_pmap_subtype and the simplified function.

  If the tactic fails, you can try doing simplification first to expose these opportunities or using `find_pmap_func` to see what the computed function is.
-/
elab "auto_map₁_to_map" : tactic => do
  let found ← Lean.mkFreshId
  let foundId := Lean.mkIdent found
  withMainContext do
    evalTactic (← `(tactic|
      try simp only [List.mapM₁, List.attach, List.attach₂, List.mapM₂, List.mapM₁, List.attachWith, List.map₁];;
      find_pmap_func $foundId;
      try rw [List.mapM_pmap_subtype $foundId];
      ))
    evalTactic (← `(tactic| try rw [List.map_pmap_subtype $foundId]))
    evalTactic (← `(tactic| subst $foundId))


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
    repeat auto_map₁_to_map
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
  | record map ty =>
    unfold TypedExpr.toExpr
    simp [TypedExpr.toExpr, TypedExpr.toResidual, Spec.evaluate, Residual.evaluate]
    congr 1
    repeat auto_map₁_to_map
    unfold bindAttr
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
    congr 1
    repeat auto_map₁_to_map
    rw [List.mapM_then_map_combiner, List.mapM_then_map_combiner]
    rw [List.forall₂_implies_mapM_eq]
    induction args
    case _ =>
      simp
    case _ ih =>
      simp
      constructor
      case left =>
        apply conversion_preserves_evaluation
      case right =>
        apply ih
termination_by sizeOf te
decreasing_by
  any_goals
    simp;
    try omega;
  case _ =>
    sorry
  case _ =>
    sorry
  case _ =>
    sorry




end Cedar.TPE
