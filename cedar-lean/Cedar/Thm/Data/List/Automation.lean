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


import Cedar.Thm.Data.List.Basic
import Cedar.Thm.Data.List.Lemmas
import Cedar.Data.List

namespace List

open Cedar.Data


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



/-- TODO there has to be an easier way to do this without a macro -/
syntax "try_unfold_each" "[" ident,* "]" : tactic
macro_rules
  | `(tactic| try_unfold_each [$t,*]) => do
    match t.getElems.toList with
    | [] => `(tactic| skip)
    | head :: tail =>
      let tailArr := Syntax.TSepArray.mk tail.toArray
      `(tactic| (try unfold $head); (try_unfold_each [$tailArr,*]))

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
      -- try simplifying 3 times to unwrap layers of calls
      (try unfold List.attachWith); (try unfold List.mapM₁); (try unfold List.attach); (try unfold List.attach₂); (try unfold List.mapM₂); (try unfold List.mapM₁); (try unfold List.map₁); (try unfold List.attach);
      (try unfold List.attachWith); (try unfold List.mapM₁); (try unfold List.attach); (try unfold List.attach₂); (try unfold List.mapM₂); (try unfold List.mapM₁); (try unfold List.map₁); (try unfold List.attach);
      find_pmap_func $foundId;
      (first | rw [List.mapM_pmap_subtype $foundId] | rw [List.map_pmap_subtype $foundId]);
      subst $foundId
      ))
