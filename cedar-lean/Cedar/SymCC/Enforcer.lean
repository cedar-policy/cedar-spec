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

import Cedar.SymCC.Compiler

/-!
This file defines the algorithm for emitting well-formedness assumptions about
Cedar hierarchies. A valid Cedar hierarchy graph is the irreflexive transitive
closure of a DAG.  (Note that the `in` operator is reflexive, but this is
enforced separately by the semantics, and it's not needed in the hierarchy.)

The generated assumptions are expressed as Terms that enforce the acyclicty and
transitivity constraints on the symbolic store, for a given Cedar expression.

The grounding relies on the fact that a Cedar expression can reference only a
finite number of entities (so the domain of the quantification is finite), and
we can compute an overapproximation of that set by statically analyzing the
expression. We call this set the _footprint_ of the expression `x`, and it
consists of all subexpressions of `x` that could have an Entity type. The
grounding procedure computes the footprint, and grounds the acyclicity and
transitivity constraints on the set of entity terms in the footprint.
-/

namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec
open Factory

/--
Returns the terms corresponding to subexpressions of `x` of the following form:

  * A variable term with an entity type
  * An entity reference literal
  * An attribute access expression with an entity type
  * A binary (`getTag`) expression with an entity type

These are the only basic expressions in Cedar that may evaluate to an entity.
All other expressions that evaluate to an entity are build up from the above
basic expresions.

All returned terms are of type `TermType.option .entity`.
-/
def footprint (x : Expr) (εnv : SymEnv) : Set Term :=
  match x with
  | .lit _
  | .var _             => ofEntity
  | .ite x₁ x₂ x₃      => ofBranch x₁ (footprint x₁ εnv) (footprint x₂ εnv) (footprint x₃ εnv)
  | .and x₁ x₂         => ofBranch x₁ (footprint x₁ εnv) (footprint x₂ εnv) Set.empty
  | .or x₁ x₂          => ofBranch x₁ (footprint x₁ εnv) Set.empty (footprint x₂ εnv)
  | .binaryApp _ x₁ x₂ => ofEntity ∪ footprint x₁ εnv ∪ footprint x₂ εnv
  | .getAttr x₁ _      => ofEntity ∪ footprint x₁ εnv
  | .hasAttr x₁ _
  | .unaryApp _ x₁     => footprint x₁ εnv
  | .call _ xs
  | .set xs            => xs.mapUnion₁ (λ ⟨xᵢ, _⟩ => footprint xᵢ εnv)
  | .record axs        => axs.mapUnion₂ (λ ⟨(_, xᵢ), _⟩ => footprint xᵢ εnv)
where
  ofEntity : Set Term :=
    match compile x εnv with
    | .ok t => if t.typeOf.isOptionEntityType then Set.singleton t else Set.empty
    | _     => Set.empty
  ofBranch (x₁ : Expr) (ft₁ ft₂ ft₃ : Set Term) : Set Term :=
    match compile x₁ εnv with
    | .ok (.some (.bool true))  => ft₂
    | .ok (.some (.bool false)) => ft₃
    | .ok _                     => ft₁ ∪ ft₂ ∪ ft₃
    | .error _                  => Set.empty

/--
Returns the set of Terms corresponding to the footprints of xs.
-/
def footprints (xs : List Expr) (εnv : SymEnv) : Set Term :=
  xs.mapUnion (footprint · εnv)

/--
Returns the acyclicity constraint for the given term.
-/
def acyclicity (t : Term) (εs : SymEntities) : Term :=
  match t.typeOf with
  | .option (.entity ety) =>
    match εs.ancestorsOfType ety ety with
    | .some f =>
      let t' := option.get t
      implies (isSome t) (not (set.member t' (app f t')))
    | .none   => true
  | _ => true

/--
Returns the transitivity constraint for the given term.
-/
def transitivity (t₁ t₂ : Term) (εs : SymEntities) : Term :=
  if t₁ = t₂
  then true
  else
    match t₁.typeOf, t₂.typeOf with
    | .option (.entity ety₁), .option (.entity ety₂) =>
      match εs.ancestorsOfType ety₁ ety₂, εs.ancestors ety₂ with
      | .some f₁₂, .some anc₂ =>
        let t₁' := option.get t₁
        let t₂' := option.get t₂
        implies (isAncestor t₂' t₁' f₁₂) (areAncestors t₂' anc₂ t₁' ety₁)
      | _, _ => true
    | _, _ => true
where
  isAncestor t₂' t₁' f₁₂ :=                               -- t₂' ∈ f₁₂ t₁'
    and (and (isSome t₁) (isSome t₂)) (set.member t₂' (app f₁₂ t₁'))
  areAncestorsOfType t₂' f₂₃ ety₃ t₁' ety₁ :=
    match εs.ancestorsOfType ety₁ ety₃ with
    | .some f₁₃ => set.subset (app f₂₃ t₂') (app f₁₃ t₁') -- f₂₃ t₂' ⊆ f₁₃ t₁'
    | .none     => set.isEmpty (app f₂₃ t₂')              -- f₁₃ t₁' = ∅
  areAncestors t₂' (anc₂ : Map EntityType UnaryFunction) t₁' ety₁ :=
    anc₂.kvs.foldl (λ acc ⟨ety₃, f₂₃⟩ => and acc (areAncestorsOfType t₂' f₂₃ ety₃ t₁' ety₁)) (.prim (.bool true))

/--
Returns the ground acyclicity and transitivity assumptions for xs and env.
-/
def enforce (xs : List Expr) (εnv : SymEnv) : Set Term :=
  let ts := footprints xs εnv
  let ac := ts.elts.map (acyclicity · εnv.entities)
  let tr := ts.elts.flatMap (λ t => ts.elts.map (transitivity t · εnv.entities))
  Set.make (ac ∪ tr)

namespace Cedar.SymCC
