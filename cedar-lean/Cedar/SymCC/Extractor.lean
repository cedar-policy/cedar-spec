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

import Cedar.SymCC.Enforcer
import Cedar.SymCC.Concretizer
import Cedar.SymCC.Interpretation


/-!
# Extracting strongly well-formed counterexamples to verification queries

This file defines the function `extract?`, which turns interpretations
into concrete, strongly well-formed counterexamples to verification queries.

The function takes as input a list of expressions `xs`, an interpretation `I`,
and a symbolic environment `εnv`.  Given these inputs, it returns an environment
`env ∈ εnv` such that `env` is strongly well-formed, and each term in
`footprint xs εnv` has the same interpretation under both `I` and every `I'`
for which f `env ∼ εnv.interpret I'`.

If `I` is the result of solving a `verify*` query (see Cedar.SymCC.Verifier),
then `εnv.extract? xs I` is a valid strongly well-formed counterexample
to that query. More generally, `εnv.extract? xs I` extracts such a
counterexample for any verification query that is expressed as a boolean
combination of (boolean) terms obtained by compiling `xs` with respect to `εnv`.

See `Cedar.Thm.SymCC.Verification` for how this is used to prove that verification
queries based on Cedar's compiler and hierarchy enforcer are correct.
-/

namespace Cedar.SymCC

open Data Factory Spec

def UnaryFunction.uuf? : UnaryFunction → Option UUF
  | .uuf f => .some f
  | _      => .none

def SymEntityData.uufAncestors (δ : SymEntityData) : Set UUF :=
  Set.make (δ.ancestors.toList.filterMap (UnaryFunction.uuf? ∘ Prod.snd))

def SymEntities.uufAncestors (εs : SymEntities) : Set UUF :=
  εs.toList.mapUnion (SymEntityData.uufAncestors ∘ Prod.snd)

def UUF.repairAncestors (fts : Set EntityUID) (I : Interpretation) (f : UUF) : UDF :=
  let udf := I.funs f
  ⟨udf.arg, udf.out, table udf, default udf⟩
where
  entry (udf : UDF) (uid : EntityUID) : Option (Term × Term) :=
    let t := Term.entity uid
    if t.typeOf = udf.arg then .some (t, app (.udf udf) t) else .none
  table (udf : UDF) : Map Term Term :=
     Map.mk (fts.elts.filterMap (entry udf))
  default (udf : UDF) : Term :=
    match udf.out with
    | .set ty => .set Set.empty ty
    | _       => udf.default

def Interpretation.repair (footprint : Set Term) (εnv : SymEnv) (I : Interpretation) : Interpretation :=
  ⟨I.vars, funs, I.partials⟩
  where
    footprintUIDs : Set EntityUID :=
      footprint.elts.mapUnion (Term.entityUIDs ∘ (Term.interpret I))
    footprintAncestors : Map UUF UDF :=
      Map.mk (εnv.entities.uufAncestors.elts.map λ f => (f, f.repairAncestors footprintUIDs I))
    funs : UUF → UDF :=
      λ f => if let .some udf := footprintAncestors.find? f then udf else I.funs f

def SymEnv.extract? (xs : List Expr) (I : Interpretation) (εnv : SymEnv) : Option Env :=
  concretize? (Expr.set xs) (εnv.interpret (I.repair (footprints xs εnv) εnv))

end Cedar.SymCC
