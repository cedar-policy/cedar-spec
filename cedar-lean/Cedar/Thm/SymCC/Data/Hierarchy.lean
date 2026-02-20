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

import Cedar.Thm.SymCC.Data.Basic

/-!
# Strongly well-formed ancestor relations

The Cedar specification requires the entity hierarchy to be a DAG. This means
that a legal `ancestor` relation on entities is the transitive closure of a DAG:
it is (1) acyclic and (b) transitive.

This file formalizes the hierarchy requirements on the `ancestor` relation as
extra constraints on well-formed `Entities`.  A set of `Entities` is _strongly
well-formed_ if it satisfies the `WellFormed` predicate, as well as the
`Acyclic` and `Transitive` predicate on its `ancestor` relation.

We apply the same notion of strong well-formedness to symbolic environments.
Specifically, if an Entity type is enumerated (such as Cedar's action), then the
concrete the ancestor relation over that type must be concrete, acyclic, and
transitive. Moreover, an enumerated type can only have other enumerated types as
ancestors, and a non-enumerated type can only have other non-enumerated types as
ancestors.  These constraints are enforced for actions, and we will continue to
enforce them for other enums in the future.

If needed, we could allow enumerated types to have arbirary entities as parents,
but at the cost of generating more assumptions and complicating the proofs.
Specifically, to lift this restriction, we need to the following:
  * Change the definition of `footprints` to include all members of every
    enumerated type, which will cause transitivity and acyclicity constraints to
    be generated for these members along with the entities referenced in the
    analyzed policies.
  * Change the definition of `SameEntities es εs` so that `es` includes all
    enumerated values from `εs`.  This is necessary to show soundness of
    assumption generation (see `mem_footprint_reduce_exists_swf`; similar lemma
    must hold for enumerated entities that would be included in the footprint).
    This will require adjusting the proof that the result of `concretize?`
    matches the input symbolic environment according to the new stricter
    definition of `SameEntities`.  (It does, but this needs to be proven.)
  * Drop the hierarchy assumptions defined in this file.  They become
    unnecessary since they are checked / enforced by the assumption generator.
  * Adjust the proofs of assumption generation soundness and completeness. These
    proofs should become more uniform in that they can treat UDFs and UUFs
    symmetrically.

We use strong well-formedness to prove the correctness of Cedar's assumption
generation (`Cedar.SymCC.Enforcer.enforce`).  Specifically, the assumptions
are weak enough to be satisfied by all well-formed `ancestor` relations.  And
they are strong enough to be satisfied only by (finite) well-formed `ancestor`
relations.

Finally, strongly well-formed environments also restrict the shape of the
symbolic request. Specifically, the terms to which the request variables must be
either variables or literals. They cannot be arbitrary terms because we need to
be able to show that every "get attribute" term in the encoding corresponds to a
"get attribute" expression in an input policy. This means that request terms
cannot include spurious "get attribute" subterms.  Note that we can relax this
strong well-formedness constraint on the `context` term to allow combination of
variables and literals, similar to the partial evaluator.  This would complicate
proofs so we won't do it until we find a use case for this functionality.

See `Cedar/Thm/Verification.lean` for an example of how these definitions are
used to prove soundness and completeness of the
`Cedar.SymCC.Verifier.verifyEquivalent` query, which checks that two Cedar
policies are equivalent on all strongly well-formed environments `env`
represented by a given symbolic environment `εnv`.
-/

namespace Cedar.Spec

open Data

def Entities.Acyclic (es : Entities) : Prop :=
  ∀ uid d, es.find? uid = .some d → uid ∉ d.ancestors

def Entities.Transitive (es : Entities) : Prop :=
  ∀ uid₁ d₁ uid₂ d₂,
    es.find? uid₁ = .some d₁ →
    es.find? uid₂ = .some d₂ →
    uid₂ ∈ d₁.ancestors →
    d₂.ancestors ⊆ d₁.ancestors

def Entities.Hierarchical (es : Entities) : Prop :=
  es.Acyclic ∧ es.Transitive

def Entities.StronglyWellFormed (es : Entities) : Prop :=
  es.WellFormed ∧ es.Hierarchical

def Env.StronglyWellFormed (env : Env) : Prop :=
  env.request.WellFormed env.entities ∧
  env.entities.StronglyWellFormed

def Env.StronglyWellFormedFor (env : Env) (x : Expr) : Prop :=
  env.StronglyWellFormed ∧
  env.entities.ValidRefsFor x

def Env.StronglyWellFormedForAll (env : Env) (xs : List Expr) : Prop :=
  env.StronglyWellFormed ∧
  ∀ x ∈ xs, env.entities.ValidRefsFor x

def Env.StronglyWellFormedForPolicy (env : Env) (p : Policy) : Prop :=
  env.StronglyWellFormedFor p.toExpr

def Env.StronglyWellFormedForPolicies (env : Env) (ps : Policies) : Prop :=
  env.StronglyWellFormedForAll (ps.map Policy.toExpr)

end Cedar.Spec

namespace Cedar.SymCC

open Data Factory Spec

def SymEntityData.isEnum (δ : SymEntityData) : Bool :=
  δ.members.isSome

def SymEntityData.ConcreteAncestors (δ : SymEntityData) : Prop :=
  ∀ ancTy f, δ.ancestors.find? ancTy = .some f → f.isUDF

def SymEntityData.SymbolicAncestors (δ : SymEntityData) : Prop :=
  ∀ ancTy f, δ.ancestors.find? ancTy = .some f → f.isUUF

-- The ancestors for an entity type must either be fully specified (for enums)
-- or fully unconstrained (for other entity types).
def SymEntityData.PartitionedAncestors (δ : SymEntityData) : Prop :=
  if δ.isEnum then δ.ConcreteAncestors else δ.SymbolicAncestors

-- The hierarchy is partitioned among enumerated and non-enumerated types.
-- Specifically, ancestors of enumerated types must be concretely known (UDF
-- functions), while those of non-enumerated types must be symbolic (UUF
-- functions). Additionally, enumerated types can roll up only to other
-- enumerated types, while non-enumerated types can roll up only to other
-- non-enumerated types.
def SymEntities.Partitioned (εs : SymEntities) : Prop :=
  (∀ ety δ, εs.find? ety = .some δ →
    δ.PartitionedAncestors) ∧
  (∀ ety₁ δ₁ f₁₂ ety₂ δ₂,
    εs.find? ety₁ = .some δ₁ →
    εs.find? ety₂ = .some δ₂ →
    δ₁.ancestors.find? ety₂ = .some f₁₂ →
    δ₁.isEnum = δ₂.isEnum)

def SymEntities.Acyclic (εs : SymEntities) : Prop :=
  ∀ (uid : EntityUID) δ f,
    εs.find? uid.ty = .some δ →
    δ.ancestors.find? uid.ty = .some (.udf f) →
    uid ∉ (app (.udf f) (.entity uid)).entityUIDs

def SymEntityData.knownAncestors (uid : EntityUID) (δ : SymEntityData) : Set EntityUID :=
  δ.ancestors.toList.mapUnion ancs
where
  ancs : (EntityType × UnaryFunction) → Set EntityUID
  | (_, .uuf _) => Set.empty
  | (_, .udf f) => (app (.udf f) (.entity uid)).entityUIDs

def SymEntities.Transitive (εs : SymEntities) : Prop :=
  ∀ (uid₁ : EntityUID) δ₁ (uid₂ : EntityUID) δ₂,
    εs.find? uid₁.ty = .some δ₁ →
    εs.find? uid₂.ty = .some δ₂ →
    uid₂ ∈ δ₁.knownAncestors uid₁ →
    δ₂.knownAncestors uid₂ ⊆ δ₁.knownAncestors uid₁

def SymEntities.Hierarchical (εs : SymEntities) : Prop :=
  εs.Acyclic ∧ εs.Transitive ∧ εs.Partitioned

def SymEntities.StronglyWellFormed (εs : SymEntities) : Prop :=
  εs.WellFormed ∧ εs.Hierarchical

def Term.isBasic : Term → Bool
  | .var _ => true
  | t      => t.isLiteral

def SymRequest.IsBasic (ρ : SymRequest) : Prop :=
  ρ.principal.isBasic ∧
  ρ.action.isBasic ∧
  ρ.resource.isBasic ∧
  ρ.context.isBasic

def SymRequest.StronglyWellFormed (ρ : SymRequest) (εs : SymEntities) : Prop :=
  ρ.WellFormed εs ∧ ρ.IsBasic

def SymEnv.StronglyWellFormed (εnv : SymEnv) : Prop :=
  εnv.request.StronglyWellFormed εnv.entities ∧
  εnv.entities.StronglyWellFormed

def SymEnv.StronglyWellFormedFor (εnv : SymEnv) (x : Expr) : Prop :=
  εnv.StronglyWellFormed ∧
  εnv.entities.ValidRefsFor x

def SymEnv.StronglyWellFormedForAll (εnv : SymEnv) (xs : List Expr) : Prop :=
  εnv.StronglyWellFormed ∧
  ∀ x ∈ xs, εnv.entities.ValidRefsFor x

def SymEnv.StronglyWellFormedForPolicy (εnv : SymEnv) (p : Policy) : Prop :=
  εnv.StronglyWellFormedFor p.toExpr

def SymEnv.StronglyWellFormedForPolicies (εnv : SymEnv) (ps : Policies) : Prop :=
  εnv.StronglyWellFormedForAll (ps.map Policy.toExpr)

end Cedar.SymCC
