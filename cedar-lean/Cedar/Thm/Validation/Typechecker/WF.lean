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
import Cedar.Validation

/-!
This file contains the definition of well-formedness of `Environment`
and related definitions.
--/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Validation
open Cedar.Spec

----- Well-formedness of environment -----

def ActionSchema.IsActionEntityType (acts : ActionSchema) (ety : EntityType) : Prop :=
  ∃ uid, acts.contains uid ∧ uid.ty = ety

/--
Either a non-action entity type in `env.ets`,
or an action entity type in `env.acts`.
-/
def EntityType.WellFormed (env : Environment) (ety : EntityType) : Prop :=
  env.ets.contains ety ∨ env.acts.IsActionEntityType ety

mutual
inductive QualifiedType.WellFormed (env : Environment) : Qualified CedarType → Prop where
  | optional_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    QualifiedType.WellFormed env (.optional ty)
  | required_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    QualifiedType.WellFormed env (.required ty)

/--
Defines when a `CedarType` is well-formed in an `Environment`.
-/
inductive CedarType.WellFormed (env : Environment) : CedarType → Prop where
  | bool_wf {bty : BoolType} : CedarType.WellFormed env (.bool bty)
  | int_wf : CedarType.WellFormed env .int
  | string_wf : CedarType.WellFormed env .string
  | entity_wf {ety : EntityType}
    (h : EntityType.WellFormed env ety) :
    CedarType.WellFormed env (.entity ety)
  | set_wf {ty : CedarType}
    (h : CedarType.WellFormed env ty) :
    CedarType.WellFormed env (.set ty)
  | record_wf {rty : RecordType}
    -- Well-formed as a `Map`
    (h₁ : rty.WellFormed)
    -- Each attribute type is well-formed
    (h₂ : ∀ attr qty, rty.find? attr = some qty → QualifiedType.WellFormed env qty) :
    CedarType.WellFormed env (.record rty)
  | ext_wf {xty : ExtType} : CedarType.WellFormed env (.ext xty)
end

def StandardSchemaEntry.WellFormed (env : Environment) (entry : StandardSchemaEntry) : Prop :=
  -- Well-formed as `Map`/`Set`s
  entry.ancestors.WellFormed ∧
  -- Each ancestor entity type must be a well-formed,
  -- non-action, non-enum entity type
  (∀ anc ∈ entry.ancestors,
    ∃ entry, env.ets.find? anc = some entry ∧ entry.isStandard) ∧
  -- The attribute types are well-formed
  (CedarType.record entry.attrs).WellFormed env ∧
  -- The tag type is well-formed
  (∀ ty, entry.tags = .some ty → CedarType.WellFormed env ty)

def EntitySchemaEntry.WellFormed (env : Environment) (entry : EntitySchemaEntry) : Prop :=
  match entry with
  | standard entry => entry.WellFormed env
  | enum es => es.WellFormed ∧ ¬es.isEmpty

def EntitySchema.WellFormed (env : Environment) (ets : EntitySchema) : Prop :=
  Map.WellFormed ets ∧
  ∀ ety entry, ets.find? ety = some entry → entry.WellFormed env

def EntityUID.WellFormed (env : Environment) (uid : EntityUID) : Prop :=
  env.ets.isValidEntityUID uid ∨ env.acts.contains uid

def ActionSchemaEntry.WellFormed (env : Environment) (entry : ActionSchemaEntry) : Prop :=
  -- Well-formed as `Map`/`Set`s
  entry.appliesToPrincipal.WellFormed ∧
  entry.appliesToResource.WellFormed ∧
  entry.ancestors.WellFormed ∧
  -- Each principal/resource entity type is well-formed
  (∀ ety, entry.appliesToPrincipal.contains ety → EntityType.WellFormed env ety) ∧
  (∀ ety, entry.appliesToResource.contains ety → EntityType.WellFormed env ety) ∧
  -- Ancestors of each action entity must also be an action entity
  (∀ uid ∈ entry.ancestors, env.acts.contains uid) ∧
  -- Context is a well-formed `RecordType`
  (CedarType.record entry.context).WellFormed env

def ActionSchema.AcyclicActionHierarchy (acts : ActionSchema) : Prop :=
  ∀ uid entry, acts.find? uid = .some entry → uid ∉ entry.ancestors

def ActionSchema.TransitiveActionHierarchy (acts : ActionSchema) : Prop :=
  ∀ uid₁ entry₁ uid₂ entry₂,
    acts.find? uid₁ = .some entry₁ →
    acts.find? uid₂ = .some entry₂ →
    uid₂ ∈ entry₁.ancestors →
    entry₂.ancestors ⊆ entry₁.ancestors

def ActionSchema.WellFormed (env : Environment) (acts : ActionSchema) : Prop :=
  Map.WellFormed acts ∧
  (∀ uid entry, acts.find? uid = some entry → entry.WellFormed env) ∧
  (∀ uid, acts.contains uid → ¬env.ets.contains uid.ty) ∧
  acts.AcyclicActionHierarchy ∧
  acts.TransitiveActionHierarchy

def RequestType.WellFormed (env : Environment) (reqty : RequestType) : Prop :=
  ∃ entry, env.acts.find? reqty.action = some entry ∧
    -- Enforce that principal/resource/context are valid for the action
    reqty.principal ∈ entry.appliesToPrincipal ∧
    reqty.resource ∈ entry.appliesToResource ∧
    reqty.context = entry.context
  -- Other properties, such as the well-formedness of principal/resource/context
  -- follows from the above and the well-formedness of `env.ets` and `env.acts`.

def Environment.WellFormed (env : Environment) : Prop :=
  env.ets.WellFormed env ∧
  env.acts.WellFormed env ∧
  env.reqty.WellFormed env

end Cedar.Validation
