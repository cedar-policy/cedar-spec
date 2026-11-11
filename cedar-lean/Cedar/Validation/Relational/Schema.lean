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

module

public import Cedar.Spec
public import Cedar.Validation

@[expose] public section

/-! # A constructive description of well-formed type environments

`WfTypeEnv env` builds a type environment in one pass, declaring each type before it is
referred to and each type's ancestors with their own, so that the hierarchies are acyclic and
transitively closed by construction. Every environment it describes satisfies `EnvAssumptions`;
`wfTypeEnv_validateWellFormed_iff` characterizes those that are well-formed. -/

namespace Cedar.Validation.Relational.Schema

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Entity type membership -/

/-- The entity type occurs in the list. -/
inductive DefinedEntityType : List EntityType → EntityType → Prop where
  | here : ∀ et rest, DefinedEntityType (et :: rest) et
  | there : ∀ et et' rest,
      et ≠ et' →
      DefinedEntityType rest et →
      DefinedEntityType (et' :: rest) et

/-! ## Record-key ordering bound -/
inductive KeyAbove : Option Attr → Attr → Prop where
  | none : ∀ a, KeyAbove Option.none a
  | some : ∀ b a, b < a → KeyAbove (Option.some b) a

/-! ## Well-formed CedarType and attributes (mutually recursive) -/

mutual

/-- A type whose entity types occur in `ets`, whose Boolean types are `.anyBool` and whose
    record types are strictly sorted by key. -/
inductive WfCedarType : List EntityType → CedarType → Prop where
  | bool : ∀ ets, WfCedarType ets (.bool .anyBool)
  | int : ∀ ets, WfCedarType ets .int
  | string : ∀ ets, WfCedarType ets .string
  | entity : ∀ ets ety,
      DefinedEntityType ets ety →
      WfCedarType ets (.entity ety)
  | set : ∀ ets ty,
      WfCedarType ets ty →
      WfCedarType ets (.set ty)
  | record : ∀ ets attrs,
      WfAttrs Option.none ets attrs →
      WfCedarType ets (.record (Map.mk attrs))
  | extDecimal : ∀ ets, WfCedarType ets (.ext .decimal)
  | extIPAddr : ∀ ets, WfCedarType ets (.ext .ipAddr)
  | extDatetime : ∀ ets, WfCedarType ets (.ext .datetime)
  | extDuration : ∀ ets, WfCedarType ets (.ext .duration)

/-- Well-formed attribute list, threading a strict lower bound `lb` on keys so
    the generated attribute list is strictly sorted (hence duplicate-free). -/
inductive WfAttrs : Option Attr → List EntityType → List (Attr × QualifiedType) → Prop where
  | nil : ∀ lb ets, WfAttrs lb ets []
  | consRequired : ∀ lb ets attr ty rest,
      KeyAbove lb attr →
      WfCedarType ets ty →
      WfAttrs (Option.some attr) ets rest →
      WfAttrs lb ets ((attr, .required ty) :: rest)
  | consOptional : ∀ lb ets attr ty rest,
      KeyAbove lb attr →
      WfCedarType ets ty →
      WfAttrs (Option.some attr) ets rest →
      WfAttrs lb ets ((attr, .optional ty) :: rest)

end

/-! ## Structural helper relations -/

/-- `et` does not appear in the list. Used to forbid duplicate type names,
    matching Cedar construction, which rejects `DuplicateEntityTypeError`. -/
inductive NotInET : EntityType → List EntityType → Prop where
  | nil  : ∀ et, NotInET et []
  | cons : ∀ et x rest, et ≠ x → NotInET et rest → NotInET et (x :: rest)

/-- List append, as a relation. -/
inductive AppendET : List EntityType → List EntityType → List EntityType → Prop where
  | nil  : ∀ ys, AppendET [] ys ys
  | cons : ∀ x xs ys zs, AppendET xs ys zs → AppendET (x :: xs) ys (x :: zs)

/-! ## Well-formed tags -/

/-- No tags, or a tag type satisfying `WfCedarType`. -/
inductive WfTags : List EntityType → Option CedarType → Prop where
  | none : ∀ ets, WfTags ets .none
  | some : ∀ ets ty,
      WfCedarType ets ty →
      WfTags ets (.some ty)

/-! ## Transitively closed ancestors, by construction

A new entity type picks its parents among those built before it, each with its own closed
ancestor list. -/
inductive PickClosedAncestors :
    List (EntityType × List EntityType) → List EntityType → Prop where
  | none : PickClosedAncestors [] []
  | skip : ∀ p pset built chosen,
      PickClosedAncestors built chosen →
      PickClosedAncestors ((p, pset) :: built) chosen
  | pick : ∀ p pset built chosen merged,
      PickClosedAncestors built chosen →
      AppendET pset chosen merged →
      PickClosedAncestors ((p, pset) :: built) (p :: merged)

/-! ## Well-formed entity schema, in one pass -/
inductive WfEntitiesGo :
    List (EntityType × List EntityType) →   -- built (closed-ancestor payload)
    List EntityType →                       -- names so far
    List EntityType →                       -- OUT: all declared names
    List (EntityType × EntitySchemaEntry) → Prop where
  | nil : ∀ built names,
      WfEntitiesGo built names names []
  | standard : ∀ built names et ancestors attrs tags allNames rest,
      NotInET et names →
      PickClosedAncestors built ancestors →
      WfAttrs Option.none (et :: names) attrs →
      WfTags (et :: names) tags →
      WfEntitiesGo ((et, ancestors) :: built) (et :: names) allNames rest →
      WfEntitiesGo built names allNames
        ((et, .standard (StandardSchemaEntry.mk (Set.mk ancestors) (Map.mk attrs) tags)) :: rest)
  | enum : ∀ built names et eids allNames rest,
      NotInET et names →
      WfEntitiesGo built (et :: names) allNames rest →
      WfEntitiesGo built names allNames ((et, .enum (Set.mk eids)) :: rest)

/-- Well-formed entity schema: run the topological construction from empty
    accumulators. The first index is the full list of declared entity-type names. -/
inductive WfEntitySchema : List EntityType → List (EntityType × EntitySchemaEntry) → Prop where
  | mk : ∀ allNames entries,
      WfEntitiesGo [] [] allNames entries →
      WfEntitySchema allNames entries

/-! ## Well-formed principal/resource type lists -/

/-- Every principal type occurs in `ets`. -/
inductive WfPrincipalTypes : List EntityType → List EntityType → Prop where
  | nil : ∀ ets, WfPrincipalTypes ets []
  | cons : ∀ ets p rest,
      DefinedEntityType ets p →
      WfPrincipalTypes ets rest →
      WfPrincipalTypes ets (p :: rest)

/-- Every resource type occurs in `ets`. -/
inductive WfResourceTypes : List EntityType → List EntityType → Prop where
  | nil : ∀ ets, WfResourceTypes ets []
  | cons : ∀ ets r rest,
      DefinedEntityType ets r →
      WfResourceTypes ets rest →
      WfResourceTypes ets (r :: rest)

/-! ## Action hierarchy: transitively-closed ancestors -/

/-- List append for action UIDs, as a relation (the `EntityUID` analogue of `AppendET`). -/
inductive AppendUID : List EntityUID → List EntityUID → List EntityUID → Prop where
  | nil  : ∀ ys, AppendUID [] ys ys
  | cons : ∀ x xs ys zs, AppendUID xs ys zs → AppendUID (x :: xs) ys (x :: zs)

/-- `SelectRemove xs y ys`: `y` is an element of `xs` and `ys` is `xs` without it. Used to draw
    distinct action eids from a fixed pool in `WfActionSchema`. -/
inductive SelectRemove {α} : List α → α → List α → Prop where
  | here  : ∀ x xs,      SelectRemove (x :: xs) x xs
  | there : ∀ x xs y ys, SelectRemove xs y ys → SelectRemove (x :: xs) y (x :: ys)

/-- The action analogue of `PickClosedAncestors`. -/
inductive PickClosedActionAncestors :
    List (EntityUID × List EntityUID) → List EntityUID → Prop where
  | none : PickClosedActionAncestors [] []
  | skip : ∀ p pset built chosen,
      PickClosedActionAncestors built chosen →
      PickClosedActionAncestors ((p, pset) :: built) chosen
  | pick : ∀ p pset built chosen merged,
      PickClosedActionAncestors built chosen →
      AppendUID pset chosen merged →
      PickClosedActionAncestors ((p, pset) :: built) (p :: merged)

/-! ## Well-formed action schema entry -/

/-- The entity type of the actions `WfActionSchema` builds. -/
abbrev actionEntityType : EntityType := { id := "Action", path := [] }

/-! ## Well-formed action schema -/

/-- The candidate action eids. `WfActionSchema` draws them without replacement (via
    `SelectRemove`), so the actions it builds are distinct. -/
def actionEidPool : List String :=
  ["a", "b", "c", "d", "e", "foo", "bar", "baz", "id", "name", "owner"]

/-- The action entries, in one pass; action eids are drawn without replacement from `avail`. -/
inductive WfActionsGo :
    List EntityType →                       -- ets (principal/resource/context types)
    List (EntityUID × List EntityUID) →     -- built: actions so far, each with closed ancestors
    List String →                           -- avail: remaining eid pool
    List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ ets built avail, WfActionsGo ets built avail []
  | cons : ∀ ets built avail avail' eid ancestors principals resources context rest,
      SelectRemove avail eid avail' →
      PickClosedActionAncestors built ancestors →
      WfPrincipalTypes ets principals →
      WfResourceTypes ets resources →
      WfAttrs Option.none ets context →
      WfActionsGo ets ((⟨actionEntityType, eid⟩, ancestors) :: built) avail' rest →
      WfActionsGo ets built avail
        ((⟨actionEntityType, eid⟩,
          ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context)) :: rest)

/-- Well-formed action schema: run the topological construction from empty accumulators, drawing
    distinct eids from `actionEidPool`. -/
inductive WfActionSchema : List EntityType → List (EntityUID × ActionSchemaEntry) → Prop where
  | mk : ∀ ets entries,
      WfActionsGo ets [] actionEidPool entries →
      WfActionSchema ets entries

/-! ## Well-formed request type -/

/-- A request type for one of the actions of the list. -/
inductive RequestFromAction :
    List EntityType →
    List (EntityUID × ActionSchemaEntry) →
    RequestType → Prop where
  | here : ∀ ets acts uid principals resources ancestors context principal resource,
      DefinedEntityType principals principal →
      DefinedEntityType resources resource →
      RequestFromAction ets
        ((uid, ActionSchemaEntry.mk (Set.mk principals) (Set.mk resources) (Set.mk ancestors) (Map.mk context)) :: acts)
        (RequestType.mk principal uid resource (Map.mk context))
  | there : ∀ ets act acts reqty,
      RequestFromAction ets acts reqty →
      RequestFromAction ets (act :: acts) reqty

/-! ## Type environments -/

/-- A type environment built from an entity schema (`WfEntitySchema`), an action schema over
    its entity types (`WfActionSchema`) and the request type of one of its actions. -/
inductive WfTypeEnv : TypeEnv → Prop where
  | mk : ∀ entityTypes entityEntries actionEntries reqty,
      WfEntitySchema entityTypes entityEntries →
      WfActionSchema entityTypes actionEntries →
      RequestFromAction entityTypes actionEntries reqty →
      WfTypeEnv (TypeEnv.mk (Map.mk entityEntries) (Map.mk actionEntries) reqty)

end Cedar.Validation.Relational.Schema
