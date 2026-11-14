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

public import Cedar.Validation.Relational.Typing

@[expose] public section

/-! # Relational specification of schema well-formedness

The relations mirror `TypeEnv.validateWellFormed` and `Schema.validateWellFormed`. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Structural helpers -/

/-- The list is strictly increasing: `List.isSorted`, i.e. `Set.wellFormed (Set.mk xs)`. -/
inductive EltsSorted {α} [LT α] : List α → Prop where
  | nil : EltsSorted []
  | single : ∀ x, EltsSorted [x]
  | cons : ∀ x y rest, x < y → EltsSorted (y :: rest) → EltsSorted (x :: y :: rest)

/-- The keys are strictly increasing: `List.isSortedBy Prod.fst`, i.e.
`Map.wellFormed (Map.mk kvs)`. -/
inductive KeysSorted {α β} [LT α] : List (α × β) → Prop where
  | nil : KeysSorted []
  | single : ∀ k v, KeysSorted [(k, v)]
  | cons : ∀ k₁ v₁ k₂ v₂ rest, k₁ < k₂ → KeysSorted ((k₂, v₂) :: rest) →
      KeysSorted ((k₁, v₁) :: (k₂, v₂) :: rest)

/-- `x` is not an element of the set: `s.contains x = false`. -/
inductive SetNotContains {α} : α → Set α → Prop where
  | empty : ∀ x, SetNotContains x (.mk [])
  | skip : ∀ x y rest, x ≠ y → SetNotContains x (.mk rest) → SetNotContains x (.mk (y :: rest))

/-- Every element of the list is in the set: `(Set.mk xs).subset s`. -/
inductive EltsSubset {α} : List α → Set α → Prop where
  | nil : ∀ s, EltsSubset [] s
  | cons : ∀ x xs s, SetContains x s → EltsSubset xs s → EltsSubset (x :: xs) s

/-- `m.find? k = some v`: the *first* binding of `k` in `m` is `v`. Unlike `MapContains`
(any binding) this is faithful on maps with duplicate keys. -/
inductive MapFind {α β : Type} : α → β → Map α β → Prop where
  | here : ∀ k v rest, MapFind k v (.mk ((k, v) :: rest))
  | there : ∀ k v k' v' rest, k ≠ k' → MapFind k v (.mk rest) →
      MapFind k v (.mk ((k', v') :: rest))

/-! ## Types (`EntityType`/`QualifiedType`/`CedarType.validateWellFormed`) -/

/-- `EntityType.validateWellFormed`: `ety` is declared in the entity schema, or is the type
of some action. -/
inductive EntityTypeWF : EntitySchema → ActionSchema → EntityType → Prop where
  | entity : ∀ ets acts ety entry, MapContains ety entry ets → EntityTypeWF ets acts ety
  | action : ∀ ets acts ety eid entry, MapContains { ty := ety, eid := eid } entry acts →
      EntityTypeWF ets acts ety

mutual

/-- `QualifiedType.validateWellFormed`. -/
inductive QualifiedTypeWF : EntitySchema → ActionSchema → QualifiedType → Prop where
  | optional : ∀ ets acts ty, CedarTypeWF ets acts ty → QualifiedTypeWF ets acts (.optional ty)
  | required : ∀ ets acts ty, CedarTypeWF ets acts ty → QualifiedTypeWF ets acts (.required ty)

/-- `validateAttrsWellFormed`: every attribute type is well-formed. -/
inductive AttrsWF : EntitySchema → ActionSchema → List (Attr × QualifiedType) → Prop where
  | nil : ∀ ets acts, AttrsWF ets acts []
  | cons : ∀ ets acts a qty rest, QualifiedTypeWF ets acts qty → AttrsWF ets acts rest →
      AttrsWF ets acts ((a, qty) :: rest)

/-- `CedarType.validateWellFormed`: entity types are declared and records are sorted maps. -/
inductive CedarTypeWF : EntitySchema → ActionSchema → CedarType → Prop where
  | bool : ∀ ets acts bty, CedarTypeWF ets acts (.bool bty)
  | int : ∀ ets acts, CedarTypeWF ets acts .int
  | string : ∀ ets acts, CedarTypeWF ets acts .string
  | entity : ∀ ets acts ety, EntityTypeWF ets acts ety → CedarTypeWF ets acts (.entity ety)
  | set : ∀ ets acts ty, CedarTypeWF ets acts ty → CedarTypeWF ets acts (.set ty)
  | record : ∀ ets acts rty, KeysSorted rty → AttrsWF ets acts rty →
      CedarTypeWF ets acts (.record (.mk rty))
  | ext : ∀ ets acts xty, CedarTypeWF ets acts (.ext xty)

end

mutual

/-- The `optional`/`required` case of `CedarType.validateLifted` on a record attribute. -/
inductive QualifiedTypeLifted : QualifiedType → Prop where
  | optional : ∀ ty, CedarTypeLifted ty → QualifiedTypeLifted (.optional ty)
  | required : ∀ ty, CedarTypeLifted ty → QualifiedTypeLifted (.required ty)

/-- The record case of `CedarType.validateLifted`: every attribute type is lifted. -/
inductive AttrsLifted : List (Attr × QualifiedType) → Prop where
  | nil : AttrsLifted []
  | cons : ∀ a qty rest, QualifiedTypeLifted qty → AttrsLifted rest →
      AttrsLifted ((a, qty) :: rest)

/-- `CedarType.validateLifted`: no singleton Boolean types (`tt`/`ff`) occur. -/
inductive CedarTypeLifted : CedarType → Prop where
  | bool : CedarTypeLifted (.bool .anyBool)
  | int : CedarTypeLifted .int
  | string : CedarTypeLifted .string
  | entity : ∀ ety, CedarTypeLifted (.entity ety)
  | set : ∀ ty, CedarTypeLifted ty → CedarTypeLifted (.set ty)
  | record : ∀ rty, AttrsLifted rty → CedarTypeLifted (.record (.mk rty))
  | ext : ∀ xty, CedarTypeLifted (.ext xty)

end

/-! ## Entity schema (`StandardSchemaEntry`/`EntitySchemaEntry`/`EntitySchema.validateWellFormed`) -/

/-- Every ancestor type is declared in the entity schema (the `ets.find?` loop of
`StandardSchemaEntry.validateWellFormed`). Action types are not allowed. -/
inductive EntityAncestorsWF : EntitySchema → List EntityType → Prop where
  | nil : ∀ ets, EntityAncestorsWF ets []
  | cons : ∀ ets anc entry rest, MapContains anc entry ets → EntityAncestorsWF ets rest →
      EntityAncestorsWF ets (anc :: rest)

/-- The tag check of `StandardSchemaEntry.validateWellFormed`. -/
inductive TagsWF : EntitySchema → ActionSchema → Option CedarType → Prop where
  | none : ∀ ets acts, TagsWF ets acts .none
  | some : ∀ ets acts ty, CedarTypeWF ets acts ty → CedarTypeLifted ty → TagsWF ets acts (.some ty)

/-- `StandardSchemaEntry.validateWellFormed`. -/
inductive StandardEntryWF : EntitySchema → ActionSchema → StandardSchemaEntry → Prop where
  | mk : ∀ ets acts ancs attrs tags,
      EltsSorted ancs →
      EntityAncestorsWF ets ancs →
      CedarTypeWF ets acts (.record attrs) →
      CedarTypeLifted (.record attrs) →
      TagsWF ets acts tags →
      StandardEntryWF ets acts { ancestors := .mk ancs, attrs := attrs, tags := tags }

/-- `EntitySchemaEntry.validateWellFormed`: enumerations are sorted and non-empty. -/
inductive EntityEntryWF : EntitySchema → ActionSchema → EntitySchemaEntry → Prop where
  | standard : ∀ ets acts entry, StandardEntryWF ets acts entry →
      EntityEntryWF ets acts (.standard entry)
  | enum : ∀ ets acts eid eids, EltsSorted (eid :: eids) →
      EntityEntryWF ets acts (.enum (.mk (eid :: eids)))

/-- The entry loop of `EntitySchema.validateWellFormed`. -/
inductive EntityEntriesWF : EntitySchema → ActionSchema →
    List (EntityType × EntitySchemaEntry) → Prop where
  | nil : ∀ ets acts, EntityEntriesWF ets acts []
  | cons : ∀ ets acts ety entry rest, EntityEntryWF ets acts entry →
      EntityEntriesWF ets acts rest → EntityEntriesWF ets acts ((ety, entry) :: rest)

/-- `EntitySchema.validateWellFormed env ets'`, where `ets`/`acts` are `env.ets`/`env.acts`. -/
inductive EntitySchemaWF : EntitySchema → ActionSchema → EntitySchema → Prop where
  | mk : ∀ ets acts entries, KeysSorted entries → EntityEntriesWF ets acts entries →
      EntitySchemaWF ets acts (.mk entries)

/-! ## Action schema (`ActionSchemaEntry`/`ActionSchema.validateWellFormed`) -/

/-- `forM (EntityType.validateWellFormed env)` over principal/resource types. -/
inductive EntityTypesWF : EntitySchema → ActionSchema → List EntityType → Prop where
  | nil : ∀ ets acts, EntityTypesWF ets acts []
  | cons : ∀ ets acts ety rest, EntityTypeWF ets acts ety → EntityTypesWF ets acts rest →
      EntityTypesWF ets acts (ety :: rest)

/-- Every ancestor of an action is an action (`env.acts.contains uid`). -/
inductive ActionAncestorsWF : ActionSchema → List EntityUID → Prop where
  | nil : ∀ acts, ActionAncestorsWF acts []
  | cons : ∀ acts uid entry rest, MapContains uid entry acts → ActionAncestorsWF acts rest →
      ActionAncestorsWF acts (uid :: rest)

/-- `ActionSchemaEntry.validateWellFormed`. -/
inductive ActionEntryWF : EntitySchema → ActionSchema → ActionSchemaEntry → Prop where
  | mk : ∀ ets acts principals resources ancs context,
      EltsSorted principals →
      EltsSorted resources →
      EltsSorted ancs →
      EntityTypesWF ets acts principals →
      EntityTypesWF ets acts resources →
      ActionAncestorsWF acts ancs →
      CedarTypeWF ets acts (.record context) →
      CedarTypeLifted (.record context) →
      ActionEntryWF ets acts
        { appliesToPrincipal := .mk principals, appliesToResource := .mk resources,
          ancestors := .mk ancs, context := context }

/-- The entry loop of `ActionSchema.validateWellFormed`: an action's entity type is not
declared in the entity schema, and its entry is well-formed. -/
inductive ActionEntriesWF : EntitySchema → ActionSchema →
    List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ ets acts, ActionEntriesWF ets acts []
  | cons : ∀ ets acts ety eid entry rest,
      MapNotContainsKey ety ets →
      ActionEntryWF ets acts entry →
      ActionEntriesWF ets acts rest →
      ActionEntriesWF ets acts (({ ty := ety, eid := eid }, entry) :: rest)

/-- The loop of `ActionSchema.validateAcyclicActionHierarchy`: no action is its own ancestor. -/
inductive ActionsIrreflexive : List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ActionsIrreflexive []
  | cons : ∀ uid principals resources ancs context rest,
      SetNotContains uid ancs →
      ActionsIrreflexive rest →
      ActionsIrreflexive ((uid,
        { appliesToPrincipal := principals, appliesToResource := resources,
          ancestors := ancs, context := context }) :: rest)

/-- `ActionSchema.validateAcyclicActionHierarchy`. Like the check, this only forbids
self-loops; together with `ActionHierarchyTransitive` that rules out every cycle (a cycle
through `a` would make `a` its own ancestor by transitivity). -/
inductive ActionHierarchyAcyclic : ActionSchema → Prop where
  | mk : ∀ entries, ActionsIrreflexive entries → ActionHierarchyAcyclic (.mk entries)

/-- The inner loop of `ActionSchema.validateTransitiveActionHierarchy` for a fixed action with
ancestors `ancs₁`: every listed action that is an ancestor has its own ancestors in `ancs₁`. -/
inductive ActionsTransitiveFrom : Set EntityUID → List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ ancs₁, ActionsTransitiveFrom ancs₁ []
  | notAncestor : ∀ ancs₁ uid₂ entry₂ rest,
      SetNotContains uid₂ ancs₁ →
      ActionsTransitiveFrom ancs₁ rest →
      ActionsTransitiveFrom ancs₁ ((uid₂, entry₂) :: rest)
  | ancestor : ∀ ancs₁ uid₂ principals resources ancs₂ context rest,
      SetContains uid₂ ancs₁ →
      EltsSubset ancs₂ ancs₁ →
      ActionsTransitiveFrom ancs₁ rest →
      ActionsTransitiveFrom ancs₁ ((uid₂,
        { appliesToPrincipal := principals, appliesToResource := resources,
          ancestors := .mk ancs₂, context := context }) :: rest)

/-- The outer loop of `ActionSchema.validateTransitiveActionHierarchy`: each action of the
first list satisfies `ActionsTransitiveFrom` against all actions `all`. -/
inductive ActionsTransitive : List (EntityUID × ActionSchemaEntry) →
    List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ all, ActionsTransitive all []
  | cons : ∀ all uid₁ principals resources ancs₁ context rest,
      ActionsTransitiveFrom ancs₁ all →
      ActionsTransitive all rest →
      ActionsTransitive all ((uid₁,
        { appliesToPrincipal := principals, appliesToResource := resources,
          ancestors := ancs₁, context := context }) :: rest)

/-- `ActionSchema.validateTransitiveActionHierarchy`: if `a₂` is an ancestor of `a₁`, then so
are all ancestors of `a₂`. -/
inductive ActionHierarchyTransitive : ActionSchema → Prop where
  | mk : ∀ entries, ActionsTransitive entries entries → ActionHierarchyTransitive (.mk entries)

/-- `ActionSchema.validateWellFormed env acts'`, where `ets`/`acts` are `env.ets`/`env.acts`. -/
inductive ActionSchemaWF : EntitySchema → ActionSchema → ActionSchema → Prop where
  | mk : ∀ ets acts entries,
      KeysSorted entries →
      ActionEntriesWF ets acts entries →
      ActionHierarchyAcyclic (.mk entries) →
      ActionHierarchyTransitive (.mk entries) →
      ActionSchemaWF ets acts (.mk entries)

/-! ## Request type and environments -/

/-- `RequestType.validateWellFormed`: the action's (first) entry applies to the principal and
resource, with the same context type. -/
inductive RequestTypeWF : ActionSchema → RequestType → Prop where
  | mk : ∀ acts principal action resource principals resources ancs context,
      MapFind action
        { appliesToPrincipal := principals, appliesToResource := resources,
          ancestors := ancs, context := context } acts →
      SetContains principal principals →
      SetContains resource resources →
      RequestTypeWF acts
        { principal := principal, action := action, resource := resource, context := context }

/-- `TypeEnv.validateWellFormed`. -/
inductive TypeEnvWF : TypeEnv → Prop where
  | mk : ∀ ets acts reqty,
      EntitySchemaWF ets acts ets →
      ActionSchemaWF ets acts acts →
      RequestTypeWF acts reqty →
      TypeEnvWF { ets := ets, acts := acts, reqty := reqty }

/-- `env` is one of `Schema.environments schema`: one environment per action and
principal/resource pair the action applies to. -/
inductive SchemaEnvironment : Schema → TypeEnv → Prop where
  | mk : ∀ ets acts action principals resources ancs context principal resource,
      MapContains action
        { appliesToPrincipal := principals, appliesToResource := resources,
          ancestors := ancs, context := context } acts →
      SetContains principal principals →
      SetContains resource resources →
      SchemaEnvironment { ets := ets, acts := acts }
        { ets := ets, acts := acts,
          reqty := { principal := principal, action := action, resource := resource,
                     context := context } }

/-- `Schema.validateWellFormed`: every environment of the schema is well-formed. -/
def SchemaWF (schema : Schema) : Prop :=
  ∀ env, SchemaEnvironment schema env → TypeEnvWF env

end Cedar.Validation.Relational
