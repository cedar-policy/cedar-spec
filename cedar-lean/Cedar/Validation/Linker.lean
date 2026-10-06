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

public import Cedar.Validation.PartialSchema

/-!
This file implements linker that links two partial schemas
([RFC 116](https://github.com/cedar-policy/rfcs/pull/116)).
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

----- Errors -----

public inductive LinkError where
  /-- An entity type has the same name as the type of an action. -/
  | actionEntityTypeDeclared (ety : EntityType)
  /-- Both partial schemas define the entity type. -/
  | duplicateEntityType (ety : EntityType)
  /-- Both partial schemas define the action. -/
  | duplicateAction (uid : EntityUID)
  /-- An external entity type links to an enumerated entity type. -/
  | externalIsEnum (ety : EntityType)
  /-- An external entity has ancestors absent from its definition. -/
  | externalAncestorsNotInDefinition (ety : EntityType)
  /-- Linking would add ancestors to a defined entity type. -/
  | definedEntityAncestorsChanged (ety : EntityType)
  /-- Two declarations of an action have different parents. -/
  | externalActionParentsMismatch (uid : EntityUID)
deriving Repr, DecidableEq

public instance : ToString LinkError where
  toString
    | .actionEntityTypeDeclared ety => s!"entity type {ety} is also the type of an action"
    | .duplicateEntityType ety => s!"entity type {ety} is defined twice"
    | .duplicateAction uid => s!"action {uid} is defined twice"
    | .externalIsEnum ety => s!"external entity type {ety} links to an enumerated entity type"
    | .externalAncestorsNotInDefinition ety =>
      s!"external entity type {ety} has ancestors absent from its definition"
    | .definedEntityAncestorsChanged ety =>
      s!"linking would add ancestors to defined entity type {ety}"
    | .externalActionParentsMismatch uid => s!"declarations of action {uid} have different parents"

----- Transitive closure -----

/--
Close each set of parents under the parent relation, so it holds all
ancestors. Each round adds the current ancestors of every member; the number
of keys bounds the rounds needed.
-/
public def closeAncestors {α} [LT α] [DecidableLT α] [DecidableEq α]
    (parents : Map α (Set α)) : Map α (Set α) :=
  go parents.size parents
where
  go : Nat → Map α (Set α) → Map α (Set α)
    | 0,     m => m
    | n + 1, m => go n (m.mapOnValues λ s => Set.foldl (λ acc a => acc ∪ (m.find? a).getD ∅) s s)

/--
Close entity ancestors if doing so does not change a defined entity.
Error if taking closure causes any completed entity ancestor to enlarge.
-/
public def PartialEntitySchema.closeForLink (ets : PartialEntitySchema) : Except LinkError PartialEntitySchema := do
  let ancs := closeAncestors (ets.mapOnValues (·.ancestors))
  ets.toList.forM λ (ety, entry) =>
    match entry with
    | .defined (.standard std) =>
      if (ancs.find? ety).getD Set.empty == std.ancestors then .ok ()
      else .error (.definedEntityAncestorsChanged ety)
    | .defined (.enum _) | .external _ => .ok ()
  pure (Map.make (ets.toList.map λ (ety, entry) =>
    (ety, entry.withAncestors ((ancs.find? ety).getD Set.empty))))

----- Linking -----

/--
Link a single PartialEntitySchemaEntry.
Error when both are not external.
Error when the defined entity is Enum.
Error when an external ancestor is absent from the entity's definition.
-/
public def PartialEntitySchemaEntry.link (ety : EntityType) :
    PartialEntitySchemaEntry → PartialEntitySchemaEntry → Except LinkError PartialEntitySchemaEntry
  | .defined _, .defined _ => .error (.duplicateEntityType ety)
  | .external parents₁, .external parents₂ => .ok (.external (parents₁ ∪ parents₂))
  | .external parents, .defined entry
  | .defined entry, .external parents =>
    match entry with
    | .enum _ => .error (.externalIsEnum ety)
    | .standard std =>
      if parents.subset std.ancestors then .ok (.defined entry)
      else .error (.externalAncestorsNotInDefinition ety)

/--
Link a single PartialActionSchemaEntry.
Error when both are not external.
Error when they do not have the same ancestors.
-/
public def PartialActionSchemaEntry.link (uid : EntityUID) :
    PartialActionSchemaEntry → PartialActionSchemaEntry → Except LinkError PartialActionSchemaEntry
  | .defined _, .defined _ => .error (.duplicateAction uid)
  | .external parents₁, .external parents₂ =>
    if parents₁ == parents₂ then .ok (.external parents₁)
    else .error (.externalActionParentsMismatch uid)
  | .external parents, .defined entry
  | .defined entry, .external parents =>
    if parents == entry.ancestors then .ok (.defined entry)
    else .error (.externalActionParentsMismatch uid)

/--
Entity names from both first and second are linked.
Entity names appearing in only one of them are appended.
-/
public def linkMaps {α β} [LT α] [DecidableLT α] [DecidableEq α]
    (f : α → β → β → Except LinkError β) (m₁ m₂ : Map α β) : Except LinkError (Map α β) := do
  let linked ← m₁.toList.mapM λ (k, v₁) =>
    match m₂.find? k with
    | some v₂ => do pure (k, ← f k v₁ v₂)
    | none    => pure (k, v₁)
  let rest := m₂.toList.filter λ (k, _) => !m₁.contains k
  pure (Map.make (linked ++ rest))

/--
Link two partial schemas.
Error if partial schema have colliding names across action types and entity types.
-/
public def link (p c : PartialSchema) : Except LinkError PartialSchema := do
  (p.acts.toList ++ c.acts.toList).forM λ (uid, _) =>
    if p.ets.contains uid.ty || c.ets.contains uid.ty then
      .error (.actionEntityTypeDeclared uid.ty)
    else
      .ok ()
  let ets  ← linkMaps PartialEntitySchemaEntry.link p.ets c.ets
  let acts ← linkMaps PartialActionSchemaEntry.link p.acts c.acts
  let ets  ← PartialEntitySchema.closeForLink ets
  pure { ets, acts }

end Cedar.Validation
