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

public import Cedar.Validation.Relational.Request

@[expose] public section

/-! # Relational specification of entity validation

`ValidEntities schema entities` holds when `validateEntities` accepts `entities`. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- Every ancestor `ancs` of a standard entity has one of the declared ancestor types
    `ancTys` and is a valid entity. -/
inductive AncestorsAllowed : EntitySchema → ActionSchema → Set EntityType → List EntityUID →
    Prop where
  | nil : ∀ ets acts ancTys, AncestorsAllowed ets acts ancTys []
  | cons : ∀ ets acts ancTys ety eid ancs,
      SetContains ety ancTys →
      ValidEntityUID ety eid ets acts →
      AncestorsAllowed ets acts ancTys ancs →
      AncestorsAllowed ets acts ancTys (⟨ety, eid⟩ :: ancs)

/-- Every value in a list of tags is an instance of the tag type. -/
inductive TagValuesInstance : EntitySchema → ActionSchema → List (Tag × Value) → CedarType →
    Prop where
  | nil : ∀ ets acts ty, TagValuesInstance ets acts [] ty
  | cons : ∀ ets acts k v tags ty,
      InstanceOfType ets acts v ty →
      TagValuesInstance ets acts tags ty →
      TagValuesInstance ets acts ((k, v) :: tags) ty

/-- `instanceOfEntityTags`: with a tag type every tag value has that type, and without one
    there are no tags. -/
inductive TagsInstance : EntitySchema → ActionSchema → Map Tag Value → Option CedarType →
    Prop where
  | some : ∀ ets acts tags ty, TagValuesInstance ets acts tags ty →
      TagsInstance ets acts (.mk tags) (.some ty)
  | none : ∀ ets acts, TagsInstance ets acts (.mk []) .none

/-- `instanceOfEntitySchemaEntry`: the entity `⟨ety, eid⟩` with data `data` is an instance
    of its entity type's schema entry. An enumerated entity type declares no attributes,
    ancestors or tags, so its entities have none. -/
inductive InstanceOfEntitySchemaEntry : EntitySchema → ActionSchema → EntityUID → EntityData →
    EntitySchemaEntry → Prop where
  | standard : ∀ ets acts uid attrs ancs tags ancTys attrTys tagTy,
      InstanceOfType ets acts (.record attrs) (.record attrTys) →
      AncestorsAllowed ets acts ancTys ancs.elts →
      TagsInstance ets acts tags tagTy →
      InstanceOfEntitySchemaEntry ets acts uid ⟨attrs, ancs, tags⟩
        (.standard ⟨ancTys, attrTys, tagTy⟩)
  | enum : ∀ ets acts ety eid eids,
      SetContains eid eids →
      InstanceOfEntitySchemaEntry ets acts ⟨ety, eid⟩ ⟨.mk [], .mk [], .mk []⟩ (.enum eids)

/-- `instanceOfActionSchemaEntry`: an action entity has no attributes or tags and exactly the
    ancestors its action schema entry declares. -/
inductive InstanceOfActionSchemaEntry : ActionSchema → EntityUID → EntityData → Prop where
  | mk : ∀ acts uid entry,
      MapContains uid entry acts →
      InstanceOfActionSchemaEntry acts uid ⟨.mk [], entry.ancestors, .mk []⟩

/-- `instanceOfSchemaEntry`: an entity of a type declared in the entity schema is an instance
    of that type's entry; any other entity is an action. -/
inductive InstanceOfSchemaEntry : EntitySchema → ActionSchema → EntityUID → EntityData → Prop where
  | entity : ∀ ets acts uid data entry,
      MapContains uid.ty entry ets →
      InstanceOfEntitySchemaEntry ets acts uid data entry →
      InstanceOfSchemaEntry ets acts uid data
  | action : ∀ ets acts uid data,
      MapNotContainsKey uid.ty ets →
      InstanceOfActionSchemaEntry acts uid data →
      InstanceOfSchemaEntry ets acts uid data

/-- Every entity in a list of entities is an instance of its schema entry. -/
inductive EntityEntriesInstance : EntitySchema → ActionSchema → List (EntityUID × EntityData) →
    Prop where
  | nil : ∀ ets acts, EntityEntriesInstance ets acts []
  | cons : ∀ ets acts uid data es,
      InstanceOfSchemaEntry ets acts uid data →
      EntityEntriesInstance ets acts es →
      EntityEntriesInstance ets acts ((uid, data) :: es)

/-- Every action in a list of action schema entries is an entity of `entities`. -/
inductive ActionsExist : Entities → List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ entities, ActionsExist entities []
  | cons : ∀ entities uid entry data acs,
      MapContains uid data entities →
      ActionsExist entities acs →
      ActionsExist entities ((uid, entry) :: acs)

/-- `instanceOfSchema`: the entities are an instance of the entity schema `ets` and the
    action schema `acts`. -/
inductive InstanceOfSchema : EntitySchema → ActionSchema → Entities → Prop where
  | mk : ∀ ets acts es,
      EntityEntriesInstance ets acts es →
      ActionsExist (.mk es) acts.toList →
      InstanceOfSchema ets acts (.mk es)

/-- No action of a list of action schema entries has both a principal and a resource type,
    so the schema has no environments. -/
inductive NoRequestTypes : List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : NoRequestTypes []
  | noPrincipals : ∀ uid rtys ancs ctx acs, NoRequestTypes acs →
      NoRequestTypes ((uid, ⟨.mk [], rtys, ancs, ctx⟩) :: acs)
  | noResources : ∀ uid ptys ancs ctx acs, NoRequestTypes acs →
      NoRequestTypes ((uid, ⟨ptys, .mk [], ancs, ctx⟩) :: acs)

/-- `validateEntities schema entities` succeeds. -/
inductive ValidEntities : Schema → Entities → Prop where
  | noEnvironments : ∀ ets acts entities, NoRequestTypes acts.toList →
      ValidEntities ⟨ets, acts⟩ entities
  | instance : ∀ ets acts entities, InstanceOfSchema ets acts entities →
      ValidEntities ⟨ets, acts⟩ entities

end Cedar.Validation.Relational
