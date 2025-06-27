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

/- This file includes boolean definitions for the propositions declared in `Cedar/Thm/Validation/Typechecker/Types.lean`.-/
import Cedar.Validation.Validator
import Cedar.Validation.Typechecker
namespace Cedar.Validation

open Cedar.Spec
open Cedar.Data

inductive RequestValidationError where
| typeError (msg : String)

abbrev RequestValidationResult := Except RequestValidationError Unit

inductive EntityValidationError where
| typeError (msg : String)

abbrev EntityValidationResult := Except EntityValidationError Unit

def instanceOfBoolType (b : Bool) (bty : BoolType) : Bool :=
  match b, bty with
  | true, .tt => true
  | false, .ff => true
  | _, .anyBool => true
  | _, _ => false

def instanceOfEntityType (e : EntityUID) (ety : EntityType ) (eids: EntityType → Option (Set String)) : Bool :=
  ety == e.ty &&
  match eids ety with
  | .some eids => eids.contains e.eid
  | _ => true

def instanceOfExtType (ext : Ext) (extty: ExtType) : Bool :=
match ext, extty with
  | .decimal _, .decimal => true
  | .ipaddr _, .ipAddr => true
  | .datetime _, .datetime => true
  | .duration _, .duration => true
  | _, _ => false

def requiredAttributePresent (r : Map Attr Value) (rty : Map Attr (Qualified CedarType)) (k : Attr) :=
match rty.find? k with
    | .some qty => if qty.isRequired then r.contains k else true
    | _ => true

def instanceOfType (v : Value) (ty : CedarType) (schema: EntitySchema) : Bool :=
  match v, ty with
  | .prim (.bool b), .bool bty => instanceOfBoolType b bty
  | .prim (.int _), .int => true
  | .prim (.string _), .string => true
  | .prim (.entityUID e), .entity ety => instanceOfEntityType e ety schema.entityTypeMembers?
  | .set s, .set ty => s.elts.attach.all (λ ⟨v, _⟩ => instanceOfType v ty schema)
  | .record r, .record rty =>
    r.kvs.all (λ (k, _) => rty.contains k) &&
    (r.kvs.attach₂.all (λ ⟨(k, v), _⟩ => (match rty.find? k with
        | .some qty => instanceOfType v qty.getType schema
        | _ => true))) &&
    rty.kvs.all (λ (k, _) => requiredAttributePresent r rty k)
  | .ext x, .ext xty => instanceOfExtType x xty
  | _, _ => false
    termination_by v
    decreasing_by
      all_goals simp_wf
      case _ h₁ =>
        have := Set.sizeOf_lt_of_mem h₁
        omega
      case _ h₁ =>
        cases r
        simp only [Map.kvs] at h₁
        simp only [Map.mk.sizeOf_spec]
        omega

def instanceOfRequestType (request : Request) (reqty : RequestType) (schema: EntitySchema) : Bool :=
  instanceOfEntityType request.principal reqty.principal schema.entityTypeMembers? &&
  request.action == reqty.action &&
  instanceOfEntityType request.resource reqty.resource schema.entityTypeMembers? &&
  instanceOfType request.context (.record reqty.context) schema

/--
For every entity in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
4. The entity's tags' types are consistent with the tags information in the type store.
-/
def instanceOfEntitySchema (entities : Entities) (ets : EntitySchema) (as : ActionSchema) : EntityValidationResult :=
  entities.toList.forM λ (uid, data) => instanceOfEntityData uid data
where
  instanceOfEntityTags (data : EntityData) (entry : EntitySchemaEntry) : Bool :=
    match entry.tags? with
    | .some tty => data.tags.values.all (instanceOfType · tty ets)
    | .none     => data.tags == Map.empty
  instanceOfEntityData uid data :=
    match ets.find? uid.ty with
    |  .some entry =>
      if entry.isValidEntityEID uid.eid then
        if instanceOfType data.attrs (.record entry.attrs) ets then
          if data.ancestors.all (λ ancestor =>
            entry.ancestors.contains ancestor.ty &&
            instanceOfEntityType ancestor ancestor.ty ets.entityTypeMembers?) then
            if instanceOfEntityTags data entry then .ok ()
            else .error (.typeError s!"entity tags inconsistent with type store")
          else .error (.typeError s!"entity ancestors inconsistent with type store")
        else .error (.typeError "entity attributes do not match type store")
      else .error (.typeError s!"invalid entity uid: {uid}")
    | _ =>
      match as.find? uid with
      | .some _ =>
        if data.attrs == Map.empty then
          if data.tags == Map.empty then .ok ()
          else .error (.typeError s!"action entitiy {uid} cannot have tags")
        else .error (.typeError s!"action entitiy {uid} cannot have attributes")
      | _ => .error (.typeError "entity type not defined in type store")

/--
For every action in the entity store, the action's ancestors are consistent
with the ancestor information in the action store.
-/
def instanceOfActionSchema (entities : Entities) (as : ActionSchema) : EntityValidationResult :=
  as.toList.forM λ (uid, data) => instanceOfActionSchemaData uid data
where
  instanceOfActionSchemaData uid data :=
    match entities.find? uid with
      | .some entry => if data.ancestors == entry.ancestors
                       then .ok ()
                       else .error (.typeError "action ancestors inconsistent with type store information")
      | _ => .error (.typeError s!"action type {uid.eid} not defined in type store")

def requestMatchesEnvironment (env : Environment) (request : Request): Bool := instanceOfRequestType request env.reqty env.ets

def validateRequest (schema : Schema) (request : Request) : RequestValidationResult :=
  if ((schema.environments.any (requestMatchesEnvironment · request)))
  then .ok ()
  else .error (.typeError "request could not be validated in any environment")

def entitiesMatchEnvironment (env : Environment) (entities : Entities) : EntityValidationResult :=
  instanceOfEntitySchema entities env.ets env.acts >>= λ _ => instanceOfActionSchema entities env.acts

def actionSchemaEntryToEntityData (ase : ActionSchemaEntry) : EntityData := {
  ancestors := ase.ancestors,
  attrs := Map.empty,
  tags := Map.empty
}

/--
Update the entity schema with the entities created for action schema entries.
This involves the construction of the ancestor information for the associated types
by inspecting the concrete hierarchy.
-/
def updateSchema (schema : Schema) (actionSchemaEntities : Entities) : Schema :=
  let uniqueTys := Set.make (actionSchemaEntities.keys.map (·.ty)).elts
  let newEntitySchemaEntries := uniqueTys.elts.map makeEntitySchemaEntries
  {
    ets := Map.make (schema.ets.kvs ++ newEntitySchemaEntries),
    acts := schema.acts
  }
  where
    makeEntitySchemaEntries ty :=
      let entriesWithType := actionSchemaEntities.filter (λ k _ => k.ty == ty)
      let allAncestorsForType := List.flatten (entriesWithType.values.map (λ edt =>
        edt.ancestors.elts.map (·.ty) ))
      let ese : EntitySchemaEntry := .standard {
        ancestors := Set.make allAncestorsForType,
        attrs := Map.empty,
        tags := Option.none
      }
      (ty, ese)

def validateEntities (schema : Schema) (entities : Entities) : EntityValidationResult :=
  schema.environments.forM (entitiesMatchEnvironment · entities)

-- json

def entityValidationErrorToJson : EntityValidationError → Lean.Json
  | .typeError x => x

instance : Lean.ToJson EntityValidationError where
  toJson := entityValidationErrorToJson

def requestValidationErrorToJson : RequestValidationError → Lean.Json
  | .typeError x => x

instance : Lean.ToJson RequestValidationError where
  toJson := requestValidationErrorToJson


end Cedar.Validation
