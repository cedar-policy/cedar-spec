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

def instanceOfEntityType (e : EntityUID) (ety : EntityType) (env : Environment) : Bool :=
  ety == e.ty &&
  (env.ets.isValidEntityUID e || env.acts.contains e)

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

def instanceOfType (v : Value) (ty : CedarType) (env : Environment) : Bool :=
  match v, ty with
  | .prim (.bool b), .bool bty => instanceOfBoolType b bty
  | .prim (.int _), .int => true
  | .prim (.string _), .string => true
  | .prim (.entityUID e), .entity ety => instanceOfEntityType e ety env
  | .set s, .set ty => s.elts.attach.all (λ ⟨v, _⟩ => instanceOfType v ty env)
  | .record r, .record rty =>
    r.kvs.all (λ (k, _) => rty.contains k) &&
    (r.kvs.attach₂.all (λ ⟨(k, v), _⟩ => (match rty.find? k with
        | .some qty => instanceOfType v qty.getType env
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

def instanceOfRequestType (request : Request) (reqty : RequestType) (env : Environment) : Bool :=
  instanceOfEntityType request.principal reqty.principal env &&
  request.action == reqty.action &&
  instanceOfEntityType request.resource reqty.resource env &&
  instanceOfType request.context (.record reqty.context) env

/--
For every entity in the store,
1. The entity's type is defined in the type store (either `ets` or `as` for action entities).
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
4. The entity's tags' types are consistent with the tags information in the type store.

For every action in the entity store, the action's ancestors are consistent
with the ancestor information in the action store.
-/
def instanceOfSchema (entities : Entities) (env : Environment) : EntityValidationResult :=
  do
    entities.toList.forM λ (uid, data) => instanceOfSchemaEntry uid data
    env.acts.toList.forM λ (uid, _) => actionExists uid
where
  instanceOfEntityTags (data : EntityData) (entry : EntitySchemaEntry) : Bool :=
    match entry.tags? with
    | .some tty => data.tags.values.all (instanceOfType · tty env)
    | .none     => data.tags == Map.empty
  instanceOfEntitySchemaEntry uid data entry :=
    if entry.isValidEntityEID uid.eid then
      if instanceOfType data.attrs (.record entry.attrs) env then
        if data.ancestors.all (λ ancestor =>
          entry.ancestors.contains ancestor.ty &&
          instanceOfEntityType ancestor ancestor.ty env) then
          if instanceOfEntityTags data entry then .ok ()
          else .error (.typeError s!"entity tags inconsistent with type store")
        else .error (.typeError s!"entity ancestors inconsistent with type store")
      else .error (.typeError "entity attributes do not match type store")
    else .error (.typeError s!"invalid entity uid: {uid}")
  instanceOfActionSchemaEntry uid data :=
    if data.attrs == Map.empty then
      if data.tags == Map.empty then
        match env.acts.find? uid with
        | .some entry =>
          if data.ancestors == entry.ancestors then .ok ()
          else .error (.typeError s!"action entity {uid} ancestors inconsistent with schema")
        | _ => .error (.typeError "entity type not defined in type store")
      else .error (.typeError s!"action entitiy {uid} cannot have tags")
    else .error (.typeError s!"action entitiy {uid} cannot have attributes")
  instanceOfSchemaEntry uid data :=
    match env.ets.find? uid.ty with
    |  .some entry => instanceOfEntitySchemaEntry uid data entry
    | _ => instanceOfActionSchemaEntry uid data
  actionExists uid :=
    if entities.contains uid then .ok ()
    else .error (.typeError s!"action entity {uid} does not exist")

def Environment.wellFormed (env : Environment) : Bool := sorry

def requestMatchesEnvironment (env : Environment) (request : Request): Bool := instanceOfRequestType request env.reqty env

def validateRequest (schema : Schema) (request : Request) : RequestValidationResult :=
  if ((schema.environments.any (requestMatchesEnvironment · request)))
  then .ok ()
  else .error (.typeError "request could not be validated in any environment")

def entitiesMatchEnvironment (env : Environment) (entities : Entities) : EntityValidationResult :=
  instanceOfSchema entities env

def actionSchemaEntryToEntityData (ase : ActionSchemaEntry) : EntityData := {
  ancestors := ase.ancestors,
  attrs := Map.empty,
  tags := Map.empty
}

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
