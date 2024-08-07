import Cedar.Validation.Validator
import Cedar.Validation.Typechecker
namespace Cedar.Validation

open Cedar.Spec
open Cedar.Data

inductive RequestValidationError where
| typeError (loc : String)

abbrev RequestValidationResult := Except RequestValidationError Unit

inductive EntityValidationError where
| typeError (loc : String)

abbrev EntityValidationResult := Except EntityValidationError Unit

def instanceOfBoolType (b : Bool) (bty : BoolType) : Bool :=
  match b, bty with
  | true, .tt => true
  | false, .ff => true
  | _, .anyBool => true
  | _, _ => false

def instanceOfEntityType (e : EntityUID) (ety : EntityType ) : Bool := ety == e.ty

def instanceOfExtType (ext : Ext) (extty: ExtType) : Bool :=
match ext, extty with
  | .decimal _, .decimal => true
  | .ipaddr _, .ipAddr => true
  | _, _ => false

def requiredAttributePresent (r : Map Attr Value) (rty : Map Attr (Qualified CedarType)) (k : Attr) :=
match rty.find? k with
    | .some qty => if qty.isRequired then r.contains k else true
    | _ => true

def instanceOfType (v : Value) (ty : CedarType) : Bool :=
  match v, ty with
  | .prim (.bool b), .bool bty => instanceOfBoolType b bty
  | .prim (.int _), .int => true
  | .prim (.string _), .string => true
  | .prim (.entityUID e), .entity ety => instanceOfEntityType e ety
  | .set s, .set ty => s.elts.attach.all (λ ⟨v, _⟩ => instanceOfType v ty)
  | .record r, .record rty =>
    r.kvs.all (λ (k, _) => rty.contains k) &&
    (r.kvs.attach₂.all (λ ⟨(k, v), _⟩ => (match rty.find? k with
        | .some qty => instanceOfType v qty.getType
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

def instanceOfRequestType (request : Request) (reqty : RequestType) : Bool :=
  instanceOfEntityType request.principal reqty.principal &&
  request.action == reqty.action &&
  instanceOfEntityType request.resource reqty.resource &&
  instanceOfType request.context (.record reqty.context)

/--
For every entity in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
-/
def instanceOfEntitySchema (entities : Entities) (ets : EntitySchema) : EntityValidationResult :=
  entities.toList.forM λ (uid, data) => instanceOfEntityData uid data
where
  instanceOfEntityData uid data :=
    match ets.find? uid.ty with
    |  .some entry => if instanceOfType data.attrs (.record entry.attrs) then
                    if data.ancestors.all (λ ancestor => entry.ancestors.contains ancestor.ty) then .ok ()
                   else .error (.typeError s!"entity ancestors inconsistent with type store information")
                  else .error (.typeError "entity attributes do not match type store")
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

def requestMatchesEnvironment (env : Environment) (request : Request) : Bool := instanceOfRequestType request env.reqty

def validateRequest (schema : Schema) (request : Request) : RequestValidationResult :=
  if ((schema.toEnvironments.any (requestMatchesEnvironment · request)))
  then .ok ()
  else .error (.typeError "request could not be validated in any environment")

def entitiesMatchEnvironment (env : Environment) (entities : Entities) : EntityValidationResult :=
instanceOfEntitySchema entities env.ets >>= λ _ => instanceOfActionSchema entities env.acts

def actionSchemaEntryToEntityData (ase : ActionSchemaEntry) : EntityData := {
  ancestors := ase.ancestors,
  attrs := Map.empty
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
      let allAncestorsForType := List.join (entriesWithType.values.map (λ edt =>
        edt.ancestors.elts.map (·.ty) ))
      let ese : EntitySchemaEntry := {
        ancestors := Set.make allAncestorsForType,
        attrs := Map.empty
      }
      (ty, ese)

def validateEntities (schema : Schema) (entities : Entities) : EntityValidationResult :=
  let actionEntities := (schema.acts.mapOnValues actionSchemaEntryToEntityData)
  let entities := Map.make (entities.kvs ++ actionEntities.kvs)
  let schema := updateSchema schema actionEntities
  schema.toEnvironments.forM (entitiesMatchEnvironment · entities)
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
