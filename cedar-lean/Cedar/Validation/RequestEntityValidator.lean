import Cedar.Validation
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

def requiredAttributesPresent (r : Map Attr Value) (rty : Map Attr (Qualified CedarType)) (k : Attr) :=
match rty.find? k with
    | .some qty => if qty.isRequired then r.contains k else true
    | _ => true

def instanceOfType (v : Value) (ty : CedarType) : Bool := match v, ty with
| .prim (.bool b), .bool bty => instanceOfBoolType b bty
| .prim (.int _), .int => true
| .prim (.string _), .string => true
| .prim (.entityUID e), .entity ety => instanceOfEntityType e ety
| .set s, .set ty => (s.elts.attach.map (λ ⟨v, _⟩ => instanceOfType v ty)).all id
| .record r, .record rty =>
  r.keys.all rty.keys.contains &&
  (r.kvs.attach₂.all (λ ⟨(k, v), _⟩ => (match h₀ : rty.find? k with
      | .some qty => instanceOfType v qty.getType
      | _ => true))) &&
  rty.keys.all (requiredAttributesPresent r rty)
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

def instanceOfRequestType (request : Request) (reqty : RequestType) : Except RequestValidationError Unit :=
  if instanceOfEntityType request.principal reqty.principal then
    if request.action == reqty.action then
      if instanceOfEntityType request.resource reqty.resource then
        if instanceOfType request.context (.record reqty.context) then .ok ()
        else .error (.typeError "context")
      else .error (.typeError "resource")
    else .error (.typeError "action")
  else .error (.typeError "principal")
/--
For every entity in the store,
1. The entity's type is defined in the type store.
2. The entity's attributes match the attribute types indicated in the type store.
3. The entity's ancestors' types are consistent with the ancestor information
   in the type store.
-/

def instanceOfEntitySchema (entities : Entities) (ets : EntitySchema) : EntityValidationResult :=
entities.toList.forM (λ (uid, data) => match ets.find? uid.ty with
  | .some entry => if instanceOfType data.attrs (.record entry.attrs) then
                    if data.ancestors.all (λ ancestor => entry.ancestors.contains ancestor.ty) then .ok ()
                   else .error (.typeError "entity ancestors inconsistent with type store information")
                  else .error (.typeError "entity attributes do not match type store")
  | _ => .error (.typeError "entity type not defined in type store"))

/--
For every action in the entity store, the action's ancestors are consistent
with the ancestor information in the action store.
-/
def instanceOfActionSchema (entities : Entities) (as : ActionSchema) : EntityValidationResult :=
entities.toList.forM (λ (uid, data) => match as.find? uid with
  | .some entry => if data.ancestors == entry.ancestors then .ok () else .error (.typeError "action ancestors inconsistent with type store information")
  | _ => .error (.typeError "action type not defined in type store"))

def requestMatchesEnvironment (env : Environment) (request : Request) : RequestValidationResult := instanceOfRequestType request env.reqty

def validateRequest (schema : Schema) (request : Request) : RequestValidationResult := schema.toEnvironments.forM (requestMatchesEnvironment · request)

def entitiesMatchEnvironment (env : Environment) (entities : Entities) : EntityValidationResult :=
instanceOfEntitySchema entities env.ets >>= λ _ => instanceOfActionSchema entities env.acts

def validateEntities (schema : Schema) (entities : Entities) : EntityValidationResult := schema.toEnvironments.forM (entitiesMatchEnvironment · entities)

end Cedar.Validation


-- json

deriving instance Lean.ToJson for Cedar.Validation.EntityValidationError
deriving instance Lean.ToJson for Cedar.Validation.RequestValidationError
