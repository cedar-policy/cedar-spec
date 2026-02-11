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

import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Spec.Value
import Cedar.Validation.RequestEntityValidator
import Cedar.Validation.EnvironmentValidator
import Cedar.Validation.TypedExpr

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

structure PartialEntityUID where
  ty : EntityType
  id : Option String

def PartialEntityUID.asEntityUID (self : PartialEntityUID) : Option EntityUID :=
  self.id.map (⟨self.ty, ·⟩)

inductive PartialAttribute (T : Type _) where
  | present (val : T)               -- Known present, known value
  | absent (ty : CedarType)         -- Known absent, no value
  | presentUnknown (ty : CedarType) -- Known present, unknown value
  | unknown (ty : CedarType)        -- Unknown present, unknown value

deriving instance Repr, DecidableEq, Inhabited for PartialAttribute

def PartialAttribute.mustBePresent : PartialAttribute T → Bool
| present _ | presentUnknown _ => true
| absent _ | unknown _ => false

inductive PartialValue where
  | prim (p : Prim)
  | set (s : Set Value) -- Per Emina's design, sets cannot have partial values. TODO: understand why
  | record (m : Map Attr (PartialAttribute PartialValue))
  | ext (x : Ext)

deriving instance Repr, Inhabited for PartialValue
instance : DecidableEq PartialValue := by sorry

def PartialValue.asEntityUID : PartialValue → Result EntityUID
  | .prim (.entityUID uid) => .ok uid
  | _ => .error Error.typeError

def PartialValue.asSet : PartialValue → Result (Data.Set Value)
  | .set s => .ok s
  | _ => .error Error.typeError

def PartialValue.asBool : PartialValue → Result Bool
  | .prim (.bool b) => .ok b
  | _ => .error Error.typeError

def PartialValue.asString : PartialValue →  Result String
  | .prim (.string s) => .ok s
  | _ => .error Error.typeError

def PartialValue.asInt : PartialValue →  Result Int64
  | .prim (.int i) => .ok i
  | _ => .error Error.typeError

instance : Coe PartialValue (Result Bool) where
  coe v := v.asBool

instance : Coe PartialValue (Result Int64) where
  coe v := v.asInt

instance : Coe PartialValue (Result String) where
  coe v := v.asString

instance : Coe PartialValue (Result EntityUID) where
  coe v := v.asEntityUID

instance : Coe PartialValue (Result (Data.Set Value)) where
  coe v := v.asSet

abbrev PartialAttributes := Option (Map Attr (PartialAttribute PartialValue))
abbrev PartialTags := Option (Map Tag (PartialAttribute PartialValue))

structure PartialRequest where
  principal : PartialEntityUID
  action    : EntityUID
  resource  : PartialEntityUID
  -- We don't need type annotation here because the value of `context` can only
  -- be accessed via evaluating a `TypedExpr`, which allows us to obtain a
  -- (typed) `Residual`
  context   : PartialAttributes

-- We don't need type annotations here following the rationale above
structure PartialEntityData where
  attrs     : PartialAttributes
  ancestors : Option (Set EntityUID)
  tags      : PartialTags

abbrev MaybeEntityData := Option EntityData

abbrev PartialEntities := Map EntityUID PartialEntityData

/--
A subset of an Entities store.
When a `MaybeEntityData` is `none`, it means that the entity is not present in
the backing store.
-/
abbrev SlicedEntities := Map EntityUID MaybeEntityData



def PartialEntities.get (es : PartialEntities) (uid : EntityUID) (f : PartialEntityData → Option α) : Option α :=
  (es.find? uid).bind f

def PartialEntities.ancestors (es : PartialEntities) (uid : EntityUID) : Option (Set EntityUID) := es.get uid PartialEntityData.ancestors

def PartialEntities.tags (es : PartialEntities) (uid : EntityUID) : PartialTags := es.get uid PartialEntityData.tags

def PartialEntities.attrs (es : PartialEntities) (uid : EntityUID) : PartialAttributes := es.get uid PartialEntityData.attrs

def partialIsValid {α} (o : Option α) (f : α → Bool) : Bool :=
  (o.map f).getD true

def requiredAttributePresent (r : Map Attr (PartialAttribute PartialValue)) (rty : Map Attr (Qualified CedarType)) (k : Attr) :=
  match rty.find? k with
  | .some qty =>
    -- TODO: if the expected qty is optional. Then do we need to not .none?
    -- .none might be ambiguous
    -- should be an error
    !qty.isRequired ||
    match r.find? k with
    | .some (.present _)
    | .some (.presentUnknown _)
    | .some (.unknown _) => true
    | .some (.absent _) | .none => false
  | _ => true

def PartialValue.instanceOfType (v : PartialValue) (ty : CedarType) (env : TypeEnv) : Bool :=
  match v, ty with
  | .prim (.bool b), .bool bty => instanceOfBoolType b bty
  | .prim (.int _), .int => true
  | .prim (.string _), .string => true
  | .prim (.entityUID e), .entity ety => instanceOfEntityType e ety env
  | .set s, .set ty => s.elts.attach.all (λ ⟨v, _⟩ => Value.instanceOfType v ty env)
  | .record r, .record rty =>
    r.kvs.all (λ (k, _) => rty.contains k) &&
    (r.kvs.attach₂.all (λ ⟨(k, v), _⟩ => (match rty.find? k with
        | .some qty =>
          match v with
          | .present v => instanceOfType v qty.getType env
          | .absent ty
          | .presentUnknown ty
          | .unknown ty => ty == qty.getType
        | _ => true))) &&
    rty.kvs.all (λ (k, _) => requiredAttributePresent r rty k)
  | .ext x, .ext xty => instanceOfExtType x xty
  | _, _ => false
    termination_by v
    decreasing_by
      all_goals simp_wf
      case _ h₁ =>
        sorry

def requestIsValid (env : TypeEnv) (req : PartialRequest) : Bool :=
  (partialIsValid req.principal.asEntityUID λ principal =>
    instanceOfEntityType principal env.reqty.principal env) &&
  req.action == env.reqty.action &&
  (partialIsValid req.resource.asEntityUID λ resource =>
    instanceOfEntityType resource env.reqty.resource env) &&
  (partialIsValid req.context λ m =>
    PartialValue.instanceOfType (.record m) (.record env.reqty.context) env)

def entitiesIsValid (env : TypeEnv) (es : PartialEntities) : Bool :=
  (es.toList.all entityIsValid) && (env.acts.toList.all instanceOfActionSchema)
where
  entityIsValid p :=
    let (uid, entityData) := p
    let (attrs, ancestors, tags) := (entityData.attrs, entityData.ancestors, entityData.tags)
    match env.ets.find? uid.ty with
    | .some entry =>
      entry.isValidEntityEID uid.eid &&
      (partialIsValid ancestors λ ancestors =>
        ancestors.all (λ ancestor =>
        entry.ancestors.contains ancestor.ty &&
        instanceOfEntityType ancestor ancestor.ty env)) &&
      (partialIsValid attrs (λ attrs => PartialValue.instanceOfType (.record attrs)  (.record entry.attrs) env)) &&
      (partialIsValid tags λ tags =>
        match entry.tags? with
        | .some tty => tags.values.all (λ v =>
          match v with
          | .present v => PartialValue.instanceOfType v tty env
          | .absent ty
          | .presentUnknown ty
          | .unknown ty => ty == tty)
        | .none     => tags == Map.empty)
    | .none       => false
  instanceOfActionSchema p :=
    let (uid, entry) := p
    match es.find? uid with
    | .some entry₁ => entry.ancestors == entry₁.ancestors
    | _            => false

def requestAndEntitiesIsValid (env : TypeEnv) (req : PartialRequest) (es : PartialEntities) : Bool :=
  requestIsValid env req && entitiesIsValid env es

inductive ConcretizationError
  | typeError
  | requestsDoNotMatch
  | entitiesDoNotMatch
  | invalidEnvironment

def isValidAndConsistent (schema : Schema) (req₁ : Request) (es₁ : Entities) (req₂ : PartialRequest) (es₂ : PartialEntities) : Except ConcretizationError Unit :=
  match schema.environment? req₂.principal.ty req₂.resource.ty req₂.action with
  | .some env => do requestIsConsistent env; entitiesIsConsistent env; envIsWellFormed env
  | .none => .error .invalidEnvironment
where
  valueIsConsistent (env : TypeEnv) (v : Value) (pv : PartialValue) :=
    match v, pv with
    | .prim p, .prim p' => p == p'
    | .ext x, .ext x' => x == x'
    | .set s, .set s' => s == s'
    | .record a, .record a' =>
      (a'.kvs.attach₂.all λ kv=>
        match a.find? kv.val.fst, kv.val.snd with
        | .some v, .present v' =>
          valueIsConsistent env v v'
        | .some v, .unknown ty
        | .some v, .presentUnknown ty => Value.instanceOfType v ty env
        | .some v, .absent _ => false
        | .none, .present _
        | .none, .presentUnknown _ => false
        | .none, .unknown _
        | .none, .absent _ => true) &&
      (a.kvs.all λ (k, v) =>
        match a'.find? k with
        | .some (.present _)
        | .some (.unknown _)
        | .some (.presentUnknown _) => true
        | .some (.absent _)
        | .none => false)
    | _, _ => false
  termination_by pv
  decreasing_by sorry

  requestIsConsistent env :=
  if !requestIsValid env req₂ || !requestMatchesEnvironment env req₁
  then
    .error .typeError
  else
    let ⟨p₁, a₁, r₁, c₁⟩ := req₁
    let ⟨p₂, a₂, r₂, c₂⟩ := req₂
    if partialIsValid p₂.asEntityUID (· = p₁) &&
      a₁ = a₂ &&
      partialIsValid r₂.asEntityUID (· = r₁) &&
      partialIsValid c₂ (λ c₂ => valueIsConsistent env (.record c₁) (.record c₂))
    then
      .ok ()
    else
      .error .requestsDoNotMatch
  entitiesIsConsistent env : Except ConcretizationError Unit :=
    if !entitiesIsValid env es₂ || !(entitiesMatchEnvironment env es₁).isOk
    then
      .error .typeError
    else
      if entitiesMatch env then
        .ok ()
      else
        .error .entitiesDoNotMatch
  entitiesMatch env :=
      es₂.kvs.all λ (a₂, e₂) => match es₁.find? a₂ with
        | .some e₁ =>
          let ⟨attrs₁, ancestors₁, tags₁⟩ := e₁
          partialIsValid e₂.attrs (λ a₂ => valueIsConsistent env (.record attrs₁) (.record a₂)) &&
          partialIsValid e₂.ancestors (· = ancestors₁) &&
          partialIsValid e₂.tags (λ t₂ => valueIsConsistent env (.record tags₁) (.record t₂))
        | .none => false
  envIsWellFormed env : Except ConcretizationError Unit :=
    if !env.validateWellFormed.isOk
    then
      .error .typeError
    else
      .ok ()

end Cedar.TPE

namespace Cedar.Spec

open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

def Value.asPartialValue : Value → PartialValue
  | .prim p => .prim p
  | .ext x => .ext x
  | .set s => .set s
  | .record as => .record ∘ Map.mk $ as.kvs.attach₂.map λ kv => (kv.val.fst, .present kv.val.snd.asPartialValue)
decreasing_by
  have : sizeOf as.kvs < sizeOf as := by
    simp only [Map.sizeOf_lt_of_kvs]
  simp only [record.sizeOf_spec, gt_iff_lt]
  omega

instance : Coe Bool PartialValue where
  coe b := .prim (.bool b)

instance {α : Type _} [Coe α Value] : Coe α PartialValue where
  coe v := Value.asPartialValue v

def Request.asPartialRequest (req : Request) : PartialRequest :=
  { principal := { ty := req.principal.ty, id := .some req.principal.eid }
  , action    := req.action
  , resource  := { ty := req.resource.ty, id := .some req.resource.eid }
  , context   := .some ∘ Map.mk $ req.context.kvs.attach₂.map λ kv => (kv.val.fst, .present kv.val.snd.asPartialValue) }

open Cedar.TPE

def EntityData.asPartial (data : EntityData) : PartialEntityData :=
  { attrs := (.some ∘ Map.mk $ data.attrs.kvs.attach₂.map λ kv => (kv.val.fst, .present kv.val.snd.asPartialValue))
  , ancestors := (.some data.ancestors)
  , tags := (.some ∘ Map.mk $ data.tags.kvs.attach₂.map λ kv => (kv.val.fst, .present kv.val.snd.asPartialValue))}

def Entities.asPartial (entities: Entities) : PartialEntities :=
  entities.mapOnValues EntityData.asPartial


end Cedar.Spec


namespace Cedar.TPE
open Cedar.Data

/-- subtle: a missing entity bahaves the same way as a concrete entity
with empty attrs, ancestors, and tags.
This is because
1. Cedar doesn't have a way to check for a presence of a particular entity id in the database.
2. Each of the cedar operations behave the same way when encountering a missing entity compared to a empty one.

This is a necessary condition for the soundness of batched entity loading.
-/
def MaybeEntityData.asPartial :
  MaybeEntityData → PartialEntityData
| none =>
  { attrs :=  (.some Map.empty)
  , ancestors := (.some Set.empty)
  , tags := (.some Map.empty)}
| some d =>
  d.asPartial

def EntitiesWithMissing.asPartial (store: SlicedEntities) : PartialEntities :=
  store.mapOnValues MaybeEntityData.asPartial

end Cedar.TPE
