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
import Cedar.TPE.Value
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
deriving Inhabited

def PartialEntityUID.asEntityUID (self : PartialEntityUID) : Option EntityUID :=
  self.id.map (⟨self.ty, ·⟩)

structure PartialRequest where
  principal : PartialEntityUID
  action    : EntityUID
  resource  : PartialEntityUID
  -- We don't need type annotation here because the value of `context` can only
  -- be accessed via evaluating a `TypedExpr`, which allows us to obtain a
  -- (typed) `Residual`
  context   : Option PartialRecord
deriving Inhabited


-- We don't need type annotations here following the rationale above
structure PartialEntityData where
  attrs     : Option PartialRecord
  ancestors : Option (Set EntityUID)
  tags      : Option PartialRecord
deriving Inhabited

abbrev MaybeEntityData := Option EntityData

abbrev PartialEntities := Map EntityUID PartialEntityData

deriving instance Inhabited for PartialEntities

/--
A subset of an Entities store.
When a `MaybeEntityData` is `none`, it means that the entity is not present in
the backing store.
-/
abbrev SlicedEntities := Map EntityUID MaybeEntityData



def PartialEntities.get (es : PartialEntities) (uid : EntityUID) (f : PartialEntityData → Option α) : Option α :=
  (es.find? uid).bind f

def PartialEntities.ancestors (es : PartialEntities) (uid : EntityUID) : Option (Set EntityUID) := es.get uid PartialEntityData.ancestors

def PartialEntities.tags (es : PartialEntities) (uid : EntityUID) : Option PartialRecord := es.get uid PartialEntityData.tags

def PartialEntities.attrs (es : PartialEntities) (uid : EntityUID) : Option PartialRecord := es.get uid PartialEntityData.attrs



def partialIsValid {α} (o : Option α) (f : α → Bool) : Bool :=
  (o.map f).getD true

mutual

/--
Is `r` a valid record of type `rty`
-/
def partialRecordIsValid (schema : Schema) (r : PartialRecord) (rty : RecordType) : Bool :=
  r.toList.attach₂.all λ x =>
    match rty.find? x.val.fst with
    -- The partial record can't define an attribute as existing if it's not in the type.
    -- This allows explicitly absent attributes, but also an explicitly unknown attribute which
    -- could never exist in a valid concrete record of the same type.
    | .none => !x.val.snd.exists?
    | .some qty =>
      match x.val.snd with
      | .absent => !qty.isRequired
      | _ =>
        have : sizeOf x.val.snd < sizeOf r := by
          have h := x.property
          cases r
          simp only [Map.toList_mk_id, Map.mk.sizeOf_spec] at *
          omega
        attrStateIsValidAt schema x.val.snd qty.getType
termination_by sizeOf r

/--
Is this a valid attribute with type `ty`.
-/
def attrStateIsValidAt (schema : Schema) (s : AttrState) (ty : CedarType) : Bool :=
  match s with
  | .value v => instanceOfType v ty schema
  | .partialRecord r =>
    match ty with
    | .record rty => partialRecordIsValid schema r rty
    | _           => false
  | .present
  | .absent
  | .unknown => true
termination_by sizeOf s

end

/--
Any tag key may exist, but if the schema declares no tag type then none may.
-/
def partialTagsAreValid (schema : Schema) (tags : PartialRecord) (tty? : Option CedarType) : Bool :=
  match tty? with
  | .some tty => tags.toList.all λ (_, s) => attrStateIsValidAt schema s tty
  | .none => tags.toList.all λ (_, s) => !s.exists?

def requestIsValid (env : TypeEnv) (req : PartialRequest) : Bool :=
  (partialIsValid req.principal.asEntityUID λ principal =>
    instanceOfEntityType principal env.reqty.principal env.schema) &&
  req.action == env.reqty.action &&
  (partialIsValid req.resource.asEntityUID λ resource =>
    instanceOfEntityType resource env.reqty.resource env.schema) &&
  (partialIsValid req.context λ r =>
    partialRecordIsValid env.schema r env.reqty.context)

def validatePartialRequest (schema : Schema) (req : PartialRequest) : Except RequestValidationError TypeEnv :=
  match schema.environment? req.principal.ty req.resource.ty req.action with
  | .some env =>
    if requestIsValid env req
    then .ok env
    else .error (.typeError "partial request is inconsistent with the type store")
  | .none => .error (.typeError "partial request does not match any environment")

def entitiesIsValid (schema : Schema) (es : PartialEntities) : Bool :=
  (es.toList.all entityIsValid) && (schema.acts.toList.all instanceOfActionSchema)
where
  actionEntityIsValid uid entityData : Bool :=
    match schema.acts.find? uid with
    | .some actionEntry =>
      partialIsValid entityData.ancestors (· == actionEntry.ancestors) &&
      partialIsValid entityData.attrs (·.toList.isEmpty) &&
      partialIsValid entityData.tags (·.toList.isEmpty)
    | .none => true
  entityIsValid p :=
    let (uid, entityData) := p
    let (attrs, ancestors, tags) := (entityData.attrs, entityData.ancestors, entityData.tags)
    match schema.ets.find? uid.ty with
    | .some entry =>
      entry.isValidEntityEID uid.eid &&
      (partialIsValid ancestors λ ancestors =>
        ancestors.all (λ ancestor =>
        entry.ancestors.contains ancestor.ty &&
        instanceOfEntityType ancestor ancestor.ty schema)) &&
      (partialIsValid attrs (partialRecordIsValid schema · entry.attrs)) &&
      (partialIsValid tags (partialTagsAreValid schema · entry.tags?))
    | .none => actionEntityIsValid uid entityData
  instanceOfActionSchema p :=
    let (uid, _) := p
    match es.find? uid with
    | .some entry₁ => actionEntityIsValid uid entry₁
    | _            => true

/-- Every known component of `req₂` agrees with `req₁`. -/
def requestIsConsistent (req₁ : Request) (req₂ : PartialRequest) : Bool :=
  let ⟨p₁, a₁, r₁, c₁⟩ := req₁
  let ⟨p₂, a₂, r₂, c₂⟩ := req₂
  p₂.ty = p₁.ty &&
  r₂.ty = r₁.ty &&
  partialIsValid p₂.asEntityUID (· = p₁) &&
  a₁ = a₂ &&
  partialIsValid r₂.asEntityUID (· = r₁) &&
  partialIsValid c₂ (λ r => r.wellFormed && c₁.wellFormed && r.consistentWith c₁)

/-- Every entity of `es₂` is in `es₁`, and every known component of it agrees with `es₁`. -/
def entitiesIsConsistent (es₁ : Entities) (es₂ : PartialEntities) : Bool :=
  es₂.toList.all λ (a₂, e₂) => match es₁.find? a₂ with
    | .some e₁ =>
      let ⟨attrs₁, ancestors₁, tags₁⟩ := e₁
      partialIsValid e₂.attrs (·.consistentWith attrs₁) &&
      partialIsValid e₂.ancestors (· = ancestors₁) &&
      partialIsValid e₂.tags (·.consistentWith tags₁)
    | .none => false

inductive ConcretizationError
  | typeError
  | requestsDoNotMatch
  | entitiesDoNotMatch
  | invalidEnvironment

def isValidAndConsistent (schema : Schema) (req₁ : Request) (es₁ : Entities) (req₂ : PartialRequest) (es₂ : PartialEntities) : Except ConcretizationError Unit :=
  match validatePartialRequest schema req₂ with
  | .ok env => do requestIsValidAndConsistent env; entitiesIsValidAndConsistent env; envIsWellFormed env
  | .error _ => .error .invalidEnvironment
where
  requestIsValidAndConsistent env :=
  if !requestMatchesEnvironment env req₁
  then
    .error .typeError
  else
    if requestIsConsistent req₁ req₂
    then
      .ok ()
    else
      .error .requestsDoNotMatch
  entitiesIsValidAndConsistent env : Except ConcretizationError Unit :=
    if !entitiesIsValid env.schema es₂ || !(entitiesMatchEnvironment env es₁).isOk
    then
      .error .typeError
    else
      if entitiesIsConsistent es₁ es₂ then
        .ok ()
      else
        .error .entitiesDoNotMatch
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

def Request.asPartialRequest (req : Request) (ctxTy : RecordType) : PartialRequest :=
  { principal := { ty := req.principal.ty, id := .some req.principal.eid }
  , action    := req.action
  , resource  := { ty := req.resource.ty, id := .some req.resource.eid }
  , context   := .some (PartialRecord.ofConcrete req.context ctxTy) }

open Cedar.TPE

def EntityData.asPartial (data : EntityData) (rty : RecordType) : PartialEntityData :=
  { attrs := .some (PartialRecord.ofConcrete data.attrs rty)
  , ancestors := (.some data.ancestors)
  , tags := (.some (PartialRecord.ofConcreteTags data.tags)) }

end Cedar.Spec


namespace Cedar.TPE
open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def attrsOrEmpty (ets : EntitySchema) (ety : EntityType) : RecordType :=
  (ets.attrs? ety).getD Map.empty

def Entities.asPartial (ets : EntitySchema) (entities : Entities) : PartialEntities :=
  Map.mk (entities.toList.map λ (uid, data) => (uid, data.asPartial (attrsOrEmpty ets uid.ty)))

/--
Convert the entities returned by a batched loader into partial data.

A `none` means the store has no such entity. It is omitted rather than recorded with empty
attributes: an entry in the partial store is taken to exist, and `resolveAttr` may report a
required attribute as `present`, which is sound only for an entity that really exists. The uid
may be requested again on a later iteration.
-/
def SlicedEntities.asPartial (ets : EntitySchema) (store : SlicedEntities) : PartialEntities :=
  Map.mk (store.toList.filterMap λ (uid, data?) =>
    data?.map λ data => (uid, data.asPartial (attrsOrEmpty ets uid.ty)))

end Cedar.TPE
