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

structure PartialRequest where
  principal : PartialEntityUID
  action    : EntityUID
  resource  : PartialEntityUID
  -- We don't need type annotation here because the value of `context` can only
  -- be accessed via evaluating a `TypedExpr`, which allows us to obtain a
  -- (typed) `Residual`
  context   : Option (Map Attr Value)


-- We don't need type annotations here following the rationale above
inductive PartialEntityData where
  | present (attrs : Option (Map Attr Value)) (ancestors : Option (Set EntityUID)) (tags : Option (Map Attr Value))
  | absent

abbrev PartialEntities := Map EntityUID PartialEntityData

def PartialEntities.get (es : PartialEntities) (uid : EntityUID) (f : PartialEntityData → Option α) : Option α :=
  (es.find? uid).bind f

def PartialEntityData.ancestors : PartialEntityData → Option (Set EntityUID)
  | .present _ ancestors _ => ancestors
  | .absent => .some Set.empty

def PartialEntityData.tags : PartialEntityData → Option (Map Tag Value)
  | .present _ _ tags => tags
  | .absent => .some Map.empty

def PartialEntityData.attrs : PartialEntityData → Option (Map Attr Value)
  | .present attrs _ _ => attrs
  | .absent => .some Map.empty

def PartialEntities.ancestors (es : PartialEntities) (uid : EntityUID) : Option (Set EntityUID) := es.get uid PartialEntityData.ancestors

def PartialEntities.tags (es : PartialEntities) (uid : EntityUID) : Option (Map Tag Value) := es.get uid PartialEntityData.tags

def PartialEntities.attrs (es : PartialEntities) (uid : EntityUID) : Option (Map Tag Value) := es.get uid PartialEntityData.attrs

def partialIsValid {α} (o : Option α) (f : α → Bool) : Bool :=
  (o.map f).getD true

def requestIsValid (env : TypeEnv) (req : PartialRequest) : Bool :=
  (partialIsValid req.principal.asEntityUID λ principal =>
    instanceOfEntityType principal env.reqty.principal env) &&
  req.action == env.reqty.action &&
  (partialIsValid req.resource.asEntityUID λ resource =>
    instanceOfEntityType resource env.reqty.resource env) &&
  (partialIsValid req.context λ m =>
    instanceOfType (.record m) (.record env.reqty.context) env)

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
      (partialIsValid attrs (instanceOfType · (.record entry.attrs) env)) &&
      (partialIsValid tags λ tags =>
        match entry.tags? with
        | .some tty => tags.values.all (instanceOfType · tty env)
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
      partialIsValid c₂ (· = c₁)
    then
      .ok ()
    else
      .error .requestsDoNotMatch
  entitiesIsConsistent env : Except ConcretizationError Unit :=
    if !entitiesIsValid env es₂ || !(entitiesMatchEnvironment env es₁).isOk
    then
      .error .typeError
    else
      if entitiesMatch then
        .ok ()
      else
        .error .entitiesDoNotMatch
  entitiesMatch :=
      es₂.kvs.all λ (a₂, e₂) => match es₁.find? a₂ with
        | .some e₁ =>
          let ⟨attrs₁, ancestors₁, tags₁⟩ := e₁
          partialIsValid e₂.attrs (· = attrs₁) &&
          partialIsValid e₂.ancestors (· = ancestors₁) &&
          partialIsValid e₂.tags (· = tags₁)
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

def Request.asPartialRequest (req : Request) : PartialRequest :=
  { principal := { ty := req.principal.ty, id := .some req.principal.eid }
  , action    := req.action
  , resource  := { ty := req.resource.ty, id := .some req.resource.eid }
  , context   := req.context }



end Cedar.Spec


namespace Cedar.Spec
open Cedar.TPE

def EntityData.asPartial (data : EntityData) : PartialEntityData :=
  .present (.some data.attrs) (.some data.ancestors) (.some data.tags)

def Entities.asPartial (entities: Entities) : PartialEntities :=
  entities.mapOnValues EntityData.asPartial

end Cedar.Spec
