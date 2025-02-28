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
structure PartialEntityData where
  attrs     : Option (Map Attr Value)
  ancestors : Option (Set EntityUID)
  tags      : Option (Map Attr Value)

abbrev PartialEntities := Map EntityUID PartialEntityData

private def PartialEntities.get (es : PartialEntities) (uid : EntityUID) (f : PartialEntityData → Option α) : Option α :=
  (es.find? uid).bind f

def PartialEntities.ancestors (es : PartialEntities) (uid : EntityUID) : Option (Set EntityUID) := es.get uid PartialEntityData.ancestors

def PartialEntities.tags (es : PartialEntities) (uid : EntityUID) : Option (Map Tag Value) := es.get uid PartialEntityData.tags

def PartialEntities.attrs (es : PartialEntities) (uid : EntityUID) : Option (Map Tag Value) := es.get uid PartialEntityData.attrs

def partialIsValid {α} (o : Option α) (f : α → Bool) : Bool :=
  (o.map f).getD true

def requestIsValid (env : Environment) (req : PartialRequest) : Bool :=
  (partialIsValid req.principal.asEntityUID λ principal =>
    instanceOfEntityType principal principal.ty env.ets.entityTypeMembers?) &&
  (partialIsValid req.resource.asEntityUID λ resource =>
    instanceOfEntityType resource resource.ty env.ets.entityTypeMembers?) &&
  (partialIsValid req.context λ m =>
    instanceOfType (.record m) (.record env.reqty.context) env.ets)

def entitiesIsValid (env : Environment) (es : PartialEntities) : Bool :=
  (es.toList.all entityIsValid) && (env.acts.toList.all instanceOfActionSchema)
where
  entityIsValid p :=
    let (uid, ⟨attrs, ancestors, tags⟩) := p
    match env.ets.find? uid.ty with
    | .some entry =>
      entry.isValidEntityEID uid.eid &&
      (partialIsValid ancestors λ ancestors =>
        ancestors.all (λ ancestor =>
        entry.ancestors.contains ancestor.ty &&
        instanceOfEntityType ancestor ancestor.ty env.ets.entityTypeMembers?)) &&
      (partialIsValid attrs (instanceOfType · (.record entry.attrs) env.ets)) &&
      (partialIsValid tags λ tags =>
        match entry.tags? with
        | .some tty => tags.values.all (instanceOfType · tty env.ets)
        | .none     => tags == Map.empty)
    | .none       => false
  instanceOfActionSchema p :=
    let (uid, entry) := p
    match es.find? uid with
    | .some entry₁ => entry.ancestors == entry₁.ancestors
    | _            => false

def requestAndEntitiesIsValid (env : Environment) (req : PartialRequest) (es : PartialEntities) : Bool :=
  requestIsValid env req && entitiesIsValid env es

inductive ConcretizationError
  | typeError
  | requestsDoNotMatch
  | entitiesDoNotMatch

def isConsistent (env : Environment) (req₁ : Request) (es₁ : Entities) (req₂ : PartialRequest) (es₂ : PartialEntities) : Except ConcretizationError Unit :=
  do requestIsConsistent; entitiesIsConsistent
where
  requestIsConsistent :=
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
  entitiesIsConsistent : Except ConcretizationError Unit :=
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
          let ⟨attrs₂, ancestors₂, tags₂⟩ := e₂
          partialIsValid attrs₂ (· = attrs₁) &&
          partialIsValid ancestors₂ (· = ancestors₁) &&
          partialIsValid tags₂ (· = tags₁)
        | .none => false

end Cedar.TPE
