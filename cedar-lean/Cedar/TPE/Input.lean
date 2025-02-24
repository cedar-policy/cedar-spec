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

import Cedar.Spec.Value
import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Validation.TypedExpr
import Cedar.Validation.RequestEntityValidator

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

structure PartialEntityUID where
  ty : EntityType                    -- Entity type is always known,
  id : Option String                 -- but entity id may not be.

def PartialEntityUID.asEntityUID (self : PartialEntityUID) : Option EntityUID :=
  self.id.map λ x ↦ ⟨ self.ty, x⟩

structure PartialRequest where
  principal : PartialEntityUID
  action : EntityUID
  resource : PartialEntityUID
  context :  Option (Map Attr Value)

structure PartialEntityData where
  attrs : Option (Map Attr Value)
  ancestors : Option (Set EntityUID)
  tags : Option (Map Attr Value)

abbrev PartialEntities := Map EntityUID PartialEntityData

def NoneIsTrue {α} (o : Option α) (f : α → Bool) : Bool :=
  match o with
  | .some v => f v
  | .none => true

def RequestIsValid (env : Environment) (req : PartialRequest) : Bool :=
  (NoneIsTrue req.principal.asEntityUID λ principal ↦
    instanceOfEntityType principal principal.ty env.ets.entityTypeMembers?) &&
  (NoneIsTrue req.resource.asEntityUID λ resource ↦
    instanceOfEntityType resource resource.ty env.ets.entityTypeMembers?) &&
  (NoneIsTrue req.context λ m ↦
    instanceOfType (.record m) (.record env.reqty.context) env.ets)

def EntitiesIsValid (env : Environment) (es : PartialEntities) : Bool :=
  (es.toList.all EntityIsValid) && (env.acts.toList.all instanceOfActionSchema)
where
  EntityIsValid p :=
  let (uid, ⟨attrs, ancestors, tags⟩) := p
  match env.ets.find? uid.ty with
  | .some entry =>
    entry.isValidEntityEID uid.eid &&
    (NoneIsTrue ancestors λ ancestors ↦
      ancestors.all (λ ancestor =>
      entry.ancestors.contains ancestor.ty &&
      instanceOfEntityType ancestor ancestor.ty env.ets.entityTypeMembers?)) &&
    (NoneIsTrue attrs λ attrs ↦
      instanceOfType attrs (.record entry.attrs) env.ets) &&
    (NoneIsTrue tags λ tags ↦
      match entry.tags? with
    | .some tty => tags.values.all (instanceOfType · tty env.ets)
    | .none     => tags == Map.empty)
  | .none => false
  instanceOfActionSchema p :=
    let (uid, entry) := p
    match es.find? uid with
      | .some entry₁ => entry.ancestors == entry₁.ancestors
      | _ => false

def RequestAndEntitiesIsValid (env : Environment) (req : PartialRequest) (es : PartialEntities) : Bool :=
  RequestIsValid env req && EntitiesIsValid env es

end Cedar.TPE
