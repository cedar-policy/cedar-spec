/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Spec.Entities
import Cedar.Spec.PartialValue

/-!
This file defines Cedar partial-entities structures.
-/

namespace Cedar.Spec

open Cedar.Data

/--
Represents the information about one entity.

Currently, this allows attrs to be known-to-exist-but-unknown-value,
but does not allow attrs to be unknown-whether-they-exist-entirely.
(the result of `e has attr` is never a residual for an `e` that is known to exist.)

Currently, this does not allow any unknowns about ancestor information.
All ancestor information must be fully concrete.
-/
structure PartialEntityData where
  attrs : Map Attr RestrictedPartialValue
  ancestors : Set EntityUID

def EntityData.asPartialEntityData (d : EntityData) : PartialEntityData :=
  {
    attrs := d.attrs.mapOnValues RestrictedPartialValue.value,
    ancestors := d.ancestors,
  }

/--
Represents the information about all entities.

Currently, this does not allow it to be unknown whether an entity exists.
Either it exists (and we have a PartialEntityData) or it does not.
-/
abbrev PartialEntities := Map EntityUID PartialEntityData

def PartialEntities.ancestors (es : PartialEntities) (uid : EntityUID) : Result (Set EntityUID) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  .ok d.ancestors

def PartialEntities.ancestorsOrEmpty (es : PartialEntities) (uid : EntityUID) : Set EntityUID :=
  match es.find? uid with
  | some d => d.ancestors
  | none   => Set.empty

def PartialEntities.attrs (es : PartialEntities) (uid : EntityUID) : Result (Map Attr RestrictedPartialValue) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  .ok d.attrs

def PartialEntities.attrsOrEmpty (es : PartialEntities) (uid : EntityUID) : Map Attr RestrictedPartialValue :=
  match es.find? uid with
  | some d => d.attrs
  | none   => Map.empty

deriving instance Inhabited for PartialEntityData

def Entities.asPartialEntities (es : Entities) : PartialEntities :=
  es.mapOnValues EntityData.asPartialEntityData

instance : Coe Entities PartialEntities where
  coe := Entities.asPartialEntities

end Cedar.Spec
