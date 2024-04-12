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
import Cedar.Partial.Value

/-!
This file defines Cedar partial-entities structures.
-/

namespace Cedar.Partial

open Cedar.Data

/--
Represents the information about one entity.

Currently, this allows attrs to be known-to-exist-but-unknown-value,
but does not allow attrs to be unknown-whether-they-exist-entirely.
(the result of `e has attr` is never a residual for an `e` that is known to exist.)

Currently, this does not allow any unknowns about ancestor information.
All ancestor information must be fully concrete.
-/
structure EntityData where
  attrs : Map Spec.Attr Partial.RestrictedValue
  ancestors : Set Spec.EntityUID

/--
Represents the information about all entities.

Currently, this does not allow it to be unknown whether an entity exists.
Either it exists (and we have a Partial.EntityData) or it does not.
-/
abbrev Entities := Map Spec.EntityUID Partial.EntityData

def Entities.ancestors (es : Partial.Entities) (uid : Spec.EntityUID) : Spec.Result (Set Spec.EntityUID) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  .ok d.ancestors

def Entities.ancestorsOrEmpty (es : Partial.Entities) (uid : Spec.EntityUID) : Set Spec.EntityUID :=
  match es.find? uid with
  | some d => d.ancestors
  | none   => Set.empty

def Entities.attrs (es : Partial.Entities) (uid : Spec.EntityUID) : Spec.Result (Map Spec.Attr Partial.RestrictedValue) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  .ok d.attrs

def Entities.attrsOrEmpty (es : Partial.Entities) (uid : Spec.EntityUID) : Map Spec.Attr Partial.RestrictedValue :=
  match es.find? uid with
  | some d => d.attrs
  | none   => Map.empty

deriving instance Inhabited for EntityData

end Cedar.Partial

namespace Cedar.Spec

def EntityData.asPartialEntityData (d : Spec.EntityData) : Partial.EntityData :=
  {
    attrs := d.attrs.mapOnValues Partial.RestrictedValue.value,
    ancestors := d.ancestors,
  }

def Entities.asPartialEntities (es : Spec.Entities) : Partial.Entities :=
  es.mapOnValues Spec.EntityData.asPartialEntityData

instance : Coe Spec.Entities Partial.Entities where
  coe := Spec.Entities.asPartialEntities

end Cedar.Spec
