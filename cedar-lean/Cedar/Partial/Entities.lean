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

import Cedar.Spec.Entities
import Cedar.Partial.Value

/-!
This file defines Cedar partial-entities structures.
-/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Attr EntityUID Result)

/--
Represents the information about one entity.

Currently, this allows attrs to be known-to-exist-but-unknown-value,
but does not allow attrs to be unknown-whether-they-exist-entirely.
(the result of `e has attr` is never a residual for an `e` that is known to exist.)

Currently, this does not allow any unknowns about ancestor information.
All ancestor information must be fully concrete.
-/
structure EntityData where
  attrs : Map Attr Partial.Value
  ancestors : Set EntityUID

/--
Represents the information about all entities.

Currently, this does not allow it to be unknown whether an entity exists.
Either it exists (and we have a `Partial.EntityData`) or it does not.
-/
structure Entities where
  es : Map EntityUID Partial.EntityData

def Entities.ancestors (es : Partial.Entities) (uid : EntityUID) : Result (Set EntityUID) := do
  let d ← es.es.findOrErr uid .entityDoesNotExist
  .ok d.ancestors

def Entities.ancestorsOrEmpty (es : Partial.Entities) (uid : EntityUID) : Set EntityUID :=
  match es.es.find? uid with
  | some d => d.ancestors
  | none   => Set.empty

def Entities.attrs (es : Partial.Entities) (uid : EntityUID) : Result (Map Attr Partial.Value) := do
  let d ← es.es.findOrErr uid .entityDoesNotExist
  .ok d.attrs

def Entities.attrsOrEmpty (es : Partial.Entities) (uid : EntityUID) : Map Attr Partial.Value :=
  match es.es.find? uid with
  | some d => d.attrs
  | none   => Map.empty

deriving instance Inhabited for EntityData

end Cedar.Partial

namespace Cedar.Spec

def EntityData.asPartialEntityData : Spec.EntityData → Partial.EntityData
  | { attrs, ancestors } => {
      attrs := attrs.mapOnValues Partial.Value.value,
      ancestors,
  }

instance : Coe Spec.EntityData Partial.EntityData where
  coe := Spec.EntityData.asPartialEntityData

def Entities.asPartialEntities (es : Spec.Entities) : Partial.Entities :=
  { es := es.mapOnValues Spec.EntityData.asPartialEntityData }

instance : Coe Spec.Entities Partial.Entities where
  coe := Spec.Entities.asPartialEntities

end Cedar.Spec

namespace Cedar.Partial

open Cedar.Data

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new `Partial.EntityData`.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.EntityData` will still contain some unknowns.
-/
def EntityData.subst (subsmap : Map Unknown Partial.Value) : Partial.EntityData → Partial.EntityData
  | { attrs, ancestors } => {
      attrs := attrs.mapOnValues (Partial.Value.subst subsmap),
      ancestors,
    }

/--
  Given a map of unknown-name to value, substitute all unknowns with the
  corresponding values, producing a new `Partial.Entities`.
  It's fine for some unknowns to not be in `subsmap`, in which case the returned
  `Partial.Entities` will still contain some unknowns.
-/
def Entities.subst (subsmap : Map Unknown Partial.Value) : Partial.Entities → Partial.Entities
  | { es } => {
      es := es.mapOnValues (Partial.EntityData.subst subsmap)
  }

end Cedar.Partial
