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

import Cedar.Spec.Value

/-!
This file defines Cedar entities.
-/

namespace Cedar.Spec

open Cedar.Data

----- Definitions -----

structure EntityData where
  attrs : Map Attr Value
  ancestors : Set EntityUID

abbrev Entities := Map EntityUID EntityData

def Entities.ancestors (es : Entities) (uid : EntityUID) : Result (Set EntityUID) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  .ok d.ancestors

def Entities.ancestorsOrEmpty (es : Entities) (uid : EntityUID) : Set EntityUID :=
  match es.find? uid with
  | some d => d.ancestors
  | none   => Set.empty

def Entities.attrs (es : Entities) (uid : EntityUID) : Result (Map Attr Value) := do
  let d ← es.findOrErr uid .entityDoesNotExist
  .ok d.attrs

def Entities.attrsOrEmpty (es : Entities) (uid : EntityUID) : Map Attr Value :=
  match es.find? uid with
  | some d => d.attrs
  | none   => Map.empty

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for EntityData

end Cedar.Spec
