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

module

import Cedar.Spec.Value
public import Cedar.Spec.Entities
public import Cedar.Spec.Request
import Cedar.Data.SizeOf

/-!
This file defines entity slicing at a level
-/

namespace Cedar.Spec

open Cedar.Data

public def Value.sliceEUIDs : Value → Set EntityUID
  | .prim (.entityUID uid) => Set.singleton uid
  | .record (Map.mk avs) => avs.mapUnion₃ λ e => e.val.snd.sliceEUIDs
  | .prim _ | set _ | .ext _ => ∅

public def EntityData.sliceEUIDs (ed : EntityData) : Set EntityUID :=
  ed.attrs.values.mapUnion Value.sliceEUIDs ∪
  ed.tags.values.mapUnion Value.sliceEUIDs

public def Request.sliceEUIDs (r : Request) : Set EntityUID :=
  Set.make [r.principal, r.action, r.resource] ∪
  (Value.record r.context).sliceEUIDs

@[expose]
public def Entities.sliceAtLevel (es : Entities) (r : Request) (level : Nat) : Entities :=
  let slice := sliceAtLevel r.sliceEUIDs level
  let slice := slice.elts.filterMap λ e => do some (e, ←(es.find? e))
  Map.make slice
where
  sliceAtLevel (work : Set EntityUID) : Nat → Set EntityUID
    | 0 => ∅
    | level + 1 =>
      let eds := work.elts.filterMap es.find?
      let slice := eds.mapUnion λ ed => sliceAtLevel ed.sliceEUIDs level
      work ∪ slice
