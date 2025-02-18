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
import Cedar.Spec.Entities
import Cedar.Spec.Request
import Cedar.Data.SizeOf

/-!
This file defines entity slicing at a level
-/

namespace Cedar.Spec

open Cedar.Data

def List.unionAll {α} [LT α] [DecidableLT α] : List (Set α) → Set α :=
  List.foldl (· ∪ ·) ∅

def Value.sliceEUIDs : Value → Set EntityUID
  | .prim (.entityUID uid) => Set.singleton uid
  | .record (Map.mk avs) => List.unionAll $ avs.attach₃.map λ e => e.val.snd.sliceEUIDs
  | .prim _ | set _ | .ext _ => ∅

def EntityData.sliceEUIDs (ed : EntityData) : Set EntityUID :=
  (List.unionAll $ ed.attrs.values.map Value.sliceEUIDs) ∪
  (List.unionAll $ ed.tags.values.map Value.sliceEUIDs)

def Request.sliceEUIDs (r : Request) : Set EntityUID :=
  Set.make [r.principal, r.action, r.resource] ∪
  (Value.record r.context).sliceEUIDs

def Entities.sliceAtLevel (es : Entities) (r : Request) (level : Nat) : Option Entities := do
  let slice ← sliceAtLevel r.sliceEUIDs level
  let slice ← slice.elts.mapM λ e => do some (e, ←(es.find? e))
  some (Map.make slice)
where
  sliceAtLevel (work : Set EntityUID) : Nat → Option (Set EntityUID)
    | 0 => some ∅
    | level + 1 => do
      let eds ← work.elts.mapM es.find?
      let slice ← List.unionAll <$> eds.mapM (λ ed => sliceAtLevel ed.sliceEUIDs level)
      some (work ∪ slice)
