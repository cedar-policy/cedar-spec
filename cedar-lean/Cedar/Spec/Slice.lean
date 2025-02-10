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

def flatten_union {α} [LT α] [DecidableLT α] : List (Set α) → Set α :=
  List.foldl (· ∪ ·) ∅

def Value.sliceEUIDs (v : Value) : Set EntityUID :=
  match v with
  | .prim (.entityUID uid) => Set.singleton uid
  -- TODO: You can't access these except by `in`, so maybe this could just be `Set.empty`
  | .set s => flatten_union $ s.elts.attach.map λ e => e.val.sliceEUIDs
  | .record r => flatten_union $ r.toList.attach.map λ e => e.val.snd.sliceEUIDs
  | .prim _ | .ext _ => ∅
  decreasing_by
    · simp [←Nat.succ_eq_one_add, Nat.lt.step, Set.sizeOf_lt_of_mem e.property]
    · simp only [Map.toList] at e
      have _ := Map.sizeOf_lt_of_kvs r
      have _ := List.sizeOf_lt_of_mem e.property
      have _ : sizeOf e.val.snd < sizeOf e.val := by simp [sizeOf, Prod._sizeOf_1, Nat.one_add]
      rw [record.sizeOf_spec] ; omega

def EntityData.sliceEUIDs (ed : EntityData) : Set EntityUID :=
  (flatten_union $ ed.attrs.values.map Value.sliceEUIDs) ∪
  (flatten_union $ ed.tags.values.map Value.sliceEUIDs)

def Request.sliceEUIDs (r : Request) : Set EntityUID :=
  Set.make [r.principal, r.action, r.resource] ∪
  (Value.record r.context).sliceEUIDs

def Entities.sliceAtLevel (es : Entities) (r : Request) (level : Nat) : Option Entities := do
  let slice ← sliceAtLevel r.sliceEUIDs level
  let slice ← slice.elts.mapM λ e => do some (e, ←(es.find? e))
  some (Map.make slice)
where
  sliceAtLevel (work : Set EntityUID) (level : Nat) : Option (Set EntityUID) :=
    match level with
    | 0 => some ∅
    | Nat.succ level => do
      let eds ← work.elts.mapM es.find?
      let slice ← flatten_union <$> eds.mapM (λ ed => sliceAtLevel ed.sliceEUIDs level)
      some (work ∪ slice)
