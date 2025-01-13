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
This file defines Cedar entities.
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
  Map.make $ ← sliceAtLevel es r.sliceEUIDs r level
where
  sliceAtLevel (es : Entities) (work : Set EntityUID) (r : Request) (level : Nat) : Option (List (EntityUID × EntityData)) :=
    if level == 0 then
      .some []
    else do
      let eds ← work.elts.mapM λ uid => do .some (uid, ←(es.find? uid))
      let work := flatten_union $ eds.map λ (_, ed) => ed.sliceEUIDs
      eds ++ (← sliceAtLevel es work r (level - 1))
    termination_by level
    decreasing_by
      rename_i h₁
      simp only [beq_iff_eq] at h₁
      omega
