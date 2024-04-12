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

namespace Cedar.Spec

open Cedar.Data

/--
  an alternate metric for "size" of a value, used in termination arguments
-/
def Value.size : Value -> Nat
  | .prim _ => 1
  | .set vs => 1 + (vs.elts.map Value.size).foldl Nat.add 0
  | .record vs => 1 + (vs.values.map Value.size).foldl Nat.add 0
  | .ext _ => 1
decreasing_by all_goals sorry

theorem all_values_have_positive_size (v : Value) :
  v.size > 0
:= by
  unfold Value.size
  cases v <;> simp
  case set s =>
    generalize (s.elts.map Value.size).foldl Nat.add 0 = n
    omega
  case record m =>
    generalize (m.values.map Value.size).foldl Nat.add 0 = n
    omega

theorem List.foldl_add_pos {xs : List Nat} {init : Nat} :
  init > 0 → xs.foldl Nat.add init > 0
:= by
  intro h₁
  induction xs
  case nil => simp [h₁]
  case cons x tail h_ind =>
    simp [List.foldl_cons]
    apply @Nat.lt_of_lt_of_le 0 (tail.foldl Nat.add init) _ (by simp [h_ind])
    have h₂ : init <= init + x := by simp [Nat.le_add_right]
    -- should follow from h₂ and associativity
    sorry

theorem Value.set_termination (v : Value) (vs : Set Value) :
  v ∈ vs.elts → v.size < (Value.set vs).size
:= by
  intro h₁
  unfold Value.size List.map
  cases h₂ : vs.elts
  case nil => simp [h₂] at h₁
  case cons v' tail =>
    cases v <;> simp
    case prim p | ext x =>
      have h₃ := List.foldl_add_pos (all_values_have_positive_size v') (xs := tail.map size)
      apply @Nat.lt_of_lt_of_le 1 (1 + 1) _ (by simp)
      apply Nat.add_le_add_left
      generalize (tail.map size).foldl Nat.add v'.size = n at *
      cases n
      case zero => simp at h₃
      case succ n' => omega
    case set s =>
      sorry
    case record m =>
      sorry

theorem Value.record_termination (v : Value) (m : Map Attr Value) :
  v ∈ m.values → v.size < (Value.record m).size
:= by
  intro h₁
  unfold Value.size List.map
  cases h₂ : m.values
  case nil => simp [h₂] at h₁
  case cons v' tail =>
    cases v <;> simp
    case prim p | ext x =>
      -- our goal clearly follows from `all_values_have_positive_size`
      -- and the fact that `Nat.add` is non-decreasing. But not sure
      -- how to convince Lean
      sorry
    case set s =>
      sorry
    case record m =>
      sorry
