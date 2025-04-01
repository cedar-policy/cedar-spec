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

import Cedar.Spec
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.Data.MapUnion
import Cedar.Thm.Validation.Levels.CheckLevel

import Cedar.Thm.Validation.Slice.Reachable.Basic

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem var_entity_reachable {var : Var} {v : Value} {n : Nat} {request : Request} {entities : Entities} {euid : EntityUID} {path : List Attr}
  (he : evaluate (.var var) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid)
  (hf : entities.contains euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have hi : euid ∈ request.sliceEUIDs := by
    rw [Request.sliceEUIDs, Set.mem_union_iff_mem_or, ←Set.make_mem]
    cases var <;> simp only [evaluate, Except.ok.injEq] at he <;> subst he <;> cases ha
    case principal | action | resource => simp [hf]
    case context v a path hf' hv =>
      suffices h : ∃ kv ∈ request.context.kvs, euid ∈ kv.snd.sliceEUIDs by
        unfold Value.sliceEUIDs List.attach₃
        right
        simpa [List.mapUnion_pmap_subtype  (·.snd.sliceEUIDs) request.context.kvs, Set.mem_mapUnion_iff_mem_exists] using h
      exists (a, v)
      constructor
      · exact Map.find?_mem_toList hf'
      · exact in_val_then_val_slice hv
  exact ReachableIn.in_start hi
