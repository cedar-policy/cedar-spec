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

public import Cedar.Spec
public import Cedar.Data
public import Cedar.Validation
public import Cedar.Thm.Validation.Typechecker
public import Cedar.Thm.Validation.Typechecker.Types
public import Cedar.Thm.Data.MapUnion
public import Cedar.Thm.Validation.Levels.CheckLevel

public import Cedar.Thm.Validation.Slice.Reachable.Basic

@[expose] public section

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem var_entity_reachable {var : Var} {v : Value} {n : Nat} {request : Request} {entities : Entities} {euid : EntityUID} {path : List Attr}
  (he : evaluate (.var var) request entities = .ok v)
  (ha : Value.EuidViaPath v path euid) :
  ReachableIn entities request.sliceEUIDs euid (n + 1)
:= by
  have hi : euid ∈ request.sliceEUIDs := by
    rw [mem_sliceEUIDs_request, Set.mem_make]
    cases var <;> simp only [evaluate, Except.ok.injEq] at he <;> subst he <;> cases ha
    case principal | action | resource => simp
    case context v a path hf' hv =>
      right
      rw [mem_sliceEUIDs_record]
      exists (a, v)
      constructor
      · exact Map.find?_mem_toList hf'
      · exact in_val_then_val_slice hv
  exact ReachableIn.in_start hi
