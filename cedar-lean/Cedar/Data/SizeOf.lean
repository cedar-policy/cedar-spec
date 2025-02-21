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

import Cedar.Data.Map
import Cedar.Data.Set

/-!
  Lemmas involving `sizeOf`, which are located here rather than in `Cedar/Thm`
  because they are needed for some definitions in `Cedar/Spec` and/or
  `Cedar/Partial`, and our convention prevents files in `Cedar/Spec` or
  `Cedar/Partial` from depending on lemmas in `Cedar/Thm`.
-/

namespace Cedar.Data.Map

/-! ## Map -/

theorem sizeOf_lt_of_value [SizeOf α] [SizeOf β] {m : Map α β} {k : α} {v : β}
  (h : (k, v) ∈ m.1) :
  sizeOf v < sizeOf m
:= by
  simp only [Membership.mem] at h
  replace h := List.sizeOf_lt_of_mem h
  have v_lt_kv : sizeOf v < sizeOf (k, v) := by
    simp only [sizeOf, Prod._sizeOf_1]
    omega
  have m1_lt_m : sizeOf m.1 < sizeOf m := by
    simp only [sizeOf, Map._sizeOf_1]
    omega
  omega

theorem sizeOf_lt_of_kvs [SizeOf α] [SizeOf β] (m : Map α β) :
  sizeOf m.kvs < sizeOf m
:= by
  unfold kvs
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1 ; simp only
  generalize sizeOf m.1 = s
  omega

theorem sizeOf_lt_of_tl [SizeOf α] [SizeOf β] {m : Map α β} {tl : List (α × β)}
  (h : m.kvs = (k, v) :: tl) :
  1 + sizeOf tl < sizeOf m
:= by
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1
  simp only
  unfold kvs at h
  simp only [h, List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]
  omega

end Cedar.Data.Map

namespace Cedar.Data.Set

/-! ## Set -/

theorem sizeOf_lt_of_mem [SizeOf α] {s : Set α}
  (h : a ∈ s) :
  sizeOf a < sizeOf s
:= by
  simp only [Membership.mem, elts] at h
  replace h := List.sizeOf_lt_of_mem h
  have _ : sizeOf s.1 < sizeOf s := by
    simp only [sizeOf, _sizeOf_1]
    omega
  omega

theorem sizeOf_lt_of_elts [SizeOf α] {s : Set α} :
  sizeOf s.elts < sizeOf s
:= by
  simp only [elts]
  conv => rhs ; unfold sizeOf _sizeOf_inst _sizeOf_1 ; simp
  omega

end Cedar.Data.Set
