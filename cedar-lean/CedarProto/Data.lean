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

/-!
Unverified variants of `Cedar.Data.Set.make` and `Cedar.Data.Map.make` for
arrays, for use when decoding protobuf messages. `make` canonicalizes with an
insertion sort, which takes a quadratic number of comparisons on unsorted
input; these sort the array with a library sort instead. They are not proven
equivalent to `make`.
-/

namespace Cedar.Data

/-- Variant of `Set.make` for an array. -/
def setOfArray {α} [LT α] [DecidableLT α] [BEq α] (elts : Array α) : Set α :=
  Set.mk (elts.qsort (· < ·)).eraseReps.toList

/--
Variant of `Map.make` for an array. Like `Map.make`, the first occurrence of a
duplicated key is kept, because the sort is stable.
-/
def mapOfArray {α β} [LT α] [DecidableLT α] [BEq α] (kvs : Array (α × β)) : Map α β :=
  Map.mk ((kvs.mergeSort (λ a b => !(b.1 < a.1))).toList.eraseRepsBy (·.1 == ·.1))

end Cedar.Data
