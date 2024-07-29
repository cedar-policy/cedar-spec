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
/-
Iterators for ByteArrays
-/
namespace ByteArray

deriving instance Repr, DecidableEq, Inhabited for ByteArray

structure Iterator where
  data : ByteArray
  /-- The current position.--/
  pos : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Creates an iterator at the beginning of a ByteArray. -/
def iter (b : ByteArray) : Iterator := ⟨b, 0⟩

namespace Iterator

def next (i: Iterator) : Iterator := ⟨i.data, i.pos + 1⟩

@[simp] theorem next_pos_eq (i: Iterator) : i.next.pos = i.pos + 1 := rfl
@[simp] theorem next_data_eq (i: Iterator) : i.next.data = i.data := rfl

def forward : Iterator → Nat → Iterator
  | it, 0   => it
  | it, n+1 => forward it.next n

def size (i: Iterator) : Nat := i.data.size

@[simp] theorem next_size_eq (i: Iterator) : i.next.size = i.size := rfl

def remaining (i: Iterator) : Nat := i.size - i.pos

@[simp] theorem remaining_eq (i: Iterator) : i.remaining = i.size - i.pos := rfl

theorem next_le_remaining (i: Iterator) : i.next.remaining ≤ i.remaining := by
  simp only [remaining_eq, next_size_eq, next_pos_eq]
  omega

/-- True if there are more bytes passed the current position. -/
def hasNext (i: Iterator) : Bool := i.remaining > 0
@[simp] theorem hasNext_iff (i: Iterator) : i.hasNext ↔ i.remaining > 0 := by
  apply Iff.intro
  all_goals unfold hasNext
  all_goals simp only [remaining_eq, gt_iff_lt, decide_eq_true_eq, imp_self]

@[simp] theorem not_hasNext_iff (i: Iterator) : ¬i.hasNext ↔ i.remaining = 0 := by
  apply Iff.intro
  all_goals unfold hasNext
  all_goals simp only [remaining_eq, gt_iff_lt, decide_eq_true_eq,
    Nat.not_lt, Nat.le_zero_eq, imp_self]


def empty (i: Iterator) : Bool := ¬i.hasNext

@[simp] theorem empty_iff (i: Iterator) : i.empty ↔ ¬i.hasNext := by
  apply Iff.intro
  all_goals unfold empty
  all_goals simp only [hasNext_iff, remaining_eq, gt_iff_lt, Nat.not_lt,
   Nat.le_zero_eq, decide_eq_true_eq, imp_self]

@[simp] theorem not_empty_iff (i: Iterator) : ¬i.empty ↔ i.hasNext := by
  simp only [empty_iff, hasNext_iff, remaining_eq, gt_iff_lt, Nat.not_lt, Nat.le_zero_eq]
  exact Nat.ne_zero_iff_zero_lt

/-- The byte at the current position.
On an invalid position, returns `(default : UInt8)`. -/
def curr : Iterator → UInt8 :=
  fun i => if h : hasNext i then
    have h2 : i.pos < i.size := by
     simp only [hasNext_iff, remaining_eq, gt_iff_lt] at h
     exact Nat.lt_of_sub_pos h
    i.data.data[i.pos]
  else
    default

end Iterator
end ByteArray
