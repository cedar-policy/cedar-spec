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

/-!
Iterators for ByteArrays
-/

namespace ByteArray

deriving instance Repr, DecidableEq, Inhabited for ByteArray

structure ByteIterator where
  data : ByteArray
  /-- The current position.--/
  pos : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Creates an iterator at the beginning of a ByteArray. -/
@[inline]
def byte_iter (b : ByteArray) : ByteIterator := ⟨b, 0⟩

@[inline]
def ByteIterator.next (i : ByteIterator) : ByteIterator := ⟨i.data, i.pos + 1⟩

@[inline]
def ByteIterator.forward (i : ByteIterator) (n : Nat) : ByteIterator := ⟨i.data, i.pos + n⟩

@[inline]
def ByteIterator.size (i : ByteIterator) : Nat := i.data.size

@[inline]
def ByteIterator.remaining (i : ByteIterator) : Nat := i.size - i.pos

/-- True if there are more bytes passed the current position. -/
@[inline]
def ByteIterator.hasNext (i : ByteIterator) : Bool := i.remaining != 0

@[inline]
def ByteIterator.empty (i : ByteIterator) : Bool := ¬i.hasNext

end ByteArray
