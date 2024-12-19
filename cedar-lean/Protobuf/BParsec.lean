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

import Protobuf.ByteArray

/-!
Monadic Parser Combinator for ByteArrays
-/

namespace BParsec
structure ParseResult (α : Type) where
  pos : ByteArray.ByteIterator
  res : Except String α
  deriving Repr
end BParsec

def BParsec (α : Type) : Type := ByteArray.ByteIterator → BParsec.ParseResult α

namespace BParsec

@[inline]
def pure (a : α) : BParsec α := λ pos => { pos, res := .ok a }

@[inline]
def fail (msg : String) : BParsec α := λ pos => { pos, res := .error msg }

instance (α : Type) : Inhabited (BParsec α) := ⟨fail ""⟩

@[inline]
def map (g : α → β) (f : BParsec α) : BParsec β := λ pos₀ =>
  match f pos₀ with
  | { pos, res := .ok a } => { pos, res := .ok (g a) }
  | { pos, res := .error msg } => { pos, res := .error msg }

@[inline]
def mapConst (x : α) (f : BParsec β) : BParsec α := λ pos₀ =>
  match f pos₀ with
  | { pos, res := .ok _ } => { pos, res := .ok x }
  | { pos, res := .error msg } => { pos, res := .error msg }

instance : Functor BParsec := { map, mapConst }

@[inline]
def bind (f : BParsec α) (g : α → BParsec β) : BParsec β := λ pos₀ =>
  match f pos₀ with
  | { pos, res := .ok a } => g a pos
  | { pos, res := .error msg } => { pos, res := .error msg }

instance : Monad BParsec := { pure, bind }

@[inline]
def tryCatch (body : BParsec α) (handler : String → BParsec α) : BParsec α := λ pos₀ =>
  match body pos₀ with
  | { pos, res := .ok result } => { pos, res := .ok result }
  | { pos, res := .error msg } => (handler msg) pos

@[inline]
def orElse (p : BParsec α) (q : Unit → BParsec α) : BParsec α := λ pos₀ =>
  match p pos₀ with
  | { pos, res := .ok result } => { pos, res := .ok result }
  | { pos, res := .error _ } => q () pos

/-- Attempt a parser combinator on a byte array, if it fails, reset
the position-/
@[inline]
def attempt (p : BParsec α) : BParsec α := λ pos₀ =>
  match p pos₀ with
  | { pos, res := .ok res } => { pos, res := .ok res }
  | { pos := _, res := .error msg } => { pos := pos₀, res := .error msg }

instance : Alternative BParsec := { failure := fail default, orElse }

instance : MonadExceptOf String BParsec := {
  throw := fail, tryCatch := tryCatch
}

/- Execute parser combinators on a byte array,
returns an Except to capture both successes and failures -/
@[inline]
def run (p : BParsec α) (ba : ByteArray) : Except String α :=
  match p ba.byte_iter with
  | { pos := _, res := .ok res } => .ok res
  | { pos, res := .error msg } => .error s!"offset {pos.pos}: {msg}"

/- Execute parser combinators on a byte array, panics on error -/
@[inline]
def run! [Inhabited α] (p : BParsec α) (ba : ByteArray) : α :=
  match run p ba with
  | .ok res => res
  | .error msg => panic!(s!"Unexpected error: {msg}")

-- Iterator wrappers

/-- Advance the iterator one byte, discarding it -/
@[inline]
def next : BParsec Unit := λ pos =>
  { pos := pos.next, res := .ok () }

/-- Advance the iterator `n` bytes, discarding them -/
@[inline]
def forward (n : Nat) : BParsec Unit := λ pos =>
  { pos := pos.forward n, res := .ok () }

/-- Advance the iterator one byte, returning it, or `None` if the iterator was empty -/
@[inline]
def nextByte : BParsec (Option UInt8) := λ pos =>
  { pos := pos.next, res := .ok pos.data[pos.pos]? }

/-- Return some computation on the current iterator state, without changing the state -/
@[inline]
def inspect (f : ByteArray.ByteIterator → α) : BParsec α := λ pos =>
  { pos, res := .ok (f pos) }

@[inline]
def hasNext : BParsec Bool := inspect ByteArray.ByteIterator.hasNext

@[inline]
def size : BParsec Nat := inspect ByteArray.ByteIterator.size

@[inline]
def remaining : BParsec Nat := inspect ByteArray.ByteIterator.remaining

@[inline]
def empty : BParsec Bool := inspect ByteArray.ByteIterator.empty

/-- Get the current iterator position, as a `Nat` -/
@[inline]
def pos : BParsec Nat := inspect ByteArray.ByteIterator.pos

@[specialize] def foldlHelper (f : BParsec α) (g : β → α → β) (remaining : Nat) (result : β) : BParsec β := do
  if remaining = 0 then
    pure result
  else

  let startPos ← pos
  let element ← f
  let endPos ← pos

  let elementSize := endPos - startPos
  if elementSize = 0 then
    throw "f did not progress ByteArray"
  else

  let newResult := g result element
  foldlHelper f g (remaining - elementSize) newResult

@[inline]
def foldl (f : BParsec α) (g : β → α → β) (remaining : Nat) (init : β) : BParsec β :=
  foldlHelper f g remaining init

@[inline]
def eof : BParsec Unit := do
  let pos ← pos
  let size ← size
  if pos ≥ size then
    pure ()
  else
    throw "Expected end of file"

end BParsec
