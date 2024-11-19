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
inductive ParseResult (α : Type) where
  | success (pos : ByteArray.ByteIterator) (res : α)
  | error (pos : ByteArray.ByteIterator) (err : String)
  deriving Repr
end BParsec

def BParsec (α : Type) : Type := ByteArray.ByteIterator → BParsec.ParseResult α

namespace BParsec

instance (α : Type) : Inhabited (BParsec α) := ⟨λ it => .error it ""⟩

@[inline]
def map {α β : Type}  (g : α → β) (f : BParsec α) : BParsec β := λ it =>
  match f it with
  | .success it a => .success it (g a)
  | .error it msg => .error it msg

@[inline]
def mapConst {α β : Type} (x : α) (f : BParsec β) : BParsec α := λ it =>
  match f it with
  | .success it _ => .success it x
  | .error it msg => .error it msg

instance : Functor BParsec := { map, mapConst }

@[inline]
def pure (a : α) : BParsec α := λ it => .success it a

@[inline]
def bind {α β : Type} (f : BParsec α) (g : α → BParsec β) : BParsec β := λ it =>
  match f it with
  | .success it a => g a it
  | .error it msg => .error it msg

instance : Monad BParsec := { pure := BParsec.pure, bind }

@[inline]
def fail (msg : String) : BParsec α := fun it => .error it msg

@[inline]
def tryCatch (body : BParsec α) (handler : String → BParsec α) : BParsec α := fun it =>
  match body it with
    | .success it result => .success it result
    | .error it err => (handler err) it

@[inline]
def orElse (p : BParsec α) (q : Unit → BParsec α) : BParsec α := fun it =>
  match p it with
    | .success it result => .success it result
    | .error it _ => q () it

/-- Attempt a parser combinator on a byte array, if it fails, reset
the position-/
@[inline]
def attempt (p : BParsec α) : BParsec α := λ it =>
  match p it with
  | .success rem res => .success rem res
  | .error _ err => .error it err

instance : Alternative BParsec := { failure := fail default, orElse }

instance : MonadExceptOf String BParsec := {
  throw := fail, tryCatch := tryCatch
}

/- Execute parser combinators on a byte array,
returns an Except to capture both successes and failures -/
@[inline]
def run (p : BParsec α) (ba : ByteArray) : Except String α :=
  match p ba.byte_iter with
  | .success _ res => .ok res
  | .error it err  => .error s!"offset {it.pos}: {err}"

/- Execute parser combinators on a byte array, panics on error -/
@[inline]
def run! [Inhabited α] (p : BParsec α) (ba : ByteArray) : α :=
  match p ba.byte_iter with
  | .success _ res => res
  | .error _ _  => panic!("Unexpected error")

-- Iterator wrappers

@[inline]
def hasNext : BParsec Bool :=
  fun it => .success it it.hasNext

@[inline]
def next : BParsec Unit :=
  fun it => .success (it.next) ()

@[inline]
def forward (n : Nat) : BParsec Unit :=
  fun it => .success (it.forward n) ()

@[inline]
def size : BParsec Nat :=
  fun it => .success it it.size

@[inline]
def remaining : BParsec Nat :=
  fun it => .success it it.remaining

@[inline]
def empty : BParsec Bool :=
  fun it => .success it it.empty

@[inline]
def pos : BParsec Nat :=
  fun it => .success it it.pos

@[specialize] def foldlHelper {α β : Type} (f : BParsec α) (g : β → α → β) (remaining : Nat) (result : β) : BParsec β := do
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
def foldl {α β : Type} (f : BParsec α) (g : β → α → β) (remaining : Nat) (init : β) : BParsec β :=
  foldlHelper f g remaining init

@[inline]
def eof : BParsec Unit := fun it =>
  if it.pos ≥ it.data.size then
    .success it ()
  else
    .error it "Expected end of file"

end BParsec
