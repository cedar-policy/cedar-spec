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
Monadic Parser Combinator for ByteArrays
-/
import Protobuf.ByteArray

namespace BParsec
inductive ParseResult (α : Type) where
  | success (pos : ByteArray.Iterator) (res : α)
  | error (pos : ByteArray.Iterator) (err : String)
  deriving Repr
end BParsec

def BParsec (α : Type) : Type := ByteArray.Iterator → BParsec.ParseResult α

namespace BParsec

instance (α : Type) : Inhabited (BParsec α) := ⟨λ it => ParseResult.error it ""⟩

@[inline]
def pure (a : α) : BParsec α := λ it => ParseResult.success it a

@[inline]
def bind {α β : Type} (f : BParsec α) (g : α → BParsec β) : BParsec β := λ it =>
  match f it with
  | ParseResult.success it a => g a it
  | ParseResult.error it msg => ParseResult.error it msg

instance : Monad BParsec := { pure := BParsec.pure, bind }

@[inline]
def fail (msg : String) : BParsec α := fun it => ParseResult.error it msg

@[inline]
def tryCatch (body: BParsec α) (handler: String → BParsec α): BParsec α := fun it =>
  match body it with
    | ParseResult.success it result => ParseResult.success it result
    | ParseResult.error it err => (handler err) it

@[inline]
def orElse (p : BParsec α) (q : Unit → BParsec α) : BParsec α := fun it =>
  match p it with
    | .success it result => ParseResult.success it result
    | .error it _ => q () it

/-- Attempt a parser combinator on a byte array, if it fails, reset
the position-/
@[inline]
def attempt (p : BParsec α) : BParsec α := λ it =>
  match p it with
  | ParseResult.success rem res => ParseResult.success rem res
  | ParseResult.error _ err => ParseResult.error it err

instance : Alternative BParsec := { failure := fail default, orElse }

instance : MonadExceptOf String BParsec := {
  throw := fail, tryCatch := tryCatch
}

/- Execute parser combinators on a byte array,
returns an Except to capture both successes and failures -/
@[inline]
def run (p : BParsec α) (ba : ByteArray) : Except String α :=
  match p ba.iter with
  | ParseResult.success _ res => Except.ok res
  | ParseResult.error it err  => Except.error s!"offset {repr it.pos}: {err}"

/- Execute parser combinators on a byte array, panics on error -/
@[inline]
def run! [Inhabited α] (p: BParsec α) (ba: ByteArray) : α :=
  match p ba.iter with
  | ParseResult.success _ res => res
  | ParseResult.error _ _  => panic!("Unexpected error")

-- Iterator wrapers

@[inline]
def hasNext : BParsec Bool :=
  fun it => ParseResult.success it it.hasNext

@[simp] theorem has_next_eq (it: ByteArray.Iterator) :
  (hasNext it) = ParseResult.success it it.hasNext := rfl

@[inline]
def next : BParsec Unit :=
  fun it => ParseResult.success (it.next) ()

@[simp] theorem next_eq (it: ByteArray.Iterator) : (next it) = ParseResult.success (it.next) () := rfl

@[inline]
def forward (n: Nat) : BParsec Unit :=
  fun it => ParseResult.success (it.forward n) ()

@[simp] theorem forward_eq (it: ByteArray.Iterator) (n: Nat) :
   (forward n) it = ParseResult.success (it.forward n) () := rfl

@[inline]
def size : BParsec Nat :=
  fun it => ParseResult.success it it.size

@[simp] theorem size_eq (it: ByteArray.Iterator) : size it = ParseResult.success it it.size := rfl

@[inline]
def remaining : BParsec Nat :=
  fun it => ParseResult.success it it.remaining


@[simp] theorem remaining_eq (it: ByteArray.Iterator):
  remaining it = ParseResult.success it it.remaining := rfl

@[inline]
def empty : BParsec Bool :=
  fun it => ParseResult.success it it.empty

@[simp] theorem empty_eq (it: ByteArray.Iterator) : empty it = ParseResult.success it it.empty := rfl

@[inline]
def pos : BParsec Nat :=
  fun it => ParseResult.success it it.pos

@[simp] theorem pos_eq (it: ByteArray.Iterator) : pos it = ParseResult.success it it.pos := rfl

@[specialize] def foldlHelper {α β : Type} (f: BParsec α) (g: β → α → β) (remaining: Nat) (result: β) : BParsec β := do
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
def foldl {α β : Type} (f: BParsec α) (g: β → α → β) (remaining: Nat) (init: β): BParsec β :=
  foldlHelper f g remaining init

@[inline]
def eof : BParsec Unit := fun it =>
  if it.pos ≥ it.data.size then
    ParseResult.success it ()
  else
    ParseResult.error it "Expected end of file"

end BParsec
