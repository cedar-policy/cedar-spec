import Protobuf.BParsec
import Protobuf.Structures
import Protobuf.Packed
import Protobuf.Types
namespace Proto

@[reducible]
def MessageM (α: Type) : Type := StateM α Unit


class Message (α : Type) where
  parseField : Tag → BParsec (MessageM α)
  merge: α → α → α

export Message (parseField)

namespace MessageM

@[inline]
def run {σ : Type u} {α : Type u} (x : StateM σ α) (s : σ) : σ :=
  (StateT.run x s).snd

private def modifyMessageHelper (f: α → α) : StateM α Unit := do
  modifyGet fun s => ((), f s)

def modifyGet (f: α → α) : MessageM α := modifyMessageHelper f

@[inline]
def pure  : MessageM α := StateT.pure ()

end MessageM


namespace Message

private partial def parseMessageHelper {α: Type} [Message α] (remaining: Nat) (result: MessageM α) : BParsec (MessageM α) := do
  if remaining = 0 then
    pure result
  else

  let empty ← BParsec.empty
  if empty then
    throw "Expected more bytes"

  let startPos ← BParsec.pos

  let tag ← BParsec.attempt Tag.parse

  let result: MessageM α ← BParsec.attempt (parseField tag)

  let endPos ← BParsec.pos
  let elementSize := (endPos - startPos)

  (parseMessageHelper (remaining - elementSize) result)


def parse {α: Type} [Message α] [Inhabited α] : BParsec α := do
  let remaining ← BParsec.remaining
  let message_m: StateM α Unit ← parseMessageHelper remaining MessageM.pure
  pure (MessageM.run message_m default)

def parseWithLen {α: Type} [Message α] [Inhabited α] : BParsec α := do
  let len ← Len.parse
  let message_m: StateM α Unit ← parseMessageHelper len.size MessageM.pure
  pure (MessageM.run message_m default)

def parseWithSize {α: Type} [Message α] [Inhabited α] (size: Nat) : BParsec α := do
  let message_m: StateM α Unit ← parseMessageHelper size MessageM.pure
  pure (MessageM.run message_m default)

def interpret? {α: Type} [Message α] [Inhabited α] (b: ByteArray) : Except String α :=
  BParsec.run parse b

def interpret! {α: Type} [Message α] [Inhabited α] (b: ByteArray) : α :=
  BParsec.run! parse b

instance [Message α] [Inhabited α] : Field α := {
  parse := parseWithLen
  checkWireType := fun (w: WireType) => WireType.LEN = w
  merge := merge
}

end Message

end Proto
