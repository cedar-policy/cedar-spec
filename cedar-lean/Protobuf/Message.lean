import Protobuf.BParsec
import Protobuf.Structures
import Protobuf.Packed
import Protobuf.Types
namespace Proto

class Message (α : Type) [Inhabited α] where
  parseField : Tag → BParsec (StateM α Unit)
  merge: α → α → α

export Message (parseField)
namespace Message

private partial def parseMessageHelper {α: Type} [Inhabited α] [Message α] (remaining: Nat) (result: StateM α Unit) : BParsec (StateM α Unit) := do
  if remaining = 0 then
    pure result
  else

  let empty ← BParsec.empty
  if empty then
    throw "Expected more bytes"
  else

  let startPos ← BParsec.pos

  let tag ← BParsec.attempt Tag.parse

  let result2: StateM α Unit ← BParsec.attempt (parseField tag)

  let endPos ← BParsec.pos
  let elementSize := (endPos - startPos)

  (parseMessageHelper (remaining - elementSize) (result >>= fun () => result2))

@[inline]
def parse {α: Type} [Inhabited α] [Message α] : BParsec α := do
  let remaining ← BParsec.remaining
  let initial: StateM α Unit := pure ()
  let message_m: StateM α Unit ← parseMessageHelper remaining initial
  BParsec.eof
  pure (StateT.run message_m default).snd

@[inline]
def parseWithLen {α: Type} [Inhabited α] [Message α] : BParsec α := do
  let len ← Len.parse
  let message_m: StateM α Unit ← parseMessageHelper len.size (pure ())
  pure (StateT.run message_m default).snd

@[inline]
def parseWithSize {α: Type} [Inhabited α] [Message α] (size: Nat) : BParsec α := do
  let message_m: StateM α Unit ← parseMessageHelper size (pure ())
  pure (StateT.run message_m default).snd

@[inline]
def interpret? {α: Type} [Inhabited α] [Message α] (b: ByteArray) : Except String α :=
  BParsec.run parse b

@[inline]
def interpret! {α: Type} [Inhabited α] [Message α] (b: ByteArray) : α :=
  BParsec.run! parse b

instance {α: Type} [Inhabited α] [Message α] : Field α := {
  parse := parseWithLen
  checkWireType := fun (w: WireType) => WireType.LEN = w
  merge := merge
}

end Message

end Proto
