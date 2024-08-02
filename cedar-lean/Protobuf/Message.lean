import Protobuf.BParsec
import Protobuf.Structures
import Protobuf.Packed
namespace Proto

class Message (α : outParam Type) where
  wt_matches : Tag → Bool
  parse_field : α → Tag → BParsec α

export Message (wt_matches)
export Message (parse_field)

private partial def parse_message_helper {α: Type} [Message α] (remaining: Nat) (result: α) : BParsec α := do
  if remaining = 0 then
    pure result
  else

  let empty ← BParsec.empty
  if empty then
    return result

  let startPos ← BParsec.pos

  let tag ← BParsec.attempt Tag.parse
  let result ← parse_field result tag

  let endPos ← BParsec.pos
  let element_size := (endPos - startPos)

  (parse_message_helper (remaining - element_size) result)


def parse_message {α: Type} [Message α] [Inhabited α] : BParsec α := do
  let remaining ← BParsec.remaining
  parse_message_helper remaining default

def parse_message_of_size {α: Type} [Message α] [Inhabited α] (size: Nat) : BParsec α := do
  parse_message_helper size default

def interpret_message {α: Type} [Message α] [Inhabited α] (b: ByteArray) : Except String α :=
  BParsec.run parse_message b

end Proto
