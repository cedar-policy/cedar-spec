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

import Protobuf.Field
import Protobuf.Message
import Protobuf.Structures
import Batteries.Data.UInt

open Proto

macro "update " f:Lean.Parser.Term.structInstLVal : term => `(λ x v => { x with $f := v })

/--
Helper function for defining `parseField` for a structure (Protobuf message).
For example, for a struct with fields `name` and `value`,
```
  parseField (t : Tag) := do
     match t.fieldNum with
     | 1 => parseFieldElement t name (update name)
     | 2 => parseFieldElement t value (update value)
     | _ => let _ ← t.wireType.skip ; pure ignore
```

Note that `β` is the type of the field, while `α` is the type of the entire struct
-/
def parseFieldElement {α β} [Field β] (t : Tag) (f : α → β) (g : α → β → α) : BParsec (MergeFn α) := do
  let x : β ← Field.guardedParse t
  let merge (result : α) (x : β) :=
     let old : β := f result
     g result (Field.merge old x)
  pureMergeFn (merge · x)
