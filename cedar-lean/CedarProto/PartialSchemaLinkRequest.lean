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
import Cedar.Validation.Linker
import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.Schema

open Proto

namespace Cedar.Validation

deriving instance DecidableEq for ActionSchemaEntry
deriving instance DecidableEq for PartialEntitySchemaEntry
deriving instance DecidableEq for PartialActionSchemaEntry
deriving instance DecidableEq for PartialSchema

namespace Proto

/-- `linked` is absent when linking is expected to fail. -/
structure PartialSchemaLinkRequest where
  first : Validation.PartialSchema
  second : Validation.PartialSchema
  linked : Option Validation.PartialSchema
deriving Repr, Inhabited

namespace PartialSchemaLinkRequest

instance : Message PartialSchemaLinkRequest where
  parseField (t : Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t first (update first)
    | 2 => parseFieldElement t second (update second)
    | 3 => parseFieldElement t linked (update linked)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    first  := Field.merge x.first  y.first
    second := Field.merge x.second y.second
    linked := Field.merge x.linked y.linked
  }

end PartialSchemaLinkRequest

end Proto

/-- Check that linking agrees with `linked`; `none` means expected failure. -/
def checkLink
    (first second : PartialSchema)
    (linked : Option PartialSchema) : Except String Unit :=
  match link first second, linked with
  | .ok ours, some theirs =>
    if ours == theirs then .ok ()
    else .error s!"both linkers accepted, but produced different schemas: model produced {repr ours}, but was given {repr theirs}"
  | .error _, none => .ok ()
  | .error e, some _ => .error s!"the model rejected the pair ({e}), but the other linker accepted it"
  | .ok _, none => .error "the model accepted the pair, but the other linker rejected it"

end Cedar.Validation
