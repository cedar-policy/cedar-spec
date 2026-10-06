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

module

public import Cedar.Validation.Types

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

----- PartialEntitySchemaEntry -----

public inductive PartialEntitySchemaEntry where
  | defined (entry : EntitySchemaEntry)
  | external (parents : Set EntityType)
deriving Repr

public def PartialEntitySchemaEntry.isValidEntityEID (entry : PartialEntitySchemaEntry) (eid : String) : Bool :=
  match entry with
  | .defined e  => e.isValidEntityEID eid
  | .external _ => true

public def PartialEntitySchemaEntry.tags? : PartialEntitySchemaEntry → Option (Option CedarType)
  | .defined e  => some e.tags?
  | .external _ => none

public def PartialEntitySchemaEntry.attrs? : PartialEntitySchemaEntry → Option RecordType
  | .defined e  => some e.attrs
  | .external _ => none

public def PartialEntitySchemaEntry.ancestors : PartialEntitySchemaEntry → Set EntityType
  | .defined e        => e.ancestors
  | .external parents => parents

public def PartialEntitySchemaEntry.isStandard : PartialEntitySchemaEntry → Bool
  | .defined e  => e.isStandard
  | .external _ => true

public def PartialEntitySchemaEntry.isExternal : PartialEntitySchemaEntry → Bool
  | .defined _  => false
  | .external _ => true

public def PartialEntitySchemaEntry.toEntitySchemaEntry? : PartialEntitySchemaEntry → Option EntitySchemaEntry
  | .defined e  => some e
  | .external _ => none

public def PartialEntitySchemaEntry.withAncestors (ancestors : Set EntityType) : PartialEntitySchemaEntry → PartialEntitySchemaEntry
  | .defined e  => .defined (e.withAncestors ancestors)
  | .external _ => .external ancestors

public instance : Coe EntitySchemaEntry PartialEntitySchemaEntry := ⟨.defined⟩

----- PartialActionSchemaEntry -----

public inductive PartialActionSchemaEntry where
  | defined (entry : ActionSchemaEntry)
  | external (parents : Set EntityUID)
deriving Repr

public def PartialActionSchemaEntry.ancestors : PartialActionSchemaEntry → Set EntityUID
  | .defined e        => e.ancestors
  | .external parents => parents

public def PartialActionSchemaEntry.isExternal : PartialActionSchemaEntry → Bool
  | .defined _  => false
  | .external _ => true

public def PartialActionSchemaEntry.toActionSchemaEntry? : PartialActionSchemaEntry → Option ActionSchemaEntry
  | .defined e  => some e
  | .external _ => none

public def PartialActionSchemaEntry.withAncestors (ancestors : Set EntityUID) : PartialActionSchemaEntry → PartialActionSchemaEntry
  | .defined e  => .defined { e with ancestors }
  | .external _ => .external ancestors

public instance : Coe ActionSchemaEntry PartialActionSchemaEntry := ⟨.defined⟩

----- PartialSchema -----

public abbrev PartialEntitySchema := Map EntityType PartialEntitySchemaEntry

public abbrev PartialActionSchema := Map EntityUID PartialActionSchemaEntry

public structure PartialSchema where
  ets  : PartialEntitySchema
  acts : PartialActionSchema
deriving Repr

----- Schema → PartialSchema -----

@[coe]
public def Schema.toPartialSchema (s : Schema) : PartialSchema :=
  { ets  := s.ets.mapOnValues .defined,
    acts := s.acts.mapOnValues .defined }

public instance : Coe Schema PartialSchema := ⟨Schema.toPartialSchema⟩

----- PartialSchema → Schema -----

public def PartialSchema.isComplete (ps : PartialSchema) : Bool :=
  ps.ets.values.all (!·.isExternal) && ps.acts.values.all (!·.isExternal)

public def PartialSchema.asSchema? (ps : PartialSchema) : Option Schema := do
  let ets  ← ps.ets.mapMOnValues (·.toEntitySchemaEntry?)
  let acts ← ps.acts.mapMOnValues (·.toActionSchemaEntry?)
  pure { ets, acts }

end Cedar.Validation
