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
import Cedar

-- Message Dependencies
import CedarProto.EntityUID

open Proto

namespace Cedar.Spec

namespace TemplateLinkedPolicy

-- Already defined
-- structure TemplateLinkedPolicy where
--   id : PolicyID
--   templateId : TemplateID
--   slotEnv : SlotEnv

@[inline]
def mergeId (result: TemplateLinkedPolicy) (x: String) : TemplateLinkedPolicy :=
  {result with
    id := Field.merge result.id x
  }

@[inline]
def mergeTemplateId (result: TemplateLinkedPolicy) (x: String): TemplateLinkedPolicy :=
  {result with
    templateId := Field.merge result.templateId x
  }

@[inline]
def mergePrincipalEuid (result: TemplateLinkedPolicy) (x: EntityUID): TemplateLinkedPolicy :=
  let elem : (SlotID × EntityUID) := Prod.mk "prinicpal" x
  {result with
    slotEnv := Cedar.Data.Map.mk (elem :: result.slotEnv.kvs)
  }

@[inline]
def mergeResourceEuid (result: TemplateLinkedPolicy) (x: EntityUID): TemplateLinkedPolicy :=
  let elem : (SlotID × EntityUID) := Prod.mk "resource" x
  {result with
    slotEnv := Cedar.Data.Map.mk (elem :: result.slotEnv.kvs)
  }

@[inline]
def merge (x: TemplateLinkedPolicy) (y: TemplateLinkedPolicy) : TemplateLinkedPolicy :=
  {x with
    id := Field.merge x.id y.id
    templateId := Field.merge x.id y.id
    slotEnv := Cedar.Data.Map.mk (y.slotEnv.kvs ++ x.slotEnv.kvs)
  }

def parseField (t: Tag) : BParsec (StateM TemplateLinkedPolicy Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTemplateId s x))
    | 2 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeId s x))
    | 4 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergePrincipalEuid s x))
    | 5 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x: EntityUID ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeResourceEuid s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

deriving instance Inhabited for TemplateLinkedPolicy
instance : Message TemplateLinkedPolicy := {
  parseField := parseField
  merge := merge
}

end TemplateLinkedPolicy

end Cedar.Spec
