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
import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.EntityUID

open Proto

namespace Cedar.Spec.Proto

structure Policy where
  templateId : String
  linkId : Option String
  isTemplateLink : Bool
  principalEuid : Option EntityUID
  resourceEuid : Option EntityUID
deriving Repr, Inhabited

namespace Policy

instance : Message Policy := {
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t templateId (update templateId)
    | 2 => parseFieldElement t linkId (update linkId)
    | 3 => parseFieldElement t isTemplateLink (update isTemplateLink)
    | 4 => parseFieldElement t principalEuid (update principalEuid)
    | 5 => parseFieldElement t resourceEuid (update resourceEuid)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    templateId     := Field.merge x.templateId     y.templateId
    linkId         := Field.merge x.linkId         y.linkId
    isTemplateLink := Field.merge x.isTemplateLink y.isTemplateLink
    principalEuid  := Field.merge x.principalEuid  y.principalEuid
    resourceEuid   := Field.merge x.resourceEuid   y.resourceEuid
  }
}

def toTemplateLinkedPolicy (p : Policy) : Spec.TemplateLinkedPolicy :=
  {
    templateId := p.templateId
    id := if p.isTemplateLink then
      match p.linkId with | some id => id | none => panic!("template link should have a linkId")
    else
      p.templateId -- for static policies, the id is the template id
    slotEnv := Data.Map.make $ match p.principalEuid, p.resourceEuid with
      | some p, some r => [("?principal", p), ("?resource", r)]
      | some p, none   => [("?principal", p)]
      | none,   some r => [("?resource", r)]
      | none,   none   => []
  }

end Policy

end Cedar.Spec.Proto

namespace Cedar.Spec

deriving instance Inhabited for TemplateLinkedPolicy

def TemplateLinkedPolicy.merge (x y : TemplateLinkedPolicy) : TemplateLinkedPolicy := {
  templateId := Field.merge x.templateId y.templateId
  id := Field.merge x.id y.id
  slotEnv := match x.slotEnv.kvs, y.slotEnv.kvs with
    -- avoid sort if either are empty
    | [], _ => y.slotEnv
    | _, [] => x.slotEnv
    | xkvs, ykvs  => Data.Map.make $ xkvs ++ ykvs
}

instance : Field TemplateLinkedPolicy := Field.fromInterField (Proto.Policy.toTemplateLinkedPolicy) TemplateLinkedPolicy.merge

end Cedar.Spec
