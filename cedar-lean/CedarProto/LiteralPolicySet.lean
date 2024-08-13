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
import Protobuf.BParsec
import Protobuf.Message
import Protobuf.String

import CedarProto.TemplateBody
import CedarProto.LiteralPolicy

import Cedar
open Cedar.Spec
open Proto


structure LiteralPolicySet where
  templates: Array (String × Template)
  links: Array (String × TemplateLinkedPolicy)
deriving Inhabited

namespace Cedar.Spec.LiteralPolicySet

@[inline]
def mergeTemplates (result: LiteralPolicySet) (x: Array (String × Template)) : LiteralPolicySet :=
  {result with
    templates := result.templates ++ x
  }

@[inline]
def mergeLinks (result: LiteralPolicySet) (x: Array (String × TemplateLinkedPolicy)): LiteralPolicySet :=
  {result with
    links := result.links ++ x
  }

@[inline]
def merge (x y: LiteralPolicySet) : LiteralPolicySet :=
  {x with
    templates := x.templates ++ y.templates
    links := x.links ++ y.links
  }


def parseField (t: Tag) : BParsec (StateM LiteralPolicySet Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Array (String × Template))) t.wireType
      let x: Array (String × Template) ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTemplates s x))
    | 2 =>
      (@Field.guardWireType (Array (String × TemplateLinkedPolicy))) t.wireType
      let x: Array (String × TemplateLinkedPolicy) ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeLinks s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message LiteralPolicySet := {
  parseField := parseField
  merge := merge
}

end Cedar.Spec.LiteralPolicySet


namespace Cedar.Spec.Policies

def fromLiteralPolicySet (x: LiteralPolicySet) : Policies :=
  match link? (Cedar.Data.Map.make x.templates.toList) (x.links.map (fun ⟨_, p⟩ => p)).toList with
  | .some policies => policies
  | .none => panic!("fromLiteralPolicySet: failed to link templates")

private def merge (x y : Policies): Policies :=
  x ++ y

instance : Field Policies := Field.fromIntField fromLiteralPolicySet merge

end Cedar.Spec.Policies
