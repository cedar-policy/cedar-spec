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
import CedarProto.TemplateBody
import CedarProto.LiteralPolicy

open Proto

namespace Cedar.Spec

structure LiteralPolicySet where
  templates: Array (String × Template)
  links: Array (String × TemplateLinkedPolicy)
deriving Inhabited

namespace LiteralPolicySet

@[inline]
def mergeTemplates (result: LiteralPolicySet) (x: Array (String × Template)) : LiteralPolicySet :=
  {result with
    templates := x ++ result.templates
  }

@[inline]
def mergeLinks (result: LiteralPolicySet) (x: Array (String × TemplateLinkedPolicy)): LiteralPolicySet :=
  {result with
    links := x ++ result.links
  }

@[inline]
def merge (x y: LiteralPolicySet) : LiteralPolicySet :=
  {x with
    templates := y.templates ++ x.templates
    links := y.links ++ x.links
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

end LiteralPolicySet


namespace Policies

def fromLiteralPolicySet (x: LiteralPolicySet) : Policies :=
  let templates := Cedar.Data.Map.make x.templates.toList
  let links := (x.links.map (fun ⟨id, p⟩ => (p.mergeId id).mkWf)).toList
  match link? templates links with
  | .some policies => policies
  | .none => panic!("fromLiteralPolicySet: failed to link templates")

private def merge (x y : Policies): Policies :=
  y ++ x

instance : Field Policies := Field.fromInterField fromLiteralPolicySet merge

end Policies
end Cedar.Spec
