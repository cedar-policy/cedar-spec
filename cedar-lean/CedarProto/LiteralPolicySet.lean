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
  templates : Array (String × Template)
  links : Array (String × TemplateLinkedPolicy)
deriving Inhabited

namespace LiteralPolicySet

@[inline]
def mergeTemplates (result : LiteralPolicySet) (x : Array (String × Template)) : LiteralPolicySet :=
  {result with
    templates := result.templates ++ x
  }

@[inline]
def mergeLinks (result : LiteralPolicySet) (x : Array (String × TemplateLinkedPolicy)) : LiteralPolicySet :=
  {result with
    links := result.links ++ x
  }

@[inline]
def merge (x y : LiteralPolicySet) : LiteralPolicySet :=
  {
    templates := x.templates ++ y.templates
    links := x.links ++ y.links
  }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn LiteralPolicySet) := do
  match t.fieldNum with
    | 1 =>
      let x : Proto.Map String Template ← Field.guardedParse t
      pure (mergeTemplates · x)
    | 2 =>
      let x : Proto.Map String TemplateLinkedPolicy ← Field.guardedParse t
      pure (mergeLinks · x)
    | _ =>
      t.wireType.skip
      pure id

instance : Message LiteralPolicySet := {
  parseField := parseField
  merge := merge
}

end LiteralPolicySet


namespace Policies

@[inline]
def fromLiteralPolicySet (x : LiteralPolicySet) : Policies :=
  let templates := Cedar.Data.Map.make x.templates.toList
  let links := x.links.map (λ ⟨id, p⟩ => (p.mergeId id).mkWf)
  match link? templates links.toList with
  | .some policies => policies
  | .none => panic!("fromLiteralPolicySet: failed to link templates")

@[inline]
private def merge (x y : Policies) : Policies :=
  x ++ y

instance : Field Policies := Field.fromInterField fromLiteralPolicySet merge

end Policies
end Cedar.Spec
