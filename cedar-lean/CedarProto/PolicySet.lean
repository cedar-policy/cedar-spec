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

-- Message Dependencies
import CedarProto.TemplateBody
import CedarProto.Policy

open Proto

namespace Cedar.Spec

structure PolicySet where
  templates : Proto.Map String Template
  links : Proto.Map String TemplateLinkedPolicy
deriving Inhabited

namespace PolicySet

@[inline]
def mergeTemplates (result : PolicySet) (x : Proto.Map String Template) : PolicySet :=
  {result with
    templates := result.templates ++ x
  }

@[inline]
def mergeLinks (result : PolicySet) (x : Proto.Map String TemplateLinkedPolicy) : PolicySet :=
  {result with
    links := result.links ++ x
  }

@[inline]
def merge (x y : PolicySet) : PolicySet :=
  {
    templates := x.templates ++ y.templates
    links := x.links ++ y.links
  }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn PolicySet) := do
  match t.fieldNum with
    | 1 =>
      let x : Proto.Map String Template ← Field.guardedParse t
      pure (pure $ mergeTemplates · x)
    | 2 =>
      let x : Proto.Map String TemplateLinkedPolicy ← Field.guardedParse t
      pure (pure $ mergeLinks · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message PolicySet := {
  parseField := parseField
  merge := merge
}

end PolicySet


namespace Policies

@[inline]
def fromPolicySet (x : PolicySet) : Policies :=
  let templates := Cedar.Data.Map.make x.templates.toList
  let links := x.links.map (λ ⟨id, p⟩ => (p.mergeId id).mkWf)
  match link? templates links.toList with
  | .ok policies => policies
  | .error e => panic!(s!"fromPolicySet: failed to link templates: {e}\n  templates: {repr templates}\n  links: {repr links.toList}}")

@[inline]
private def merge (x y : Policies) : Policies :=
  x ++ y

instance : Field Policies := Field.fromInterField fromPolicySet merge

end Policies
end Cedar.Spec
