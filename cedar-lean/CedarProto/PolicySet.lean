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
import Protobuf.Map
import Protobuf.Message
import Protobuf.Structure

-- Message Dependencies
import CedarProto.TemplateBody
import CedarProto.Policy

open Proto

namespace Cedar.Spec.Proto

structure PolicySet where
  templates : Proto.Map String Template
  links     : Proto.Map String TemplateLinkedPolicy
deriving Inhabited

namespace PolicySet

@[inline]
def mergeTemplates (result : PolicySet) (x : Proto.Map String Template) : PolicySet :=
  { result with
    templates := result.templates ++ x }

@[inline]
def mergeLinks (result : PolicySet) (x : Proto.Map String TemplateLinkedPolicy) : PolicySet :=
  { result with
    links := result.links ++ x }

@[inline]
def merge (x y : PolicySet) : PolicySet :=
  { templates := x.templates ++ y.templates,
    links     := x.links     ++ y.links }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn PolicySet) := do
  match t.fieldNum with
  | 1 =>
    let x : Proto.Map String Template ← Field.guardedParse t
    pureMergeFn (mergeTemplates · x)
  | 2 =>
    let x : Proto.Map String TemplateLinkedPolicy ← Field.guardedParse t
    pureMergeFn (mergeLinks · x)
  | _ =>
    t.wireType.skip
    pure ignore

instance : Message PolicySet := {
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t templates (update templates)
    | 2 => parseFieldElement t links (update links)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    templates := Field.merge x.templates y.templates,
    links     := Field.merge x.links     y.links
  }
}

def toPolicies : PolicySet → Spec.Policies
  | { templates, links } =>
    let templates := Data.Map.make templates.toList
    match link? templates (links.toList.map Prod.snd) with
    | .ok policies => policies
    | .error e     => panic!(s!"toPolicies: failed to link templates: {e}\n  templates: {repr templates}\n  links: {repr links.toList}")

end PolicySet

end Cedar.Spec.Proto

namespace Cedar.Spec

instance : Field Policies :=
  Field.fromInterField Proto.PolicySet.toPolicies (· ++ ·)

end Cedar.Spec
