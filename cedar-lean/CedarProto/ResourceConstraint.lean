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
import CedarProto.PrincipalOrResourceConstraint

open Proto

namespace Cedar.Spec

namespace ResourceScopeTemplate

@[inline]
def mergeConstraint (result: ResourceScopeTemplate) (x: ScopeTemplate.PrincipalOrResourceConstraint) : ResourceScopeTemplate :=
  let ⟨ sc1 ⟩ := result
  .resourceScope (ScopeTemplate.merge sc1 (x.toScopeTemplate "?resource"))

@[inline]
def merge (x: ResourceScopeTemplate) (y: ResourceScopeTemplate) : ResourceScopeTemplate :=
  let ⟨ sc1 ⟩ := x
  let ⟨ sc2 ⟩ := y
  .resourceScope (ScopeTemplate.merge sc1 sc2)

def parseField (t: Tag) : BParsec (StateM ResourceScopeTemplate Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ScopeTemplate.PrincipalOrResourceConstraint) t.wireType
      let x: ScopeTemplate.PrincipalOrResourceConstraint ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeConstraint s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

deriving instance Inhabited for ResourceScopeTemplate
instance : Message ResourceScopeTemplate := {
  parseField := parseField
  merge := merge
}

end ResourceScopeTemplate
