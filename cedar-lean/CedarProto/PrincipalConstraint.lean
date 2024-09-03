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
namespace PrincipalScopeTemplate

@[inline]
def mergeConstraint (result: PrincipalScopeTemplate) (x: Cedar.Spec.ScopeTemplate) : PrincipalScopeTemplate :=
  have ⟨ sc1 ⟩ := result
  .principalScope (ScopeTemplate.merge sc1 (x.withSlot "?principal"))

@[inline]
def merge (x: PrincipalScopeTemplate) (y: PrincipalScopeTemplate) : PrincipalScopeTemplate :=
  have ⟨ sc1 ⟩ := x
  have ⟨ sc2 ⟩ := y
  .principalScope (ScopeTemplate.merge sc1 sc2)

def parseField (t: Tag) : BParsec (StateM PrincipalScopeTemplate Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ScopeTemplate) t.wireType
      let x: ScopeTemplate ← Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeConstraint s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

deriving instance Inhabited for PrincipalScopeTemplate
instance : Message PrincipalScopeTemplate := {
  parseField := parseField
  merge := merge
}

end PrincipalScopeTemplate
end Cedar.Spec
