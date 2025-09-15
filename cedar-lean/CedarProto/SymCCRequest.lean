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
import CedarProto.Term

-- Message Dependencies
import CedarProto.Policy
import CedarProto.PolicySet
import CedarProto.RequestEnv
import CedarProto.Schema

open Proto


namespace Cedar.SymCC.Proto

structure Policy where
  template : Spec.Proto.Template
  policy : Spec.TemplateLinkedPolicy
deriving Inhabited

namespace Policy

instance : Message Policy where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t template (update template)
    | 2 => parseFieldElement t policy (update policy)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    template := Field.merge x.template y.template
    policy := Field.merge x.policy y.policy
  }

def toPolicy : Policy -> Except String Spec.Policy
  | { template, policy } =>
    let template := template.toIdAndTemplate.snd
    match template.link? policy.id policy.slotEnv with
    | .ok policy => .ok policy
    | .error s => .error s

end Policy
end Cedar.SymCC.Proto

namespace Cedar.Spec

def Scope.merge (x y : Spec.Scope) : Spec.Scope :=
  match x, y with
  | .any, .any => .any
  | .eq e₁, .eq e₂ => .eq (Field.merge e₁ e₂)
  | .mem e₁, .mem e₂ => .mem (Field.merge e₁ e₂)
  | .is n₁, .is n₂ => .is (Field.merge n₁ n₂)
  | .isMem n₁ e₁, .isMem n₂ e₂ => .isMem (Field.merge n₁ n₂) (Field.merge e₁ e₂)
  | _, _ => y

def PrincipalScope.merge (x y : PrincipalScope) : PrincipalScope :=
  let ⟨ sc₁ ⟩ := x
  let ⟨ sc₂ ⟩ := y
  .principalScope (Scope.merge sc₁ sc₂)

def ResourceScope.merge (x y : ResourceScope) : ResourceScope :=
  let ⟨ sc₁ ⟩ := x
  let ⟨ sc₂ ⟩ := y
  .resourceScope (Scope.merge sc₁ sc₂)

def Policy.merge (x y : Spec.Policy) : Spec.Policy := {
  id             := Field.merge x.id y.id
  effect         := Field.merge x.effect y.effect
  principalScope := x.principalScope.merge y.principalScope
  actionScope    := Field.merge x.actionScope y.actionScope
  resourceScope  := x.resourceScope.merge y.resourceScope
  condition      := Field.merge x.condition y.condition
}

instance : Field Policy :=
  Field.fromInterFieldFallible SymCC.Proto.Policy.toPolicy Policy.merge

end Cedar.Spec

namespace Cedar.SymCC.Proto

structure CheckPolicyRequest where
  policy  : Spec.Policy
  request : Validation.Proto.RequestEnv
deriving Inhabited

namespace CheckPolicyRequest

instance : Message CheckPolicyRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t policy (update policy)
    | 3 => parseFieldElement t request (update request)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    policy  := Field.merge x.policy y.policy
    request := Field.merge x.request y.request
  }

end CheckPolicyRequest

structure CheckPolicySetRequest where
  policySet : Spec.Policies
  request : Validation.Proto.RequestEnv
deriving Inhabited

namespace CheckPolicySetRequest

instance : Message CheckPolicySetRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t policySet (update policySet)
    | 3 => parseFieldElement t request (update request)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    policySet := Field.merge x.policySet y.policySet
    request := Field.merge x.request y.request
  }

end CheckPolicySetRequest

structure ComparePolicySetsRequest where
  srcPolicySet : Spec.Policies
  tgtPolicySet : Spec.Policies
  request : Validation.Proto.RequestEnv
deriving Inhabited

namespace ComparePolicySetsRequest

instance : Message ComparePolicySetsRequest where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t srcPolicySet (update srcPolicySet)
    | 2 => parseFieldElement t tgtPolicySet (update tgtPolicySet)
    | 4 => parseFieldElement t request (update request)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    srcPolicySet := Field.merge x.srcPolicySet y.srcPolicySet
    tgtPolicySet := Field.merge x.tgtPolicySet y.tgtPolicySet
    request := Field.merge x.request y.request
  }

end ComparePolicySetsRequest

structure CheckAssertsRequest where
  asserts : Cedar.SymCC.Asserts
  request : Validation.Proto.RequestEnv
deriving Inhabited

namespace CheckAssertsRequest

instance : Field Cedar.SymCC.Asserts := Field.fromInterFieldFallible (λ (asserts: Cedar.SymCC.Proto.Asserts) =>
  match asserts.toCedar with
  | .some asserts => .ok asserts
  | .none => .error "Failed to convert to proto-Asserts to cedar-Asserts"
) (· ++ ·)

instance : Message CheckAssertsRequest where
  parseField (t : Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t asserts (update asserts)
    | 3 => parseFieldElement t request (update request)
    | _ => t.wireType.skip ; pure ignore

  merge x y := {
    asserts := Field.merge x.asserts y.asserts
    request := Field.merge x.request y.request
  }

end CheckAssertsRequest

end Cedar.SymCC.Proto
