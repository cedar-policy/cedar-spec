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

import Cedar.Validation.Types
import Cedar.PQ.ResourcesForPrincipal

namespace Cedar.PQ

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

def isUnqualifiedPolicy (p : Policy) : Bool :=
  p.principalScope.scope.bound == none &&
  p.resourceScope.scope.bound == none

def isPrincipalPolicyUnqualifiedResource (principal : EntityUID) (p : Policy) : Bool :=
  p.principalScope.scope.bound == some principal &&
  p.resourceScope.scope.bound == none

def isUnqualifiedPrincipalResourceTypePolicy (resourceType : EntityType) (p : Policy) : Bool :=
  p.principalScope.scope.bound == none &&
  match p.resourceScope.scope.bound with
  | some e => e.ty == resourceType
  | none => true

def isPrincipalPolicyForResourceType (principal : EntityUID) (resourceType : EntityType) (p : Policy) : Bool :=
  p.principalScope.scope.bound == some principal &&
  match p.resourceScope.scope.bound with
  | some e => e.ty == resourceType
  | none => true

def isPrincipalParentPolicy (principalAncestor : EntityUID) (resourceType : EntityType) (p : Policy) : Bool :=
  p.principalScope.scope.bound == some principalAncestor &&
  match p.resourceScope.scope.bound with
  | some e => e.ty == resourceType
  | none => true

def policySliceByResourceType (pq : ResourcesForPrincipalRequest) (policies : Policies) (entities : Entities) (schema : Schema)  : Policies :=
  let resourceAncestorTypes := schema.ancestorTypes pq.resourceType
  policies.filter λ p =>
      isUnqualifiedPolicy p ||
      resourceAncestorTypes.any (isUnqualifiedPrincipalResourceTypePolicy · p) ||
      isPrincipalPolicyUnqualifiedResource pq.principal p ||
      resourceAncestorTypes.any (isPrincipalPolicyForResourceType pq.principal · p) ||
      resourceAncestorTypes.any ((entities.ancestorsOrEmpty pq.principal).any λ group => isPrincipalParentPolicy group · p)
