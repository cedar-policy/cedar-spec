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
import CedarProto.Expr
import CedarProto.ActionConstraint
import CedarProto.PrincipalOrResourceConstraint

open Proto

namespace Cedar.Spec

namespace Effect
def fromInt (n : Int) : Except String Effect :=
  match n with
  | 0 => .ok .forbid
  | 1 => .ok .permit
  | n => .error s!"Field {n} does not exist in enum"

instance : Inhabited Effect := {
  default := .forbid
}

instance : ProtoEnum Effect := {
  fromInt := fromInt
}
end Effect

namespace Conditions

@[inline]
def merge (c1 c2 : Conditions) : Conditions :=
  c1 ++ c2

-- Emulating the behavior from the JSON parser
-- where it is assumed that conditions are formed
-- from one condition of type "when"
@[inline]
private def fromExpr (e : Expr) : Conditions :=
  [{kind := .when, body := e}]

instance : Field Conditions := Field.fromInterField fromExpr merge

end Conditions

namespace PrincipalScopeTemplate

deriving instance Inhabited for PrincipalScopeTemplate

@[inline]
def merge (x : PrincipalScopeTemplate) (y : PrincipalScopeTemplate) : PrincipalScopeTemplate :=
  have ⟨ sc1 ⟩ := x
  have ⟨ sc2 ⟩ := y
  .principalScope (ScopeTemplate.merge sc1 sc2)

instance : Field PrincipalScopeTemplate := Field.fromInterField
  (λ (st : ScopeTemplate) => .principalScope $ st.withSlot "?principal")
  merge

end PrincipalScopeTemplate

namespace ResourceScopeTemplate

deriving instance Inhabited for ResourceScopeTemplate

@[inline]
def merge (x : ResourceScopeTemplate) (y : ResourceScopeTemplate) : ResourceScopeTemplate :=
  let ⟨ sc1 ⟩ := x
  let ⟨ sc2 ⟩ := y
  .resourceScope (ScopeTemplate.merge sc1 sc2)

instance : Field ResourceScopeTemplate := Field.fromInterField
  (λ (st : ScopeTemplate) => .resourceScope $ st.withSlot "?resource")
  merge

end ResourceScopeTemplate

namespace Proto

/-- Exactly like `Cedar.Spec.Template` except that it carries the `id` -/
structure Template where
  id : String
  effect : Effect
  principalScope : PrincipalScopeTemplate
  actionScope : ActionScope
  resourceScope : ResourceScopeTemplate
  condition : Conditions

-- Forbid is the default for Rust protobuf, but Lean auto-derives `permit` as
-- the default. We use a manual derivation here to resolve the discrepancy.
instance : Inhabited Effect where default := .forbid
deriving instance Inhabited for Template -- must come after the Inhabited Effect instance

namespace Template

instance : Message Template where
  parseField (t : Proto.Tag) := do
    match t.fieldNum with
    | 1 => parseFieldElement t id (update id)
    | 4 => parseFieldElement t effect (update effect)
    | 5 => parseFieldElement t principalScope (update principalScope)
    | 6 => parseFieldElement t actionScope (update actionScope)
    | 7 => parseFieldElement t resourceScope (update resourceScope)
    | 8 => parseFieldElement t condition (update condition)
    | _ => let _ ← t.wireType.skip ; pure ignore

  merge x y := {
    id             := Field.merge x.id             y.id
    effect         := Field.merge x.effect         y.effect
    principalScope := Field.merge x.principalScope y.principalScope
    actionScope    := Field.merge x.actionScope    y.actionScope
    resourceScope  := Field.merge x.resourceScope  y.resourceScope
    condition      := Field.merge x.condition      y.condition
  }

def toIdAndTemplate : Proto.Template → String × Spec.Template
  | { id, effect, principalScope, actionScope, resourceScope, condition } =>
    (id, { effect, principalScope, actionScope, resourceScope, condition })

end Template
end Proto
end Cedar.Spec
