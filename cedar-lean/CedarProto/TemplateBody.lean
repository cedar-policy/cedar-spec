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

instance : Field PrincipalScopeTemplate := Field.fromInterField .principalScope merge

end PrincipalScopeTemplate

namespace ResourceScopeTemplate

deriving instance Inhabited for ResourceScopeTemplate

@[inline]
def merge (x : ResourceScopeTemplate) (y : ResourceScopeTemplate) : ResourceScopeTemplate :=
  let ⟨ sc1 ⟩ := x
  let ⟨ sc2 ⟩ := y
  .resourceScope (ScopeTemplate.merge sc1 sc2)

instance : Field ResourceScopeTemplate := Field.fromInterField .resourceScope merge

end ResourceScopeTemplate

-- Note that Cedar.Spec.Template is defined as
-- structure Template where
--   effect : Effect
--   principalScope : PrincipalScopeTemplate
--   actionScope : ActionScope
--   resourceScope : ResourceScopeTemplate
--   condition : Conditions

-- Forbid is the default for Rust protobuf, but Lean auto-derives `permit` as
-- the default. We use a manual derivation here to resolve the discrepancy.
instance : Inhabited Effect where default := .forbid
deriving instance Inhabited for Template -- must come after the Inhabited Effect instance

namespace Template

@[inline]
def mergeEffect (result : Template) (x : Effect) : Template :=
  {result with
    effect := Field.merge result.effect x
  }

@[inline]
def mergePrincipalScope (result : Template) (x : ScopeTemplate) : Template :=
  have ⟨ result_st ⟩ := result.principalScope
  {result with
    principalScope := .principalScope $ ScopeTemplate.merge result_st (x.withSlot "?principal")
  }

@[inline]
def mergeActionScope (result : Template) (x : ActionScope) : Template :=
  {result with
    actionScope := Field.merge result.actionScope x
  }

@[inline]
def mergeResourceScope (result : Template) (x : ScopeTemplate) : Template :=
  have ⟨ result_st ⟩ := result.resourceScope
  {result with
    resourceScope := .resourceScope $ ScopeTemplate.merge result_st (x.withSlot "?resource")
  }

@[inline]
def mergeConditions (result : Template) (x : Conditions) : Template :=
  {result with
    condition := Field.merge result.condition x
  }

@[inline]
def merge (x y : Template) : Template :=
  {
    effect := Field.merge x.effect y.effect
    principalScope := Field.merge x.principalScope y.principalScope
    actionScope := Field.merge x.actionScope y.actionScope
    resourceScope := Field.merge x.resourceScope y.resourceScope
    condition := Field.merge x.condition y.condition
  }

@[inline]
def parseField (t : Proto.Tag) : BParsec (MergeFn Template) := do
  match t.fieldNum with
    -- NOTE: Doesn't look like id gets utilized in this message
    | 4 =>
      let x : Effect ← Field.guardedParse t
      pure (pure $ mergeEffect · x)
    | 5 =>
      let x : ScopeTemplate ← Field.guardedParse t
      pure (pure $ mergePrincipalScope · x)
    | 6 =>
      let x : ActionScope ← Field.guardedParse t
      pure (pure $ mergeActionScope · x)
    | 7 =>
      let x : ScopeTemplate ← Field.guardedParse t
      pure (pure $ mergeResourceScope · x)
    | 8 =>
      let x : Conditions ← Field.guardedParse t
      pure (pure $ mergeConditions · x)
    | _ =>
      t.wireType.skip
      pure ignore

instance : Message Template := {
  parseField := parseField
  merge := merge
}

end Template

end Cedar.Spec
