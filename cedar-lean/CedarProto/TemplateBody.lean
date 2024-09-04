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
import CedarProto.Expr
import CedarProto.PrincipalConstraint
import CedarProto.ActionConstraint
import CedarProto.ResourceConstraint

open Proto

namespace Cedar.Spec

namespace Effect
def fromInt (n: Int): Except String Effect :=
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
def merge (c1 c2: Conditions) : Conditions :=
  c1 ++ c2

-- Emulating the behavior from the JSON parser
-- where it is assumed that conditions are formed
-- from one condition of type "when"
@[inline]
private def fromExpr (e: Expr) : Conditions :=
  [{kind := .when, body := e}]

instance : Field Conditions := Field.fromInterField fromExpr merge

end Conditions

namespace Template

-- Already defined in Cedar.Spec
-- structure Template where
--   effect : Effect
--   principalScope : PrincipalScopeTemplate
--   actionScope : ActionScope
--   resourceScope : ResourceScopeTemplate
--   condition : Conditions
deriving instance Inhabited for Template

@[inline]
def mergeEffect (result: Template) (x: Effect): Template :=
  {result with
    effect := Field.merge result.effect x
  }

@[inline]
def mergePrincipalScope (result: Template) (x: PrincipalScopeTemplate) : Template :=
  {result with
    principalScope := Field.merge result.principalScope x
  }

@[inline]
def mergeActionScope (result: Template) (x: ActionScope): Template :=
  {result with
    actionScope := Field.merge result.actionScope x
  }

@[inline]
def mergeResourceScope (result: Template) (x: ResourceScopeTemplate) : Template :=
  {result with
    resourceScope := Field.merge result.resourceScope x
  }

@[inline]
def mergeConditions (result: Template) (x: Conditions): Template :=
  {result with
    condition := Field.merge result.condition x
  }

@[inline]
def merge (x y: Template) : Template :=
  {x with
    effect := Field.merge x.effect y.effect
    principalScope := Field.merge x.principalScope y.principalScope
    actionScope := Field.merge x.actionScope y.actionScope
    resourceScope := Field.merge x.resourceScope y.resourceScope
    condition := Field.merge x.condition y.condition
  }

@[inline]
def parseField (t: Tag) : BParsec (MergeFn Template) := do
  match t.fieldNum with
    -- NOTE: Doesn't look like id gets utilized in this message
    | 4 =>
      (@Field.guardWireType Effect) t.wireType
      let x: Effect ← Field.parse
      pure (fun s => mergeEffect s x)
    | 5 =>
      (@Field.guardWireType PrincipalScopeTemplate) t.wireType
      let x: PrincipalScopeTemplate ← Field.parse
      pure (fun s => mergePrincipalScope s x)
    | 6 =>
      (@Field.guardWireType ActionScope) t.wireType
      let x: ActionScope ← Field.parse
      pure (fun s => mergeActionScope s x)
    | 7 =>
      (@Field.guardWireType ResourceScopeTemplate) t.wireType
      let x: ResourceScopeTemplate ← Field.parse
      pure (fun s => mergeResourceScope s x)
    | 8 =>
      (@Field.guardWireType Conditions) t.wireType
      let x: Conditions ← Field.parse
      pure (fun s => mergeConditions s x)
    | _ =>
      t.wireType.skip
      pure (fun s => s)

instance : Message Template := {
  parseField := parseField
  merge := merge
}

end Template

end Cedar.Spec
