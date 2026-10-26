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

module

public import CedarRustModel.Extracted
public import Cedar.Spec
public import Cedar.Thm.Data.Set
public import Cedar.Thm.Data.Map
import all Cedar.Spec.Ext.IPAddr

/-!
Structural translation (`toSpec`) of the extracted Rust model into the Lean spec.
Sets and maps are not re-sorted; the `WF` predicates require them canonical.
-/

namespace CedarRustModel

open Cedar.Data Cedar.Spec
open cedar_rust_model (value.List)

@[expose] public section

def List.toList {α} : value.List α → _root_.List α
  | .Nil => []
  | .Cons x xs => x :: List.toList xs

def Str.toSpec (s : value.List Char) : String :=
  String.ofList (List.toList s)

def Name.toSpec (n : cedar_rust_model.value.Name) : Cedar.Spec.Name :=
  { id := Str.toSpec n.id, path := (List.toList n.path).map Str.toSpec }

def EntityUID.toSpec (u : cedar_rust_model.value.EntityUID) : Cedar.Spec.EntityUID :=
  { ty := Name.toSpec u.ty, eid := Str.toSpec u.eid }

def Prim.toSpec : cedar_rust_model.value.Prim → Cedar.Spec.Prim
  | .Bool b => .bool b
  | .Int i => .int (Int64.ofInt i.val)
  | .String s => .string (Str.toSpec s)
  | .EntityUID u => .entityUID (EntityUID.toSpec u)

/-! ## Extension values -/

/-- `Cedar.Spec.Ext.IPAddr.IPNetPrefix.ofNat` (which is private to its module) -/
def prefixOfNat (w p : Nat) : Cedar.Spec.Ext.IPAddr.IPNetPrefix w :=
  if p < Cedar.Spec.Ext.IPAddr.ADDR_SIZE w then some (BitVec.ofNat w p) else none

def IPNet.toSpec : cedar_rust_model.ext.IPNet → Cedar.Spec.Ext.IPAddr.IPNet
  | .V4 a p => .V4 ⟨BitVec.ofNat 32 a.val, prefixOfNat Cedar.Spec.Ext.IPAddr.V4_WIDTH p.val⟩
  | .V6 a p => .V6 ⟨BitVec.ofNat 128 a.val, prefixOfNat Cedar.Spec.Ext.IPAddr.V6_WIDTH p.val⟩

def Ext.toSpec : cedar_rust_model.ext.Ext → Cedar.Spec.Ext
  | .Decimal d => .decimal (Int64.ofInt d.val)
  | .IPAddr a => .ipaddr (IPNet.toSpec a)
  | .Datetime d => .datetime ⟨Int64.ofInt d.val⟩
  | .Duration d => .duration ⟨Int64.ofInt d.val⟩

def ExtFun.toSpec : cedar_rust_model.ext.ExtFun → Cedar.Spec.ExtFun
  | .Decimal => .decimal
  | .LessThan => .lessThan
  | .LessThanOrEqual => .lessThanOrEqual
  | .GreaterThan => .greaterThan
  | .GreaterThanOrEqual => .greaterThanOrEqual
  | .Ip => .ip
  | .IsIpv4 => .isIpv4
  | .IsIpv6 => .isIpv6
  | .IsLoopback => .isLoopback
  | .IsMulticast => .isMulticast
  | .IsInRange => .isInRange
  | .Datetime => .datetime
  | .Duration => .duration
  | .Offset => .offset
  | .DurationSince => .durationSince
  | .ToDate => .toDate
  | .ToTime => .toTime
  | .ToMilliseconds => .toMilliseconds
  | .ToSeconds => .toSeconds
  | .ToMinutes => .toMinutes
  | .ToHours => .toHours
  | .ToDays => .toDays

mutual

def Value.toSpec : cedar_rust_model.value.Value → Cedar.Spec.Value
  | .Prim p => .prim (Prim.toSpec p)
  | .Set vs => .set (Set.mk (Values.toSpec vs))
  | .Record avs => .record (Map.mk (Attrs.toSpec avs))
  | .Ext e => .ext (Ext.toSpec e)

def Values.toSpec : value.List cedar_rust_model.value.Value → _root_.List Cedar.Spec.Value
  | .Nil => []
  | .Cons v vs => Value.toSpec v :: Values.toSpec vs

def Attrs.toSpec :
    value.List (value.List Char × cedar_rust_model.value.Value) → _root_.List (Attr × Cedar.Spec.Value)
  | .Nil => []
  | .Cons (a, v) avs => (Str.toSpec a, Value.toSpec v) :: Attrs.toSpec avs

end

def Error.toSpec : cedar_rust_model.value.Error → Cedar.Spec.Error
  | .EntityDoesNotExist => .entityDoesNotExist
  | .AttrDoesNotExist => .attrDoesNotExist
  | .TagDoesNotExist => .tagDoesNotExist
  | .TypeError => .typeError
  | .ArithBoundsError => .arithBoundsError
  | .ExtensionError => .extensionError

def Result.toSpec {α β} (f : α → β) :
    Aeneas.Std.core.result.Result α cedar_rust_model.value.Error → Cedar.Spec.Result β
  | .Ok v => .ok (f v)
  | .Err e => .error (Error.toSpec e)

def Var.toSpec : cedar_rust_model.expr.Var → Cedar.Spec.Var
  | .Principal => .principal
  | .Action => .action
  | .Resource => .resource
  | .Context => .context

def PatElem.toSpec : cedar_rust_model.expr.PatElem → Cedar.Spec.PatElem
  | .Star => .star
  | .JustChar c => .justChar c

def UnaryOp.toSpec : cedar_rust_model.expr.UnaryOp → Cedar.Spec.UnaryOp
  | .Not => .not
  | .Neg => .neg
  | .IsEmpty => .isEmpty
  | .Like p => .like ((List.toList p).map PatElem.toSpec)
  | .Is ety => .is (Name.toSpec ety)

def BinaryOp.toSpec : cedar_rust_model.expr.BinaryOp → Cedar.Spec.BinaryOp
  | .Eq => .eq
  | .Mem => .mem
  | .HasTag => .hasTag
  | .GetTag => .getTag
  | .Less => .less
  | .LessEq => .lessEq
  | .Add => .add
  | .Sub => .sub
  | .Mul => .mul
  | .Contains => .contains
  | .ContainsAll => .containsAll
  | .ContainsAny => .containsAny

mutual

def Expr.toSpec : cedar_rust_model.expr.Expr → Cedar.Spec.Expr
  | .Lit p => .lit (Prim.toSpec p)
  | .Var v => .var (Var.toSpec v)
  | .Ite x₁ x₂ x₃ => .ite (Expr.toSpec x₁) (Expr.toSpec x₂) (Expr.toSpec x₃)
  | .And x₁ x₂ => .and (Expr.toSpec x₁) (Expr.toSpec x₂)
  | .Or x₁ x₂ => .or (Expr.toSpec x₁) (Expr.toSpec x₂)
  | .UnaryApp op x₁ => .unaryApp (UnaryOp.toSpec op) (Expr.toSpec x₁)
  | .BinaryApp op x₁ x₂ => .binaryApp (BinaryOp.toSpec op) (Expr.toSpec x₁) (Expr.toSpec x₂)
  | .GetAttr x₁ a => .getAttr (Expr.toSpec x₁) (Str.toSpec a)
  | .HasAttr x₁ a => .hasAttr (Expr.toSpec x₁) (Str.toSpec a)
  | .ExtHasAttr x₁ a as' => .extHasAttr (Expr.toSpec x₁) (Str.toSpec a) ((List.toList as').map Str.toSpec)
  | .Set xs => .set (Exprs.toSpec xs)
  | .Record axs => .record (AttrExprs.toSpec axs)
  | .Call f xs => .call (ExtFun.toSpec f) (Exprs.toSpec xs)

def Exprs.toSpec : value.List cedar_rust_model.expr.Expr → _root_.List Cedar.Spec.Expr
  | .Nil => []
  | .Cons x xs => Expr.toSpec x :: Exprs.toSpec xs

def AttrExprs.toSpec :
    value.List (value.List Char × cedar_rust_model.expr.Expr) → _root_.List (Attr × Cedar.Spec.Expr)
  | .Nil => []
  | .Cons (a, x) axs => (Str.toSpec a, Expr.toSpec x) :: AttrExprs.toSpec axs

end

def Request.toSpec (r : cedar_rust_model.request.Request) : Cedar.Spec.Request :=
  { principal := EntityUID.toSpec r.principal
    action := EntityUID.toSpec r.action
    resource := EntityUID.toSpec r.resource
    context := Map.mk (Attrs.toSpec r.context) }

def EntityData.toSpec (d : cedar_rust_model.entities.EntityData) : Cedar.Spec.EntityData :=
  { attrs := Map.mk (Attrs.toSpec d.attrs)
    ancestors := Set.mk ((List.toList d.ancestors).map EntityUID.toSpec)
    tags := Map.mk (Attrs.toSpec d.tags) }

def Entities.toSpec
    (es : value.List (cedar_rust_model.value.EntityUID × cedar_rust_model.entities.EntityData)) :
    Cedar.Spec.Entities :=
  Map.mk ((List.toList es).map fun (u, d) => (EntityUID.toSpec u, EntityData.toSpec d))

def Decision.toSpec : cedar_rust_model.authorizer.Decision → Cedar.Spec.Decision
  | .Allow => .allow
  | .Deny => .deny

def Response.toSpec (r : cedar_rust_model.authorizer.Response) : Cedar.Spec.Response :=
  { decision := Decision.toSpec r.decision
    determiningPolicies := Set.mk ((List.toList r.determining_policies).map Str.toSpec)
    erroringPolicies := Set.mk ((List.toList r.erroring_policies).map Str.toSpec) }

def Effect.toSpec : cedar_rust_model.authorizer.Effect → Cedar.Spec.Effect
  | .Permit => .permit
  | .Forbid => .forbid

/-- Same ID and effect, and `Policy.toExpr` is the translated condition. -/
def Policy.Corresponds (p : cedar_rust_model.authorizer.Policy) (lp : Cedar.Spec.Policy) : Prop :=
  lp.id = Str.toSpec p.id ∧ lp.effect = Effect.toSpec p.effect ∧ lp.toExpr = Expr.toSpec p.condition

end -- public section

end CedarRustModel
