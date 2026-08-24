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

import Protobuf.Message
import Protobuf.Map
import Protobuf.String

-- Message Dependencies
import CedarProto.Expr
import CedarProto.Name
import CedarProto.Type
import CedarProto.Value
import Cedar.TPE.Residual

/-!
Parsing of the `Residual` protobuf message.
-/

namespace Cedar.Spec.Proto

open _root_.Proto

inductive ResidualKind where
  | val | var | ite | and | or | unaryApp | binaryApp
  | getAttr | hasAttr | set | record | call | error | like | is
deriving Inhabited, Repr

namespace ResidualKind

def fromInt : Int → Except String ResidualKind
  | 0  => .ok .val
  | 1  => .ok .var
  | 2  => .ok .ite
  | 3  => .ok .and
  | 4  => .ok .or
  | 5  => .ok .unaryApp
  | 6  => .ok .binaryApp
  | 7  => .ok .getAttr
  | 8  => .ok .hasAttr
  | 9  => .ok .set
  | 10 => .ok .record
  | 11 => .ok .call
  | 12 => .ok .error
  | 13 => .ok .like
  | 14 => .ok .is
  | n  => .error s!"Field {n} does not exist in Residual.Kind"

instance : ProtoEnum ResidualKind := { fromInt := fromInt }

end ResidualKind

structure ProtoResidual where
  ty         : Option Validation.Proto.ProtoType := none
  kind       : ResidualKind := .val
  children   : List ProtoResidual := []
  val        : Option Expr := none
  var        : Var := .principal
  attr       : String := ""
  fieldNames : List String := []
  unaryOp    : Proto.ExprKind.UnaryApp.Op := .not
  binaryOp   : Proto.ExprKind.BinaryApp.Op := .eq
  fnName     : Option Spec.Proto.Name := none
  pattern    : Pattern := []
  entityType : Option EntityType := none

instance : Inhabited ProtoResidual where
  default := {}

namespace ProtoResidual

def merge (r₁ r₂ : ProtoResidual) : ProtoResidual :=
  { ty         := match r₁.ty, r₂.ty with
                  | some t₁, some t₂ => some (Validation.Proto.ProtoType.merge t₁ t₂)
                  | some t, none | none, some t => some t
                  | none, none => none
    kind       := r₂.kind
    children   := r₁.children ++ r₂.children
    val        := r₂.val.orElse (λ _ => r₁.val)
    var        := r₂.var
    attr       := Field.merge r₁.attr r₂.attr
    fieldNames := r₁.fieldNames ++ r₂.fieldNames
    unaryOp    := r₂.unaryOp
    binaryOp   := r₂.binaryOp
    fnName     := r₂.fnName.orElse (λ _ => r₁.fnName)
    pattern    := r₁.pattern ++ r₂.pattern
    entityType := r₂.entityType.orElse (λ _ => r₁.entityType) }

partial def parseField (t : _root_.Proto.Tag) : BParsec (MergeFn ProtoResidual) := do
  have : Message ProtoResidual := ⟨parseField, merge⟩
  match t.fieldNum with
  | 1 =>
    let x : Validation.Proto.ProtoType ← Field.guardedParse t
    pureMergeFn (λ r => { r with ty := some (match r.ty with
                                             | some t₀ => Validation.Proto.ProtoType.merge t₀ x
                                             | none    => x) })
  | 2 =>
    let x : ResidualKind ← Field.guardedParse t
    pureMergeFn (λ r => { r with kind := x })
  | 3 =>
    let x : Repeated ProtoResidual ← Field.guardedParse t
    pureMergeFn (λ r => { r with children := r.children ++ x.toList })
  | 4 =>
    let x : Expr ← Field.guardedParse t
    pureMergeFn (λ r => { r with val := some x })
  | 5 =>
    let x : Var ← Field.guardedParse t
    pureMergeFn (λ r => { r with var := x })
  | 6 =>
    let x : String ← Field.guardedParse t
    pureMergeFn (λ r => { r with attr := Field.merge r.attr x })
  | 7 =>
    let x : Repeated String ← Field.guardedParse t
    pureMergeFn (λ r => { r with fieldNames := r.fieldNames ++ x.toList })
  | 8 =>
    let x : Proto.ExprKind.UnaryApp.Op ← Field.guardedParse t
    pureMergeFn (λ r => { r with unaryOp := x })
  | 9 =>
    let x : Proto.ExprKind.BinaryApp.Op ← Field.guardedParse t
    pureMergeFn (λ r => { r with binaryOp := x })
  | 10 =>
    let x : Spec.Proto.Name ← Field.guardedParse t
    pureMergeFn (λ r => { r with fnName := some x })
  | 11 =>
    let x : Pattern ← Field.guardedParse t
    pureMergeFn (λ r => { r with pattern := r.pattern ++ x })
  | 12 =>
    let x : EntityType ← Field.guardedParse t
    pureMergeFn (λ r => { r with entityType := some x })
  | _ =>
    t.wireType.skip
    pure ignore

instance : Message ProtoResidual := ⟨parseField, merge⟩

/-! ### Conversion to the model's `Residual` -/

def unaryOpOf : Proto.ExprKind.UnaryApp.Op → UnaryOp
  | .not     => .not
  | .neg     => .neg
  | .isEmpty => .isEmpty

def binaryOpOf : Proto.ExprKind.BinaryApp.Op → BinaryOp
  | .eq          => .eq
  | .less        => .less
  | .lesseq      => .lessEq
  | .add         => .add
  | .sub         => .sub
  | .mul         => .mul
  | .in          => .mem
  | .contains    => .contains
  | .containsAll => .containsAll
  | .containsAny => .containsAny
  | .getTag      => .getTag
  | .hasTag      => .hasTag

def extFunOf (n : Spec.Proto.Name) : Except String ExtFun :=
  match n.id with
  | "decimal"            => .ok .decimal
  | "lessThan"           => .ok .lessThan
  | "lessThanOrEqual"    => .ok .lessThanOrEqual
  | "greaterThan"        => .ok .greaterThan
  | "greaterThanOrEqual" => .ok .greaterThanOrEqual
  | "ip"                 => .ok .ip
  | "isIpv4"             => .ok .isIpv4
  | "isIpv6"             => .ok .isIpv6
  | "isLoopback"         => .ok .isLoopback
  | "isMulticast"        => .ok .isMulticast
  | "isInRange"          => .ok .isInRange
  | "datetime"           => .ok .datetime
  | "duration"           => .ok .duration
  | "offset"             => .ok .offset
  | "durationSince"      => .ok .durationSince
  | "toDate"             => .ok .toDate
  | "toTime"             => .ok .toTime
  | "toMilliseconds"     => .ok .toMilliseconds
  | "toSeconds"          => .ok .toSeconds
  | "toMinutes"          => .ok .toMinutes
  | "toHours"            => .ok .toHours
  | "toDays"             => .ok .toDays
  | _                    => .error s!"unknown extension function {n.toName}"

/--
Convert a parsed message to a `Residual`.
-/
partial def toResidual (r : ProtoResidual) : Except String Residual := do
  let some protoTy := r.ty
    | .error s!"Residual: missing `ty` on a {repr r.kind} node"
  let ty ← protoTy.toCedarType
  let kids ← r.children.mapM toResidual
  let arity (n : Nat) : Except String Unit :=
    if kids.length == n then .ok ()
    else .error s!"Residual: {repr r.kind} expects {n} children, got {kids.length}"
  match r.kind, kids with
  | .val, _ => do
    arity 0
    let some e := r.val | .error "Residual: VAL without `val`"
    .ok (.val (← Value.exprToValue e) ty)
  | .var, _ => do
    arity 0
    .ok (.var r.var ty)
  | .error, _ => do
    arity 0
    .ok (.error ty)
  | .ite, [c, t, e] => .ok (.ite c t e ty)
  | .and, [a, b] => .ok (.and a b ty)
  | .or, [a, b] => .ok (.or a b ty)
  | .binaryApp, [a, b] => .ok (.binaryApp (binaryOpOf r.binaryOp) a b ty)
  | .unaryApp, [a] => .ok (.unaryApp (unaryOpOf r.unaryOp) a ty)
  | .getAttr, [a] => .ok (.getAttr a r.attr ty)
  | .hasAttr, [a] => .ok (.hasAttr a r.attr ty)
  | .like, [a] => .ok (.unaryApp (.like r.pattern) a ty)
  | .is, [a] => do
    let some ety := r.entityType | .error "Residual: IS without `entity_type`"
    .ok (.unaryApp (.is ety) a ty)
  | .set, _ => .ok (.set kids ty)
  | .call, _ => do
    let some fn := r.fnName | .error "Residual: CALL without `fn_name`"
    .ok (.call (← extFunOf fn) kids ty)
  | .record, _ =>
    if r.fieldNames.length == kids.length
    then .ok (.record (r.fieldNames.zip kids) ty)
    else .error s!"Residual: RECORD has {r.fieldNames.length} names \
                   but {kids.length} children"
  -- Wrong number of children for the kind; `arity` produces the message.
  | .ite, _ => do arity 3; .error "unreachable"
  | .and, _ | .or, _ | .binaryApp, _ => do arity 2; .error "unreachable"
  | .unaryApp, _ | .getAttr, _ | .hasAttr, _ | .like, _ | .is, _ => do
    arity 1; .error "unreachable"

end ProtoResidual

-- Two encodings are two different residuals, so the later one wins rather than being merged.
instance : Field Residual :=
  Field.fromInterFieldFallible ProtoResidual.toResidual (λ _ r₂ => r₂)

end Cedar.Spec.Proto
