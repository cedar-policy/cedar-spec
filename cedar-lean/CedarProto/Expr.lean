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
import Protobuf.Message
import Protobuf.Enum
import Protobuf.Map

-- Message Dependencies
import CedarProto.EntityUID

open Proto

namespace Cedar.Spec

namespace Prim

-- Already defined
-- inductive Prim where
--   | bool (b : Bool)
--   | int (i : Int64)
--   | string (s : String)
--   | entityUID (uid : EntityUID)
-- Note: This is the same as Literal in the proto file

@[inline]
def merge_bool (p: Prim) (b2: Bool) : Prim :=
  match p with
    | .bool b1 => Prim.bool (Field.merge b1 b2)
    | _ => Prim.bool b2

@[inline]
def merge_int (_: Prim) (pi: Proto.Int64) : Prim :=
  have i : Int := pi
  if H1: i < Cedar.Data.INT64_MIN then
    panic!("Integer less than INT64_MIN")
  else if H2: i > Cedar.Data.INT64_MAX then
    panic!("Integer greater than INT64_MAX")
  else
    have h1 : Cedar.Data.INT64_MIN ≤ i ∧ i ≤ Cedar.Data.INT64_MAX := by
      unfold Proto.Int64 at *
      omega

    -- Override semantics
    Prim.int (Cedar.Data.Int64.mk i h1)

@[inline]
def merge_string (p: Prim) (s2: String) : Prim :=
  match p with
    | .string s1 => Prim.string (Field.merge s1 s2)
    | _ => Prim.string s2

@[inline]
def merge_euid (p: Prim) (euid2: EntityUID): Prim :=
  match p with
    | .entityUID euid1 => Prim.entityUID (Field.merge euid1 euid2)
    | _ => Prim.entityUID euid2

@[inline]
def merge (p1: Prim) (p2: Prim) : Prim :=
  match p2 with
    | .bool b2 => merge_bool p1 b2
    | .int i2 =>
      let i2_1 : Int := i2
      let i2_2 : Proto.Int64 := i2_1
      merge_int p1 i2_2
    | .string s2 => merge_string p1 s2
    | .entityUID e2 => merge_euid p1 e2

def parseField (t: Tag) : BParsec (StateM Prim Unit) := do
  match t.fieldNum with
    -- NOTE: Skipping parsing 1 for now since I may make this a oneof
    | 2 =>
      (@Field.guardWireType Bool) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Bool))
      pure (modifyGet fun s => Prod.mk () (s.merge_bool x))
    | 3 =>
      (@Field.guardWireType Int64) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Int64))
      pure (modifyGet fun s => Prod.mk () (s.merge_int x))
    | 4 =>
      (@Field.guardWireType String) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec String))
      pure (modifyGet fun s => Prod.mk () (s.merge_string x))
    | 5 =>
      (@Field.guardWireType EntityUID) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec EntityUID))
      pure (modifyGet fun s => Prod.mk () (s.merge_euid x))
    | _ =>
      t.wireType.skip
      pure (pure ())

instance : Message Prim := {
  parseField := parseField
  merge := merge
}

end Prim

namespace Var
def fromInt (n: Int) : Except String Var :=
  match n with
    | 0 => .ok .principal
    | 1 => .ok .action
    | 2 => .ok .resource
    | 3 => .ok .context
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum Var := {
  fromInt := fromInt
}

end Var

inductive UnaryOpProto where
  | na -- Not applicable, ignore this type when creating expression
  | not
  | neg

instance : Inhabited UnaryOpProto where
  default := UnaryOpProto.na

namespace UnaryOpProto
def fromInt (n: Int) : Except String UnaryOpProto :=
  match n with
    | 1 => .ok .not
    | 2 => .ok .neg
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum UnaryOpProto := {
  fromInt := fromInt
}
end UnaryOpProto

inductive BinaryOpProto where
  | na -- not applicable, ignore this type when creating expr
  | eq
  | less
  | lesseq
  | add
  | sub
  | mul
  | in
  | contains
  | containsAll
  | containsAny

instance : Inhabited BinaryOpProto where
  default := BinaryOpProto.na

namespace BinaryOpProto
def fromInt (n: Int) : Except String BinaryOpProto :=
  match n with
    | 1 => .ok .eq
    | 2 => .ok .less
    | 3 => .ok .lesseq
    | 4 => .ok .add
    | 5 => .ok .sub
    | 6 => .ok .mul
    | 7 => .ok .in
    | 8 => .ok .contains
    | 9 => .ok .containsAll
    | 10 => .ok .containsAny
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum BinaryOpProto := {
  fromInt := fromInt
}
end BinaryOpProto

namespace PatElem

inductive PatElemTy where
  | star
  | justChar
deriving Inhabited

namespace PatElemTy
def fromInt (n: Int): Except String PatElemTy :=
  match n with
    | 0 => .ok .star
    | 1 => .ok .justChar
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum PatElemTy := {
  fromInt := fromInt
}
end PatElemTy

@[inline]
def mergeTy (result: PatElem) (x: PatElemTy) : PatElem :=
  -- Same type than do nothing, otherwise instantiate with default
  match x with
    | .star => .star
    | .justChar => match result with
      | .justChar _ => result
      | _ => .justChar default

@[inline]
def mergeC (_: PatElem) (x2: String): PatElem :=
  match x2.data with
    | [c2] => .justChar c2
    | _ => panic!("Only expected a single character in PatElem")

@[inline]
def merge (_: PatElem) (y: PatElem) : PatElem :=
  y

def parseField (t: Tag) : BParsec (StateM PatElem Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType PatElemTy) t.wireType
      let x: PatElemTy ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTy s x))
    | 2 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeC s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

-- We assume in the parse functions above that
-- the default is wildcard/star
#guard default = Cedar.Spec.PatElem.star

instance : Message PatElem := {
  parseField := parseField
  merge := merge
}
end PatElem

inductive ExprKindType where
  | na
  | lit
  | varTy
  | if
  | and
  | or
  | unaryApp
  | binaryApp
  -- TODO: ExtensionFunctionApp
  | getAttr
  | hasAttr
  | like
  | is
  | set
  | record
deriving Inhabited

namespace ExprKindType
def fromInt (n: Int) : Except String ExprKindType :=
  match n with
    | 1 => .ok .lit
    | 2 => .ok .varTy
    | 5 => .ok .if
    | 6 => .ok .and
    | 7 => .ok .or
    | 8 => .ok .unaryApp
    | 9 => .ok .binaryApp
    | 11 => .ok .getAttr
    | 12 => .ok .hasAttr
    | 13 => .ok .like
    | 14 => .ok .is
    | 15 => .ok .set
    | 16 => .ok .record
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum ExprKindType := {
  fromInt := fromInt
}
end ExprKindType

mutual
inductive ExprProto where
  | mk (v : ExprKindProto)

inductive ExprKindProto where
  | lit (l : Prim)
  | var (v : Var)
  | expr (ty: ExprKindType)
    (uop: UnaryOpProto)
    (bop: BinaryOpProto)
    (attr: Attr)
    (args: List ExprProto)
    (pattern: List PatElem)
    (et: EntityTypeProto)
    (record : List (Attr × ExprProto))
    -- TODO: call (xfn: ExtFun) (args: List ExprProto)
end

deriving instance Inhabited for ExprKindProto
deriving instance Inhabited for ExprProto


namespace ExprKindProto

@[inline]
def mergeTy (result: ExprKindProto) (x: ExprKindType) : ExprKindProto :=
  match x with
  | .lit => match result with
    | .lit _ => result
    | _ => .lit default
  | .varTy => match result with
    | .var _ => result
    | _ => .var default
  | ty => match result with
    | .expr _ uop bop attr es1 pat et m => .expr ty uop bop attr es1 pat et m
    | _ => .expr ty default default default default default default default

@[inline]
def mergePrim (result: ExprKindProto) (p2: Prim) : ExprKindProto :=
  match result with
    | .lit p1 => .lit (Field.merge p1 p2)
    | _ => .lit p2

@[inline]
def mergeVar (result: ExprKindProto) (v2: Var) : ExprKindProto :=
  match result with
    | .var v1 => .var (Field.merge v1 v2)
    | _ => .var v2

@[inline]
def mergeArgs (result: ExprKindProto) (es2: Array ExprProto) : ExprKindProto :=
  match result with
    | .expr ty uop bop attr es1 pat et m => .expr ty uop bop attr (es2.toList ++ es1) pat et m
    | _ => .expr default default default default es2.toList default default default


@[inline]
def mergeUop (result: ExprKindProto) (uop2: UnaryOpProto) : ExprKindProto :=
  match result with
    | .expr ty uop1 bop attr es pat et m => .expr ty (Field.merge uop1 uop2) bop attr es pat et m
    | _ => .expr default uop2 default default default default default default

@[inline]
def mergeBop (result: ExprKindProto) (bop2: BinaryOpProto) : ExprKindProto :=
  match result with
    | .expr ty uop bop1 attr es pat et m => .expr ty uop (Field.merge bop1 bop2) attr es pat et m
    | _ => .expr default default bop2 default default default default default

@[inline]
def mergeAttr (result: ExprKindProto) (attr2: String) : ExprKindProto :=
  match result with
    | .expr ty uop bop attr1 es pat et m => .expr ty uop bop (Field.merge attr1 attr2) es pat et m
    | _ => .expr default default default attr2 default default default default

@[inline]
def mergePattern (result: ExprKindProto) (pat2: Array PatElem): ExprKindProto :=
  match result with
    | .expr ty uop bop attr es pat1 et m => .expr ty uop bop attr es (pat2.toList ++ pat1) et m
    | _ => .expr default default default default default pat2.toList default default

@[inline]
def mergeEntityType (result: ExprKindProto) (et2: EntityTypeProto): ExprKindProto :=
  match result with
    | .expr ty uop bop attr es pat et1 m => .expr ty uop bop attr es pat (Field.merge et1 et2) m
    | _ => .expr default default default default default default et2 default

@[inline]
def mergeRecord (result: ExprKindProto) (m2: (Array (String × ExprProto))) : ExprKindProto :=
  match result with
    | .expr ty uop bop attr es pat et m1 => .expr ty uop bop attr es pat et (m2.toList ++ m1)
    | _ => .expr default default default default default default default m2.toList

@[inline]
def merge (x1: ExprKindProto) (x2: ExprKindProto) : ExprKindProto :=
  match x2 with
    | .lit l2 => mergePrim x1 l2
    | .var v2 => mergeVar x1 v2
    | .expr ty2 uop2 bop2 attr2 es2 pat2 et2 m2 => match x2 with
      | .expr ty1 uop1 bop1 attr1 es1 pat1 et1 m1 => .expr
        (Field.merge ty1 ty2) (Field.merge uop1 uop2)
        (Field.merge bop1 bop2)  (Field.merge attr1 attr2)
        (es1 ++ es2) (pat1 ++ pat2)
        (Field.merge et1 et2) (m1 ++ m2)
      | _ => x2

end ExprKindProto

-- There's one additinoal message wrapped around ExprKind
-- that we need to parse
namespace ExprProto

@[inline]
def mergeExprKind (x1: ExprProto) (v2: ExprKindProto) : ExprProto :=
  let ⟨ v1 ⟩ := x1
  .mk (ExprKindProto.merge v1 v2)

@[inline]
def merge (x1: ExprProto) (x2: ExprProto) : ExprProto :=
  let ⟨ v1 ⟩ := x1
  let ⟨ v2 ⟩ := x2
  .mk (ExprKindProto.merge v1 v2)

partial def toExpr (v: ExprProto) : Expr :=
  let ⟨vi⟩ := v
  match vi with
    | .lit p => .lit p
    | .var p => .var p
    | .expr ty uop bop attr es pat et m =>
      match ty with
        | .na => panic!("Expected an expression type")
        | .lit => panic!("Unexpected constructor for expression type")
        | .varTy => panic!("Unexpected constructor for expression type")
        | .if => match es with
          | [test_cond, then_expr, else_expr] => .ite test_cond.toExpr then_expr.toExpr else_expr.toExpr
          | _ => panic!("Expected three subexpressions to build .ite")
        | .and => match es with
          | [left, right] => .and left.toExpr right.toExpr
          | _ => panic!("Expected two subexpressions to build .and")
        | .or => match es with
          | [left, right] => .or left.toExpr right.toExpr
          | _ => panic!("Expected two subexpressions to build .or")
        | .unaryApp => match es with
          | [arg] => match uop with
            | .na => panic!("Expected a uop type")
            | .not => .unaryApp .not arg.toExpr
            | .neg => .unaryApp .neg arg.toExpr
          | _ => panic!("Expected a single subexpression to construct a .unaryApp")
        | .binaryApp => match es with
          | [left, right] => match bop with
            | .na => panic!("Expected a bop type")
            | .eq => .binaryApp .eq left.toExpr right.toExpr
            | .less => .binaryApp .less left.toExpr right.toExpr
            | .lesseq => .binaryApp .lessEq left.toExpr right.toExpr
            | .add => .binaryApp .add left.toExpr right.toExpr
            | .sub => .binaryApp .sub left.toExpr right.toExpr
            | .mul => .binaryApp .mul left.toExpr right.toExpr
            | .in => .binaryApp .mem left.toExpr right.toExpr
            | .contains => .binaryApp .contains left.toExpr right.toExpr
            | .containsAll => .binaryApp .containsAll left.toExpr right.toExpr
            | .containsAny => .binaryApp .containsAny left.toExpr right.toExpr
          | _ => panic!("Expected two subexpressions to build .binaryApp")
        | .getAttr => match es with
          | [arg] => .getAttr arg.toExpr attr
          | _ => panic!("Expected a single subexpression to construct .getAttr")
        | .hasAttr => match es with
          | [arg] => .hasAttr arg.toExpr attr
          | _ => panic!("Expected a single subexpression to consturct .hasAttr")
        | .like => match es with
          | [arg] => .unaryApp (.like pat) arg.toExpr
          | _ => panic!("Expected a single subexpression to construct .like")
        | .is => match es with
          | [arg] => .unaryApp (.is et) arg.toExpr
          | _ => panic!("Expected a single subexpression to construct .is")
        | .set => .set (es.map toExpr)
        | .record => .record (m.map (fun ⟨attr, e⟩ => ⟨attr, e.toExpr⟩))

end ExprProto

-- The Value message depends on ValueKind
-- and the recursive components of ValueKind
-- depends on Value
mutual
partial def parseFieldExprKindProto (t: Tag) : BParsec (StateM ExprKindProto Unit) := do
  have : Message ExprKindProto := {parseField := parseFieldExprKindProto, merge := ExprKindProto.merge}
  have : Message ExprProto := { parseField := parseFieldExprProto, merge := ExprProto.merge}

  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ExprKindType) t.wireType
      let x: ExprKindType ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeTy x))
    | 2 =>
      (@Field.guardWireType Prim) t.wireType
      let x: Prim ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergePrim x))
    | 3 =>
      (@Field.guardWireType Var) t.wireType
      let x: Var ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeVar x))
    | 11 =>
      (@Field.guardWireType UnaryOpProto) t.wireType
      let x : UnaryOpProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeUop x))
    | 13 =>
      (@Field.guardWireType BinaryOpProto) t.wireType
      let x : BinaryOpProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeBop x))
    | 17 =>
      (@Field.guardWireType (Repeated ExprProto)) t.wireType
      let x: Repeated ExprProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeArgs x))
    | 19 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeAttr x))
    | 20 =>
      (@Field.guardWireType (Repeated PatElem)) t.wireType
      let x: Repeated PatElem ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergePattern x))
    | 21 =>
      (@Field.guardWireType EntityTypeProto) t.wireType
      let x: EntityTypeProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeEntityType x))
    | 22 =>
      (@Field.guardWireType (Array (String × ExprProto))) t.wireType
      let x: Array (String × ExprProto) ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (s.mergeRecord x))
    | _ =>
      t.wireType.skip
      pure (pure ())


partial def parseFieldExprProto (t: Tag) : BParsec (StateM ExprProto Unit) := do
  have : Message ExprKindProto := {parseField := parseFieldExprKindProto, merge := ExprKindProto.merge}
  have : Message ExprProto := { parseField := parseFieldExprProto, merge := ExprProto.merge}
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType ExprKindProto) t.wireType
      let x: ExprKindProto ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (ExprProto.mergeExprKind s x))
    | _ =>
      t.wireType.skip
      pure (pure ())

end

instance : Message ExprKindProto := {
  parseField := parseFieldExprKindProto
  merge := ExprKindProto.merge
}

instance : Message ExprProto := {
  parseField := parseFieldExprProto
  merge := ExprProto.merge
}

namespace Expr

def merge (e1: Expr) (e2: Expr) : Expr :=
  match e2 with
  | .lit p2 => match e1 with
    | .lit p1 => .lit (Field.merge p1 p2)
    | _ => e2
  | .var v2 => match e1 with
    | .var v1 => .var (Field.merge v1 v2)
    | _ => e2
  | .ite cond2 thenExpr2 elseExpr2 => match e1 with
    | .ite cond1 thenExpr1 elseExpr1 => .ite
      (merge cond1 cond2) (merge thenExpr1 thenExpr2)
      (merge elseExpr1 elseExpr2)
    | _ => e2
  | .and left2 right2 => match e1 with
    | .and left1 right1 => .and
      (merge left1 left2) (merge right1 right2)
    | _ => e2
  | .or left2 right2 => match e1 with
    | .and left1 right1 => .and
      (merge left1 left2) (merge right1 right2)
    | _ => e2
  | .unaryApp op2 expr2 => match e1 with
    | .unaryApp op1 expr1 =>
      let newOp := match (op1, op2) with
        | ⟨.like p1, .like p2⟩ => .like (p1 ++ p2)
        | ⟨.is et1, .is et2⟩ => .is (Field.merge et1 et2)
        | _ => op2
      .unaryApp newOp (merge expr1 expr2)
    | _ => e2
  | .binaryApp op2 left2 right2 => match e1 with
    | .binaryApp _ left1 right1 => .binaryApp op2 (merge left1 left2) (merge right1 right2)
    | _ => e2
  | .getAttr expr2 attr2 => match e1 with
    | .getAttr expr1 attr1 => .getAttr (merge expr1 expr2) (Field.merge attr1 attr2)
    | _ => e2
  | .hasAttr expr2 attr2 => match e1 with
    | .hasAttr expr1 attr1 => .hasAttr (merge expr1 expr2) (Field.merge attr1 attr2)
    | _ => e2
  | .set es2 => match e1 with
    | .set es1 => .set (es1 ++ es2)
    | _ => e2
  | .record m2 => match e1 with
    | .record m1 => .record (m1 ++ m2)
    | _ => e2
  | _ => e2 -- TODO: ExtFun


instance : Field Expr := Field.fromInterField ExprProto.toExpr merge

end Expr

end Cedar.Spec
