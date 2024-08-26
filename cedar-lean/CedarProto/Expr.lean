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

@[inline]
def parseField (t: Tag) : BParsec (StateM Prim Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Bool) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Bool))
      pure (modifyGet fun s => Prod.mk () (s.merge_bool x))
    | 2 =>
      (@Field.guardWireType Int64) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec Int64))
      pure (modifyGet fun s => Prod.mk () (s.merge_int x))
    | 3 =>
      (@Field.guardWireType String) t.wireType
      let x ← BParsec.attempt (Field.parse: (BParsec String))
      pure (modifyGet fun s => Prod.mk () (s.merge_string x))
    | 4 =>
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
@[inline]
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

namespace Proto

-- Wrapper type
def ExprKind := Expr
  deriving Inhabited

-- Recursive constructors for Expr
def ExprKind.If := ExprKind
instance : Inhabited ExprKind.If where
  default := .ite default default default

def ExprKind.And := ExprKind
instance : Inhabited ExprKind.And where
  default := .and default default

def ExprKind.Or := ExprKind
instance : Inhabited ExprKind.Or where
  default := .or default default

def ExprKind.UnaryApp := ExprKind
instance : Inhabited ExprKind.UnaryApp where
  default := .unaryApp default default

def ExprKind.BinaryApp := ExprKind
instance : Inhabited ExprKind.BinaryApp where
  default := .binaryApp default default default

def ExprKind.ExtensionFunctionApp := ExprKind
instance : Inhabited ExprKind.ExtensionFunctionApp where
  default := .call default default

def ExprKind.GetAttr := ExprKind
instance : Inhabited ExprKind.GetAttr where
  default := .getAttr default default

def ExprKind.HasAttr := ExprKind
instance : Inhabited ExprKind.HasAttr where
  default := .hasAttr default default

def ExprKind.Like := ExprKind
instance : Inhabited ExprKind.Like where
  default := .unaryApp (.like default) default

def ExprKind.Is := ExprKind
instance : Inhabited ExprKind.Is where
  default := .unaryApp (.is default) default

def ExprKind.Set := ExprKind
instance : Inhabited ExprKind.Set where
  default := .set default

def ExprKind.Record := ExprKind
instance : Inhabited ExprKind.Record where
  default := .record default

end Proto

-- Expression Merge code
def Expr.merge (e1: Expr) (e2: Expr) : Expr :=
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
  | .call fnName2 args2 => match e1 with
    | .call _ args1 => .call fnName2 (args2 ++ args1)
    | _ => e2

namespace Proto.ExprKind.If
@[inline]
def mergeTestExpr (result: ExprKind.If) (x: Expr): ExprKind.If :=
  match result with
  | .ite testExpr thenExpr elseExpr => .ite (Expr.merge testExpr x) thenExpr elseExpr
  | _ => panic!("Expected ExprKind.If to have .ite constructor")

@[inline]
def mergeThenExpr (result: ExprKind.If) (x: Expr): ExprKind.If :=
  match result with
  | .ite testExpr thenExpr elseExpr => .ite testExpr (Expr.merge thenExpr x) elseExpr
  | _ => panic!("Expected ExprKind.If to have .ite constructor")

@[inline]
def mergeElseExpr (result: ExprKind.If) (x: Expr): ExprKind.If :=
  match result with
  | .ite testExpr thenExpr elseExpr => .ite testExpr thenExpr (Expr.merge elseExpr x)
  | _ => panic!("Expected ExprKind.If to have .ite constructor")

@[inline]
def merge (x1 x2: ExprKind.If): ExprKind.If :=
  have ⟨c2, t2, e2⟩ := match x2 with
    | .ite testExpr thenExpr elseExpr => (testExpr, thenExpr, elseExpr)
    | _ => panic!("Expected ExprKind.If to have .ite constructor")
  match x1 with
    | .ite c1 t1 e1 => .ite (Expr.merge c1 c2) (Expr.merge t1 t2) (Expr.merge e1 e2)
    | _ => panic!("Expected ExprKind.If to have .ite constructor")

-- parseField requires mutual recursion and thus can be found at the end
-- of the file
end Proto.ExprKind.If

namespace Proto.ExprKind.And
@[inline]
def mergeLeft (result: ExprKind.And) (x: Expr): ExprKind.And :=
  match result with
  | .and left right => .and (Expr.merge left x) right
  | _ => panic!("Expected ExprKind.And to have .and constructor")

@[inline]
def mergeRight (result: ExprKind.And) (x: Expr): ExprKind.And :=
  match result with
  | .and left right => .and left (Expr.merge right x)
  | _ => panic!("Expected ExprKind.And to have .and constructor")

@[inline]
def merge (x1 x2: ExprKind.And): ExprKind.And :=
  have ⟨l2, r2⟩ := match x2 with
    | .and left right => (left, right)
    | _ => panic!("Expected Proto.Expr.And to have .and constructor")
  match x1 with
    | .and l1 r1 => .and (Expr.merge l1 l2) (Expr.merge r1 r2)
    | _ => panic!("Expected Proto.Expr.And to have .and constructor")

-- parseField requires mutual recursion and thus can be found at the end
-- of the file
end Proto.ExprKind.And

namespace Proto.ExprKind.Or
@[inline]
def mergeLeft (result: ExprKind.Or) (x: Expr): ExprKind.Or :=
  match result with
  | .or left right => .or (Expr.merge left x) right
  | _ => panic!("Expected ExprKind.Or to have .or constructor")

@[inline]
def mergeRight (result: ExprKind.Or) (x: Expr): ExprKind.Or :=
  match result with
  | .or left right => .or left (Expr.merge right x)
  | _ => panic!("Expected ExprKind.Or to have .or constructor")

@[inline]
def merge (x1 x2: ExprKind.Or): ExprKind.Or :=
  have ⟨l2, r2⟩ := match x2 with
    | .or left right => (left, right)
    | _ => panic!("Expected ExprKind.Or to have .or constructor")
  match x1 with
    | .or l1 r1 => .or (Expr.merge l1 l2) (Expr.merge r1 r2)
    | _ => panic!("Expected ExprKind.Or to have .or constructor")

-- parseField requires mutual recursion and thus can be found at the end
-- of the file
end Proto.ExprKind.Or

namespace Proto.ExprKind.UnaryApp
inductive Op where
  | not
  | neg
deriving Inhabited

namespace Op
@[inline]
def fromInt (n: Int) : Except String Op :=
  match n with
    | 1 => .ok .not
    | 2 => .ok .neg
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum Op := {
  fromInt := fromInt
}
end Op

@[inline]
def mergeOp (result: ExprKind.UnaryApp) (x: Op): ExprKind.UnaryApp :=
  -- Since op is an enum, we perform a replacement
  match result with
  | .unaryApp _ expr => match x with
    | .not => .unaryApp .not expr
    | .neg => .unaryApp .neg expr
  | _ => panic!("Expected ExprKind.UnaryApp to be of constructor .unaryApp")

@[inline]
def mergeArg (result: ExprKind.UnaryApp) (e2: Expr): ExprKind.UnaryApp :=
  match result with
    | .unaryApp op e1 => .unaryApp op (Expr.merge e1 e2)
    | _ => panic!("Expected ExprKind.UnaryApp to be of constructor .unaryApp")

@[inline]
def merge (x1 x2: ExprKind.UnaryApp): ExprKind.UnaryApp :=
  have ⟨op2, e2⟩ := match x2 with
    | .unaryApp op expr => (op, expr)
    | _ => panic!("Expected ExprKind.UnaryApp to be of constructor .unaryApp")
  match x1 with
    | .unaryApp _ e1 => .unaryApp op2 (Expr.merge e1 e2)
    | _ => panic!("Expected ExprKind.UnaryApp to be of constructor .unaryApp")

-- parseField requires mutual recursion and can be found at the end of the file
end Proto.ExprKind.UnaryApp

namespace Proto.ExprKind.BinaryApp
inductive Op where
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
deriving Inhabited

namespace Op
@[inline]
def fromInt (n: Int) : Except String Op :=
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

instance : ProtoEnum Op := {
  fromInt := fromInt
}
end Op

@[inline]
def mergeOp (result: ExprKind.BinaryApp) (x: Op): ExprKind.BinaryApp :=
  match result with
    | .binaryApp _ left right => match x with
      | .eq => .binaryApp .eq left right
      | .less => .binaryApp .less left right
      | .lesseq => .binaryApp .lessEq left right
      | .add => .binaryApp .add left right
      | .sub => .binaryApp .sub left right
      | .mul => .binaryApp .mul left right
      | .in => .binaryApp .mem left right
      | .contains => .binaryApp .contains left right
      | .containsAll => .binaryApp .containsAll left right
      | .containsAny => .binaryApp .containsAny left right
    | _ => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

@[inline]
def mergeLeft (result: ExprKind.BinaryApp) (e2: Expr): ExprKind.BinaryApp :=
  match result with
  | .binaryApp op e1 right => .binaryApp op (Expr.merge e1 e2) right
  | _ => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

@[inline]
def mergeRight (result: ExprKind.BinaryApp) (e2: Expr): ExprKind.BinaryApp :=
  match result with
  | .binaryApp op left e1 => .binaryApp op left (Expr.merge e1 e2)
  | _ => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

@[inline]
def merge (x1 x2: ExprKind.BinaryApp): ExprKind.BinaryApp :=
  have ⟨op2, l2, r2⟩ := match x2 with
    | .binaryApp op left right => (op, left, right)
    | _ => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")
  match x1 with
  | .binaryApp _ l1 r1 => .binaryApp op2 (Expr.merge l1 l2) (Expr.merge r1 r2)
  | _ => panic!("Expected ExprKind.BinaryApp to have constructor .binaryApp")

-- parseField requires mutual reucrsion and can be found at the end of the file
end Proto.ExprKind.BinaryApp

namespace Proto.ExprKind.ExtensionFunctionApp
@[inline]
def mergeName (result: ExprKind.ExtensionFunctionApp) (_: Name): ExprKind.ExtensionFunctionApp :=
  match result with
  | .call _ _ => panic!("Proto.ExprKind.ExtensionFunctionApp: Not Implemented")
  | _ => panic!("Expected ExprKind.ExtensionFunctionApp to have constructor .call")

@[inline]
def mergeArgs (result: ExprKind.ExtensionFunctionApp) (es2: Array Expr): ExprKind.ExtensionFunctionApp :=
  match result with
  | .call n1 es1 => .call n1 (es2.toList ++ es1)
  | _ => panic!("Expected ExprKind.ExtensionFunctionApp to have constructor .call")

@[inline]
def merge (x1 x2: ExprKind.ExtensionFunctionApp): ExprKind.ExtensionFunctionApp :=
  have ⟨n2, es2⟩ := match x2 with
  | .call fnName args => (fnName, args)
  | _ => panic!("Expected ExprKind.ExtensionFunctionApp to have constructor .call")
  match x1 with
  | .call _ es1 => .call n2 (es2 ++ es1)
  | _ => panic!("Expected ExprKind.ExtensionFunctionApp to have constructor .call")

-- parseFIeld requires mutual recursion and can be found at the end of the file
end Proto.ExprKind.ExtensionFunctionApp

namespace Proto.ExprKind.GetAttr
@[inline]
def mergeAttr (result: ExprKind.GetAttr) (attr2: String): ExprKind.GetAttr :=
  match result with
  | .getAttr expr attr1 => .getAttr expr (Field.merge attr1 attr2)
  | _ => panic!("Expected ExprKind.GetAttr to be constructor .getAttr")

@[inline]
def mergeExpr (result: ExprKind.GetAttr) (e2: Expr): ExprKind.GetAttr :=
  match result with
  | .getAttr e1 attr => .getAttr (Expr.merge e1 e2) attr
  | _ => panic!("Expected ExprKind.GetAttr to be constructor .getAttr")

@[inline]
def merge (x1 x2: ExprKind.GetAttr): ExprKind.GetAttr :=
  have ⟨e2, attr2⟩ := match x2 with
  | .getAttr expr attr => (expr, attr)
  | _ => panic!("Expected ExprKind.GetAttr to be constructor .getAttr")
  match x1 with
  | .getAttr e1 attr1 => .getAttr (Expr.merge e1 e2) (Field.merge attr1 attr2)
  | _ => panic!("Expected ExprKind.GetAttr to be constructor .getAttr")

-- parseField requires mutual recursion and can be found at the end of this file
end Proto.ExprKind.GetAttr

namespace Proto.ExprKind.HasAttr
@[inline]
def mergeAttr (result: ExprKind.HasAttr) (attr2: String): ExprKind.HasAttr :=
  match result with
  | .hasAttr expr attr1 => .hasAttr expr (Field.merge attr1 attr2)
  | _ => panic!("Expected ExprKind.HasAttr to be constructor .hasAttr")

@[inline]
def mergeExpr (result: ExprKind.HasAttr) (e2: Expr): ExprKind.HasAttr :=
  match result with
  | .hasAttr e1 attr => .hasAttr (Expr.merge e1 e2) attr
  | _ => panic!("Expected ExprKind.HasAttr to be constructor .hasAttr")

@[inline]
def merge (x1 x2: ExprKind.HasAttr): ExprKind.HasAttr :=
  have ⟨e2, attr2⟩ := match x2 with
  | .hasAttr expr attr => (expr, attr)
  | _ => panic!("Expected ExprKind.HasAttr to be constructor .hasAttr")
  match x1 with
  | .hasAttr e1 attr1 => .hasAttr (Expr.merge e1 e2) (Field.merge attr1 attr2)
  | _ => panic!("Expected ExprKind.HasAttr to be constructor .hasAttr")

-- parseField requires mutual recursion and can be found at the end of this file
end Proto.ExprKind.HasAttr

namespace PatElem
inductive Ty where
  | star
deriving Inhabited

namespace Ty
def fromInt (n: Int): Except String Ty :=
  match n with
    | 0 => .ok .star
    | n => .error s!"Field {n} does not exist in enum"

instance : ProtoEnum Ty := {
  fromInt := fromInt
}
end Ty

@[inline]
def mergeTy (_: PatElem) (x: Ty) : PatElem :=
  -- With enums we perform replacement
  match x with
    | .star => .star

@[inline]
def mergeC (_: PatElem) (x2: String): PatElem :=
  -- With a single character we'll perform replacement
  match x2.data with
    | [c2] => .justChar c2
    | _ => panic!("Only expected a single character in PatElem")

@[inline]
def merge (_: PatElem) (y: PatElem) : PatElem :=
  -- Each constructor of the sum type merges through
  -- replacement, so we'll do the same here
  y

@[inline]
def parseField (t: Tag) : BParsec (StateM PatElem Unit) := do
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Ty) t.wireType
      let x: Ty ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeTy s x))
    | 2 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← BParsec.attempt Field.parse
      pure (modifyGet fun s => Prod.mk () (mergeC s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

instance : Message PatElem := {
  parseField := parseField
  merge := merge
}
end PatElem

namespace Proto.ExprKind.Like
@[inline]
def mergeExpr (result: ExprKind.Like) (e2: Expr): ExprKind.Like :=
  match result with
  | .unaryApp (.like pat) e1 => .unaryApp (.like pat) (Expr.merge e1 e2)
  | _ => panic!("Expected ExprKind.Like to have constructor .unaryApp .like")

@[inline]
def mergePattern (result: ExprKind.Like) (pat2: Array PatElem): ExprKind.Like :=
  match result with
  | .unaryApp (.like pat1) e => .unaryApp (.like (pat2.toList ++ pat1)) e
  | _ => panic!("Expected ExprKind.Like to have constructor .unaryApp .like")

@[inline]
def merge (x1 x2: ExprKind.Like): ExprKind.Like :=
  have ⟨pat2, e2⟩ := match x2 with
  | .unaryApp (.like pat) expr => (pat, expr)
  | _ => panic!("Expected ExprKind.Like to have constructor .unaryApp .like")
  match x1 with
  | .unaryApp (.like pat1) e1 => .unaryApp (.like (pat2 ++ pat1)) (Expr.merge e1 e2)
  | _ => panic!("Expected ExprKind.Like to have constructor .unaryApp .like")

-- parseField relies on mutual recursion and can be found at the end of the file
end Proto.ExprKind.Like

namespace Proto.ExprKind.Is
@[inline]
def mergeExpr (result: ExprKind.Is) (e2: Expr): ExprKind.Is :=
  match result with
  | .unaryApp (.is et) e1 => .unaryApp (.is et) (Expr.merge e1 e2)
  | _ => panic!("Expected ExprKind.Is to have constructor .unaryApp .is")

@[inline]
def mergeEt (result: ExprKind.Is) (et2: EntityTypeProto): ExprKind.Is :=
  match result with
  | .unaryApp (.is et1) e => .unaryApp (.is (Field.merge et1 et2)) e
  | _ => panic!("Expected ExprKind.Is to have constructor .unaryApp .is")

@[inline]
def merge (x1 x2: ExprKind.Is): ExprKind.Is :=
  have ⟨et2, e2⟩ := match x2 with
  | .unaryApp (.is entityType) expr => (entityType, expr)
  | _ => panic!("Expected ExprKind.Is to have constructor .unaryApp .is")
  match x1 with
  | .unaryApp (.is et1) e1 => .unaryApp (.is (Field.merge et1 et2)) (Expr.merge e1 e2)
  | _ => panic!("Expected ExprKind.Is to have constructor .unaryApp .is")

-- parseField relies on mutual recursion and can be found at the end of the file
end Proto.ExprKind.Is

namespace Proto.ExprKind.Set
@[inline]
def mergeElems (result: ExprKind.Set) (es2: Array Expr) : ExprKind.Set :=
  match result with
  | .set es1 => .set (es2.toList ++ es1)
  | _ => panic!("Expected ExprKind.Set to have the .set constructor")

@[inline]
def merge (x1 x2: ExprKind.Set): ExprKind.Set :=
  have es2 := match x2 with
    | .set elements => elements
    | _ => panic!("Expected ExprKind.Set to have the .set constructor")
  match x1 with
  | .set es1 => .set (es2 ++ es1)
  | _ => panic!("Expected ExprKind.Set to have the .set constructor ")

-- parseField relies on mutual recursion and can be found at the
-- end of the file
end Proto.ExprKind.Set

namespace Proto.ExprKind.Record
@[inline]
def mergeItems (result: ExprKind.Record) (its2: Array (String × Expr)) : ExprKind.Record :=
  match result with
  | .record its1 => .record (its2.toList ++ its1)
  | _ => panic!("Expected ExprKind.Record to have constructor .record")

@[inline]
def merge (x1 x2: ExprKind.Record): ExprKind.Record :=
  have its2 := match x2 with
    | .record items => items
    | _ => panic!("Expected ExprKind.Record to have constructor .record")
  match x1 with
  | .record its1 => .record (its2 ++ its1)
  | _ => panic!("Expected ExprKind.Record to have constructor .record")

-- parseField relies on mutual recursion and can be found at the
-- end of the file
end Proto.ExprKind.Record

namespace Proto.ExprKind

@[inline]
def mergePrim (result: ExprKind) (p2: Prim) : ExprKind :=
  match result with
    | .lit p1 => .lit (Field.merge p1 p2)
    | _ => .lit p2

@[inline]
def mergeVar (result: ExprKind) (v2: Var) : ExprKind :=
  match result with
    | .var v1 => .var (Field.merge v1 v2)
    | _ => .var v2

@[inline]
def mergeIf (result: ExprKind) (x: ExprKind.If): ExprKind :=
  match result with
  | .ite _ _ _ => ExprKind.If.merge result x
  | _ => x

@[inline]
def mergeAnd (result: ExprKind) (x: ExprKind.And): ExprKind :=
  match result with
  | .and _ _ => ExprKind.And.merge result x
  | _ => x

@[inline]
def mergeOr (result: ExprKind) (x: ExprKind.Or): ExprKind :=
  match result with
  | .or _ _ => ExprKind.Or.merge result x
  | _ => x

@[inline]
def mergeUApp (result: ExprKind) (x: ExprKind.UnaryApp): ExprKind :=
  match result with
  | .unaryApp _ _ => ExprKind.UnaryApp.merge result x
  | _ => x

@[inline]
def mergeBApp (result: ExprKind) (x: ExprKind.BinaryApp): ExprKind :=
  match result with
  | .binaryApp _ _ _ => ExprKind.BinaryApp.merge result x
  | _ => x

@[inline]
def mergeExtApp (result: ExprKind) (x: ExprKind.ExtensionFunctionApp): ExprKind :=
  match result with
  | .call _ _ => ExprKind.ExtensionFunctionApp.merge result x
  | _ => x

@[inline]
def mergeGetAttr (result: ExprKind) (x: ExprKind.GetAttr): ExprKind :=
  match result with
  | .getAttr _ _ => ExprKind.GetAttr.merge result x
  | _ => x

@[inline]
def mergeHasAttr (result: ExprKind) (x: ExprKind.HasAttr): ExprKind :=
  match result with
  | .hasAttr _ _ => ExprKind.HasAttr.merge result x
  | _ => x

@[inline]
def mergeLike (result: ExprKind) (x: ExprKind.Like): ExprKind :=
  match result with
  | .unaryApp (.like _) _ => ExprKind.Like.merge result x
  | _ => x

@[inline]
def mergeIs (result: ExprKind) (x: ExprKind.Is): ExprKind :=
  match result with
  | .unaryApp (.is _) _ => ExprKind.Is.merge result x
  | _ => x

@[inline]
def mergeSet (result: ExprKind) (x: ExprKind.Set): ExprKind :=
  match result with
  | .set _ => ExprKind.Set.merge result x
  | _ => x

@[inline]
def mergeRecord (result: ExprKind) (x: ExprKind.Record): ExprKind :=
  match result with
  | .record _ => ExprKind.Record.merge result x
  | _ => x

@[inline]
def merge (x1 x2: ExprKind): ExprKind :=
  Expr.merge x1 x2

-- parseField relies on mutual recursion which can be found at the
-- end of this file
end Proto.ExprKind

namespace Expr
-- There's one additinoal message wrapped around ExprKind
-- that we need to parse
@[inline]
def mergeExprKind (x1: Expr) (x2: Proto.ExprKind) : Expr :=
  Expr.merge x1 x2
end Expr

-- Expr depends on ExprKind and ExprKind is a sum type
-- where many of the constructors depend on Epxr
mutual

partial def Proto.ExprKind.If.parseField (t: Tag) : BParsec (StateM Proto.ExprKind.If Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Expr) t.wireType
      let x : Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.If.mergeTestExpr s x))
    | 2 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.If.mergeThenExpr s x))
    | 3 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.If.mergeElseExpr s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.And.parseField (t: Tag) : BParsec (StateM Proto.ExprKind.And Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.And.mergeLeft s x))
    | 2 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.And.mergeRight s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.Or.parseField (t: Tag) : BParsec (StateM Proto.ExprKind.Or Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Or.mergeLeft s x))
    | 2 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Or.mergeRight s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.UnaryApp.parseField (t: Tag) : BParsec (StateM Proto.ExprKind.UnaryApp Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Proto.ExprKind.UnaryApp.Op) t.wireType
      let x: Proto.ExprKind.UnaryApp.Op ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.UnaryApp.mergeOp s x))
    | 2 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.UnaryApp.mergeArg s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.BinaryApp.parseField (t: Tag): BParsec (StateM Proto.ExprKind.BinaryApp Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Proto.ExprKind.BinaryApp.Op) t.wireType
      let x: Proto.ExprKind.BinaryApp.Op ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.BinaryApp.mergeOp s x))
    | 2 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.BinaryApp.mergeLeft s x))
    | 3 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.BinaryApp.mergeRight s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.ExtensionFunctionApp.parseField (t: Tag): BParsec (StateM Proto.ExprKind.ExtensionFunctionApp Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Name) t.wireType
      let x: Name ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.ExtensionFunctionApp.mergeName s x))
    | 2 =>
      (@Field.guardWireType (Repeated Expr)) t.wireType
      let x: Repeated Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.ExtensionFunctionApp.mergeArgs s x))

    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.GetAttr.parseField (t: Tag) : BParsec (StateM Proto.ExprKind.GetAttr Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.GetAttr.mergeExpr s x))
    | 2 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.GetAttr.mergeAttr s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.HasAttr.parseField (t: Tag): BParsec (StateM Proto.ExprKind.HasAttr Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.HasAttr.mergeExpr s x))
    | 2 =>
      (@Field.guardWireType String) t.wireType
      let x: String ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.HasAttr.mergeAttr s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.Like.parseField (t: Tag): BParsec (StateM Proto.ExprKind.Like Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Like.mergeExpr s x))
    | 2 =>
      (@Field.guardWireType (Repeated PatElem)) t.wireType
      let x: Repeated PatElem ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Like.mergePattern s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.Is.parseField (t: Tag): BParsec (StateM Proto.ExprKind.Is Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Expr) t.wireType
      let x: Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Is.mergeExpr s x))
    | 2 =>
      (@Field.guardWireType EntityTypeProto) t.wireType
      let x: EntityTypeProto ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Is.mergeEt s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.Set.parseField (t: Tag): BParsec (StateM Proto.ExprKind.Set Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Repeated Expr)) t.wireType
      let x: Repeated Expr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Set.mergeElems s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.Record.parseField (t: Tag): BParsec (StateM Proto.ExprKind.Record Unit) := do
  have : Message Expr := { parseField := Expr.parseField, merge := Expr.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType (Array (String × Expr))) t.wireType
      let x: Array (String × Expr) ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.Record.mergeItems s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Proto.ExprKind.parseField (t: Tag): BParsec (StateM Proto.ExprKind Unit) := do
  have : Message Proto.ExprKind.If := { parseField := Proto.ExprKind.If.parseField, merge := Proto.ExprKind.If.merge }
  have : Message Proto.ExprKind.And := { parseField := Proto.ExprKind.And.parseField, merge := Proto.ExprKind.And.merge }
  have : Message Proto.ExprKind.Or := { parseField := Proto.ExprKind.Or.parseField, merge := Proto.ExprKind.Or.merge }
  have : Message Proto.ExprKind.UnaryApp := { parseField := Proto.ExprKind.UnaryApp.parseField, merge := Proto.ExprKind.UnaryApp.merge }
  have : Message Proto.ExprKind.BinaryApp := { parseField := Proto.ExprKind.BinaryApp.parseField, merge := Proto.ExprKind.BinaryApp.merge }
  have : Message Proto.ExprKind.ExtensionFunctionApp := { parseField := Proto.ExprKind.ExtensionFunctionApp.parseField, merge := Proto.ExprKind.ExtensionFunctionApp.merge }
  have : Message Proto.ExprKind.GetAttr := { parseField := Proto.ExprKind.GetAttr.parseField, merge := Proto.ExprKind.GetAttr.merge }
  have : Message Proto.ExprKind.HasAttr := { parseField := Proto.ExprKind.HasAttr.parseField, merge := Proto.ExprKind.HasAttr.merge }
  have : Message Proto.ExprKind.Like := { parseField := Proto.ExprKind.Like.parseField, merge := Proto.ExprKind.Like.merge }
  have : Message Proto.ExprKind.Is := { parseField := Proto.ExprKind.Is.parseField, merge := Proto.ExprKind.Is.merge }
  have : Message Proto.ExprKind.Set := { parseField := Proto.ExprKind.Set.parseField, merge := Proto.ExprKind.Set.merge }
  have : Message Proto.ExprKind.Record := { parseField := Proto.ExprKind.Record.parseField, merge := Proto.ExprKind.Record.merge }


  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Prim) t.wireType
      let x: Prim ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergePrim s x))
    | 2 =>
      (@Field.guardWireType Var) t.wireType
      let x: Var ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeVar s x))
    | 4 =>
      (@Field.guardWireType Proto.ExprKind.If) t.wireType
      let x: Proto.ExprKind.If ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeIf s x))
    | 5 =>
      (@Field.guardWireType Proto.ExprKind.And) t.wireType
      let x: Proto.ExprKind.And ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeAnd s x))
    | 6 =>
      (@Field.guardWireType Proto.ExprKind.Or) t.wireType
      let x: Proto.ExprKind.Or ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeOr s x))
    | 7 =>
      (@Field.guardWireType Proto.ExprKind.UnaryApp) t.wireType
      let x: Proto.ExprKind.UnaryApp ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeUApp s x))
    | 8 =>
      (@Field.guardWireType Proto.ExprKind.BinaryApp) t.wireType
      let x: Proto.ExprKind.BinaryApp ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeBApp s x))
    | 9 =>
      (@Field.guardWireType Proto.ExprKind.ExtensionFunctionApp) t.wireType
      let x: Proto.ExprKind.ExtensionFunctionApp ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeExtApp s x))
    | 10 =>
      (@Field.guardWireType Proto.ExprKind.GetAttr) t.wireType
      let x: Proto.ExprKind.GetAttr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeGetAttr s x))
    | 11 =>
      (@Field.guardWireType Proto.ExprKind.HasAttr) t.wireType
      let x: Proto.ExprKind.HasAttr ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeHasAttr s x))
    | 12 =>
      (@Field.guardWireType Proto.ExprKind.Like) t.wireType
      let x: Proto.ExprKind.Like ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeLike s x))
    | 13 =>
      (@Field.guardWireType Proto.ExprKind.Is) t.wireType
      let x: Proto.ExprKind.Is ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeIs s x))
    | 14 =>
      (@Field.guardWireType Proto.ExprKind.Set) t.wireType
      let x: Proto.ExprKind.Set ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeSet s x))
    | 15 =>
      (@Field.guardWireType Proto.ExprKind.Record) t.wireType
      let x: Proto.ExprKind.Record ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Proto.ExprKind.mergeRecord s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

partial def Expr.parseField (t: Tag): BParsec (StateM Expr Unit) := do
  have : Message Proto.ExprKind := { parseField := Proto.ExprKind.parseField, merge := Proto.ExprKind.merge }
  match t.fieldNum with
    | 1 =>
      (@Field.guardWireType Proto.ExprKind) t.wireType
      let x: Proto.ExprKind ← Field.parse
      pure (modifyGet fun s => Prod.mk () (Expr.mergeExprKind s x))
    | _ =>
      t.wireType.skip
      pure (modifyGet fun s => Prod.mk () s)

end

instance : Message Expr := {
  parseField := Expr.parseField
  merge := Expr.merge
}

end Cedar.Spec
