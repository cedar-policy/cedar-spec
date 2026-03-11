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

import Cedar.Spec.CST.Expr

/-! This file defines the CST-to-AST translation functions. -/

namespace Cedar.Spec.CST

open Cedar.Spec

/-- Translate a CST relational operator application to AST -/
def translateRel (op : RelOp) (lhs rhs : Spec.Expr) : Spec.Expr :=
  match op with
  | .eq        => .binaryApp .eq lhs rhs
  | .notEq     => .unaryApp .not (.binaryApp .eq lhs rhs)
  | .less      => .binaryApp .less lhs rhs
  | .lessEq    => .binaryApp .lessEq lhs rhs
  | .greater   => .unaryApp .not (.binaryApp .lessEq lhs rhs)
  | .greaterEq => .unaryApp .not (.binaryApp .less lhs rhs)
  | .mem       => .binaryApp .mem lhs rhs

/-- Left-fold a list into a binary Or chain -/
def foldOr (init : Spec.Expr) : List Spec.Expr → Spec.Expr
  | []      => init
  | e :: es => foldOr (.or init e) es

/-- Left-fold a list into a binary And chain -/
def foldAnd (init : Spec.Expr) : List Spec.Expr → Spec.Expr
  | []      => init
  | e :: es => foldAnd (.and init e) es

/-- Left-fold addition/subtraction -/
def foldAdd (init : Spec.Expr) : List (AddOp × Spec.Expr) → Spec.Expr
  | []                    => init
  | (.plus, e) :: rest    => foldAdd (.binaryApp .add init e) rest
  | (.minus, e) :: rest   => foldAdd (.binaryApp .sub init e) rest

/-- Left-fold multiplication -/
def foldMult (init : Spec.Expr) : List Spec.Expr → Spec.Expr
  | []      => init
  | e :: es => foldMult (.binaryApp .mul init e) es

/-- Translate extended has: e has a.b.c → (e has a) && (e.a has b) && (e.a.b has c) -/
def translateExtendedHas (base : Spec.Expr) : List Attr → Spec.Expr
  | []      => .lit (.bool true)
  | [a]     => .hasAttr base a
  | a :: as => .and (.hasAttr base a) (translateExtendedHas (.getAttr base a) as)

/-- Apply a list of unary ops (outermost first) -/
def applyUnaryOps : List UnaryOp → Spec.Expr → Spec.Expr
  | [],            e => e
  | .not :: ops,   e => .unaryApp .not (applyUnaryOps ops e)
  | .neg :: ops,   e => .unaryApp .neg (applyUnaryOps ops e)

/-- Main translation: CST.Expr → Spec.Expr (AST) -/
def Expr.toExpr : CST.Expr → Spec.Expr
  | .lit p           => .lit p
  | .var v           => .var v
  | .ite c t e       => .ite (c.toExpr) (t.toExpr) (e.toExpr)
  | .or init ext     => foldOr (init.toExpr) (ext.map₁ (fun ⟨e, _⟩ => e.toExpr))
  | .and init ext    => foldAnd (init.toExpr) (ext.map₁ (fun ⟨e, _⟩ => e.toExpr))
  | .rel op l r      => translateRel op (l.toExpr) (r.toExpr)
  | .has e a         => .hasAttr (e.toExpr) a
  | .extendedHas e as => translateExtendedHas (e.toExpr) as
  | .like e p        => .unaryApp (.like p) (e.toExpr)
  | .is e ety        => .unaryApp (.is ety) (e.toExpr)
  | .isIn e ety inE  => .and (.unaryApp (.is ety) (e.toExpr))
                              (.binaryApp .mem (e.toExpr) (inE.toExpr))
  | .add init ext    => foldAdd (init.toExpr) (ext.map₂ (fun ⟨(op, e), _⟩ => (op, e.toExpr)))
  | .mult init ext   => foldMult (init.toExpr) (ext.map₁ (fun ⟨e, _⟩ => e.toExpr))
  | .unary ops e     => applyUnaryOps ops (e.toExpr)
  | .getAttr e a     => .getAttr (e.toExpr) a
  | .hasAttr e a     => .hasAttr (e.toExpr) a
  | .set es          => .set (es.map₁ (fun ⟨e, _⟩ => e.toExpr))
  | .record ps       => .record (ps.map₂ (fun ⟨(a, e), _⟩ => (a, e.toExpr)))
  | .call fn args    => .call fn (args.map₁ (fun ⟨e, _⟩ => e.toExpr))
  | .methodCall recv fn args => .call fn (recv.toExpr :: args.map₁ (fun ⟨e, _⟩ => e.toExpr))
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals
    rename_i h
    try replace h := List.sizeOf_lt_of_mem h
    try simp at h
    omega

/-- Translate a CST condition to an AST condition -/
def Condition.toCondition (c : CST.Condition) : Spec.Condition :=
  { kind := c.kind, body := c.body.toExpr }

/-- Translate a CST policy to an AST policy -/
def Policy.toPolicy (p : CST.Policy) : Spec.Policy :=
  { id := p.id,
    effect := p.effect,
    principalScope := p.principalScope,
    actionScope := p.actionScope,
    resourceScope := p.resourceScope,
    condition := p.conditions.map Condition.toCondition }

end Cedar.Spec.CST
