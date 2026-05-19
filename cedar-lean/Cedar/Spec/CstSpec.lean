module

public import Cedar.Spec.Cst
public import Cedar.Spec.Entities
public import Cedar.Spec.Request
public import Cedar.Spec.Response
public import Cedar.Spec.Value

namespace Cedar.Spec.Cst


-- The layers of Expr in the CST
-- Expr → ExprImpl → ExprData → OrExpr → AndExpr → Relation
-- → AddExpr → MultExpr → Unary → Member → Primary

/- Lifting helpers -/

public def Expr.toPrimary (e : Expr) : Primary :=
  .expr e

public def Primary.toMember (p : Primary) : Member :=
  {item := p, access := []}

public def Member.toUnary (m : Member) : Unary :=
  {op := .nBang 0, item := m}

public def Unary.toMultExpr (u : Unary) : MultExpr :=
  {initial := u, extended := []}

public def MultExpr.toAddExpr (m : MultExpr) : AddExpr :=
  {initial := m, extended := []}

public def AddExpr.toRelation (a : AddExpr) : Relation :=
  .rCommon a []

public def Relation.toAndExpr (r : Relation) : AndExpr :=
  {initial := r, extended := []}

public def AndExpr.toOrExpr (a : AndExpr) : OrExpr :=
  {initial := a, extended := []}

public def OrExpr.toExpr (o : OrExpr) : Expr :=
  .expr {expr := .edOr o}

public def Expr.lift (e : Expr) : Expr :=
  e.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

/- Constants and Combinators on Expr -/

public def Expr.tt : Expr :=
  (Primary.literal Literal.liTrue).toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

public def Expr.ff : Expr :=
  (Primary.literal Literal.liFalse).toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

public def Expr.not (e : Expr) : Expr :=
  let e' : Unary := {op := NegOp.nBang 1, item := e.toPrimary.toMember}
  e'.toMultExpr.toAddExpr.toRelation.toAndExpr.toOrExpr.toExpr

public def Expr.and (e1 e2 : Expr) : Expr :=
  let e1' := e1.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation
  let e2' := e2.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation
  let e' : AndExpr := {initial := e1', extended := [e2']}
  e'.toOrExpr.toExpr

public def Expr.or (e1 e2 : Expr) : Expr :=
  let e1' := e1.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr
  let e2' := e2.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation.toAndExpr
  let e' : OrExpr := {initial := e1', extended := [e2']}
  e'.toExpr

public def Expr.toRelation (e : Expr) : Relation :=
  e.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation

public def Expr.foldAnd : List Expr → Expr
  | []      => Expr.tt
  | [e]     => e
  | e :: es =>
    let e'  := e.toRelation
    let es' := es.map Expr.toRelation
    let a   : AndExpr := { initial := e', extended := es' }
    a.toOrExpr.toExpr
