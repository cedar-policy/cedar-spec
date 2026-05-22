module

public import Cedar.Spec.Cst
public import Cedar.Spec.Expr
public import Cedar.Spec.Policy
public import Cedar.Spec.Value

namespace Cedar.Spec

public abbrev CExpr := Cedar.Spec.Cst.Expr
public abbrev AExpr := Cedar.Spec.Expr
public abbrev CName := Cedar.Spec.Cst.Name
public abbrev AName := Cedar.Spec.Name

public inductive ExprOrSpecial where
  -- Any expression except a variable, name, string literal, or bool literal
  | expr (e : Expr)
  -- Variables, which act as expressions or names
  | var (v : Var)
  -- Name that isn't an expr and couldn't be converted to var
  | name (n : Name)
  -- String literal, not yet unescaped
  | strLit (lit : String)
  -- A boolean literal
  | boolLit (v : Bool)

private def Cst.Ident.toUnreservedString? : Cst.Ident → Option String
  | .idPrincipal => some "principal"
  | .idAction => some "action"
  | .idResource => some "resource"
  | .idContext => some "context"
  | .idPermit => some "permit"
  | .idForbid => some "forbid"
  | .idWhen => some "when"
  | .idUnless => some "unless"
  | .idIdent s => some s
  | _ => none

private def Cst.Ident.toString : Cst.Ident → String
  | .idPrincipal => "principal"
  | .idAction => "action"
  | .idResource => "resource"
  | .idContext => "context"
  | .idTrue => "true"
  | .idFalse => "false"
  | .idPermit => "permit"
  | .idForbid => "forbid"
  | .idWhen => "when"
  | .idUnless => "unless"
  | .idIn => "in"
  | .idHas => "has"
  | .idLike => "like"
  | .idIs => "is"
  | .idIf => "if"
  | .idThen => "then"
  | .idElse => "else"
  | .idIdent s => s

public inductive AstAccessor where
  | field (id : Cst.Ident)
  -- | Call (args : List Expr)
  | index (s : String)

public def AstAccessor.toString : AstAccessor → String
  | .field id => id.toString
  | .index s => s

public def ExprOrSpecial.toExpr? : ExprOrSpecial → Option Expr
  | .expr e => some e
  | .var v => some (.var v)
  | .strLit s => sorry -- unescape the string
  | .boolLit b => some (.lit (.bool b))
  | .name _ => none


#eval (fun (n : UInt64) => - n.toInt64) 32
#eval Int64.MAX+1
#eval Int64.MIN


mutual

private def Cst.Literal.toExprOrSpecial? (l : Cst.Literal) : Option ExprOrSpecial :=
  match l with
  | .liTrue => some (.boolLit true)
  | .liFalse => some (.boolLit false)
  | .liNum n => do
    let i ← Int64.ofInt? (n.toNat)
    some (.expr (.lit (.int i)))
  | .liStr s => some (.strLit s)

private def Cst.Name.toAName? (n : Cst.Name) : Option AName := do
  let id ← n.name.toUnreservedString?
  let path ← n.path.mapM (Cst.Ident.toUnreservedString?)
  some {id := id, path := path}

private def Cst.Name.toVar? (n : Cst.Name) : Option Var :=
  if !n.path.isEmpty then none
  else match n.name with
    | .idPrincipal => some .principal
    | .idAction => some .action
    | .idResource => some .resource
    | .idContext => some .context
    | _ => none

private def Cst.Ref.toExprOrSpecial? (r : Cst.Ref) : Option ExprOrSpecial :=
  match r with
  -- Unescape `eid` not done
  | .uid path eid => do
    let ty ← path.toAName?
    match eid with
    | .string s => some (.expr (.lit (.entityUID {ty := ty, eid := s})))
  | .ref _ _ => none

public def Cst.Primary.toExprOrSpecial? (e : Cst.Primary) : Option ExprOrSpecial :=
  match e with
  | .literal l => l.toExprOrSpecial?
  | .ref r => r.toExprOrSpecial?
  | .name n => match n.toVar? with
    | some v => some (.var v)
    | none => do
      let an ← n.toAName?
      some (.name an)
  | .expr e => do
    let ae ← e.toAExpr?
    some (.expr ae)
  | .eList es => do
    let aes ← es.mapM (Cst.Expr.toAExpr?)
    some (.expr (.set aes))

private def Cst.Expr.toStringLiteral? : Cst.Expr → Option String
  | .expr e => match e.expr with
    | .edIf _ _ _ => none
    | .edOr e => match e.initial.initial with
      | .rHas _ _ => none
      | .rLike _ _ => none
      | .rCommon i _ => match i.initial.initial.item.item with
        | .literal l => match l with
          | .liStr s => some s
          | _ => none
        | _ => none

private def Cst.MemAccess.toAstAccessor? (m : Cst.MemAccess) : Option AstAccessor :=
  match m with
  | .field i => match i with
    | .idIdent _ => some (.field i)
    | _ => none
  | .index e => do
    let s ← e.toStringLiteral?
    some (.index s)

private def memberAux :  ExprOrSpecial → List AstAccessor → Option ExprOrSpecial
  | prim, [] => prim
  | .expr e, hd :: tl => memberAux (.expr (.getAttr e hd.toString)) tl
  | prim@(.strLit s), hd :: tl => do
    let ret ← prim.toExpr?
    memberAux (.expr (.getAttr ret hd.toString)) tl
  | prim@(.boolLit s), hd :: tl => do
    let ret ← prim.toExpr?
    memberAux (.expr (.getAttr ret hd.toString)) tl
  | prim@(.var v), hd@(.field id) :: tl =>
    memberAux (.expr (.getAttr (.var v) id.toString)) tl
  | prim@(.var v), hd@(.index id) :: tl =>
    memberAux (.expr (.getAttr (.var v) id)) tl
  | prim@(.name n), hd@(.field _) :: tl => none
  | prim@(.name n), hd@(.index _) :: tl => none

public def Cst.Member.toExprOrSpecial? (e : Cst.Member) : Option ExprOrSpecial := do
  let prim ← e.item.toExprOrSpecial?
  let accessors ← e.access.mapM (Cst.MemAccess.toAstAccessor?)
  memberAux prim accessors

private def Expr.bangN (e : Expr) (n : Nat) : Expr :=
  if n == 0 then e else (Expr.unaryApp .not e).bangN (n-1)
  termination_by n
  decreasing_by rename_i h; simp at h; omega

private def Expr.dashN (e : Expr) (n : Nat) : Expr :=
  if n == 0 then e else (Expr.unaryApp .neg e).dashN (n-1)
  termination_by n
  decreasing_by rename_i h; simp at h; omega

private def Cst.Member.toLit? (e : Cst.Member) : Option Cst.Literal :=
  if !e.access.isEmpty then none else
  match e.item with
  | .literal l => some l
  | _ => none

public def Cst.Unary.toExprOrSpecial? (e : Cst.Unary) : Option ExprOrSpecial :=
  match e.op with
  | none => e.item.toExprOrSpecial?
  | some (.nDash 0) => e.item.toExprOrSpecial?
  | some (.nBang n) => do
    let eos ← e.item.toExprOrSpecial?
    let expr ← eos.toExpr?
    some (.expr (expr.bangN (n.toNat)))
  | some (.nDash n) =>
    match e.item.toLit? with
    | some (.liNum x) =>
      let y := (Int64.ofUInt64 x)
      match compare y (Int64.MAX+1).toInt64 with
      | .eq => some (.expr ((Expr.lit (.int (Int64.MIN).toInt64)).dashN (n-1).toNat))
      | .lt => some (.expr ((Expr.lit (.int (-y))).dashN (n-1).toNat))
      | .gt => none
    | _ => do
      let eos ← e.item.toExprOrSpecial?
      let expr ← eos.toExpr?
      some (ExprOrSpecial.expr (expr.dashN n.toNat))
  | some .nOverBang | some .nOverDash => none

public def Cst.Unary.toExpr? (e : Cst.Unary) : Option Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?


public def Cst.Expr.toAExpr? (e : Cst.Expr) : Option AExpr :=
  sorry


end
