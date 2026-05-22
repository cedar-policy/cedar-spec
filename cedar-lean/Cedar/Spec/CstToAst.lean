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


public def Cst.Expr.toAExpr? (e : Cst.Expr) : Option AExpr :=
  sorry


end
