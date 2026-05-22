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

mutual

-- The Rust implementation handles `Invalid` strings for the `.liStr` case.
-- Not implemented at this stage.
private def Cst.Literal.toAExpr? (l : Cst.Literal) : Option AExpr :=
  match l with
  | .liTrue => some (.lit (.bool true))
  | .liFalse => some (.lit (.bool false))
  | .liNum n => do
    let i ← Int64.ofInt? (n.toNat)
    some (.lit (.int i))
  | .liStr s => some (.lit (.string s))

private def Cst.Name.toAName? (n : Cst.Name) : Option AName := do
  let id ← n.name.toUnreservedString?
  let path ← n.path.mapM (Cst.Ident.toUnreservedString?)
  some {id := id, path := path}

private def Cst.Ref.toAExpr? (r : Cst.Ref) : Option AExpr :=
  match r with
  -- Unescape `eid` not done
  | .uid path eid => do
    let ty ← path.toAName?
    match eid with
    | .string s => some (.lit (.entityUID {ty := ty, eid := s}))
  | .ref _ _ => none

private def Cst.Name.toAExpr? (n : Name) : Option AExpr :=
  if !n.path.isEmpty then none
  else match n.name with
    | .idPrincipal => some (.var .principal)
    | .idAction => some (.var .action)
    | .idResource => some (.var .resource)
    | .idContext => some (.var .context)
    | _ => none

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

public def Cst.Primary.toAExpr? (e : Cst.Primary) : Option AExpr :=
  match e with
  | .literal l => l.toAExpr?
  | .ref r => r.toAExpr?
  | .name n => n.toAExpr?
  | .expr e => e.toAExpr?
  | .eList es => do
    let aes ← es.mapM (Cst.Expr.toAExpr?)
    some (.set aes)



public def Cst.Expr.toAExpr? (e : Cst.Expr) : Option AExpr :=
  sorry


end
