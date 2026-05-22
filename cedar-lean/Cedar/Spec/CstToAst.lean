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

/- Begin code by Claude -/
/- Check correctness later -/
private def hexDigitToNat? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseUnicodeEscape (cs : List Char) : Option (Char × List Char) := do
  match cs with
  | '{' :: rest =>
    let digits := rest.takeWhile (· ≠ '}')
    let afterBrace := rest.drop digits.length
    match afterBrace with
    | '}' :: remaining =>
      if digits.isEmpty ∨ digits.length > 6 then none else do
      let codepoint ← digits.foldlM (fun acc d => do
        let v ← hexDigitToNat? d
        some (acc * 16 + v)) 0
      if codepoint > 0x10FFFF then none
      else some (Char.ofNat codepoint, remaining)
    | _ => none
  | _ => none

private def unescapeAux (input : List Char) : Option (List Char) :=
  match input with
  | [] => some []
  | '\\' :: 'n'  :: cs => do let tail ← unescapeAux cs; some ('\n' :: tail)
  | '\\' :: 'r'  :: cs => do let tail ← unescapeAux cs; some ('\r' :: tail)
  | '\\' :: 't'  :: cs => do let tail ← unescapeAux cs; some ('\t' :: tail)
  | '\\' :: '0'  :: cs => do let tail ← unescapeAux cs; some ('\x00' :: tail)
  | '\\' :: '\\' :: cs => do let tail ← unescapeAux cs; some ('\\' :: tail)
  | '\\' :: '"'  :: cs => do let tail ← unescapeAux cs; some ('"' :: tail)
  | '\\' :: '\'' :: cs => do let tail ← unescapeAux cs; some ('\'' :: tail)
  | '\\' :: 'u'  :: '{' :: cs =>
    let digits := cs.takeWhile (· ≠ '}')
    let afterBrace := cs.drop digits.length
    match h : afterBrace with
    | '}' :: remaining => do
      if digits.isEmpty ∨ digits.length > 6 then none else do
      let codepoint ← digits.foldlM (fun acc d => do
        let v ← hexDigitToNat? d
        some (acc * 16 + v)) 0
      if codepoint > 0x10FFFF then none
      let tail ← unescapeAux remaining
      some (Char.ofNat codepoint :: tail)
    | _ => none
  | '\\' :: _ => none
  | c :: cs => do
    let tail ← unescapeAux cs
    some (c :: tail)
termination_by input.length
decreasing_by
  all_goals simp_wf
  all_goals (try omega)
  · have h1 : digits.length ≤ cs.length :=
      List.IsPrefix.length_le (List.takeWhile_prefix _)
    have h2 : afterBrace.length = cs.length - digits.length := by
      simp [afterBrace, List.length_drop]
    have h3 : remaining.length + 1 = afterBrace.length := by
      simp [h]
    omega

public def String.unescape? (s : String) : Option String := do
  let chars ← unescapeAux s.toList
  some (String.ofList chars)

/- End code by Claude -/

public def ExprOrSpecial.toExpr? : ExprOrSpecial → Option Expr
  | .expr e => some e
  | .var v => some (.var v)
  | .strLit s => sorry -- unescape the string
  | .boolLit b => some (.lit (.bool b))
  | .name _ => none

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

public def Cst.Unary.toAExpr? (e : Cst.Unary) : Option Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def Cst.MultExpr.toExprOrSpecial? (e : Cst.MultExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let rest ← e.extended.mapM (fun (op, u) => do
      let expr ← u.toAExpr?
      some (op, expr))
    let result ← rest.foldlM (fun acc (op, expr) =>
      match op with
      | .mTimes => some (Expr.binaryApp .mul acc expr)
      | .mDivide => none
      | .mMod => none) first
    some (.expr result)

public def Cst.MultExpr.toAExpr? (e : Cst.MultExpr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def Cst.AddExpr.toExprOrSpecial? (e : Cst.AddExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let rest ← e.extended.mapM (fun (op, u) => do
      let expr ← u.toAExpr?
      some (op, expr))
    let result ← rest.foldlM (fun acc (op, expr) =>
      match op with
      | .aPlus => some (Expr.binaryApp .add acc expr)
      | .aMinus => some (Expr.binaryApp .sub acc expr)
    ) first
    some (.expr result)

public def Cst.AddExpr.toAExpr? (e : Cst.AddExpr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

private def constructExprRel (op : Cst.RelOp) (e₁ e₂ : Expr) : Expr :=
  match op with
  | .rLess => .binaryApp .less e₁ e₂
  | .rLessEq => .binaryApp .lessEq e₁ e₂
  | .rGreaterEq => .unaryApp .not (.binaryApp .less e₁ e₂)
  | .rGreater => .unaryApp .not (.binaryApp .lessEq e₁ e₂)
  | .rNotEq => .unaryApp .not (.binaryApp .eq e₁ e₂)
  | .rEq => .binaryApp .eq e₁ e₂
  | .rIn => .binaryApp .mem e₁ e₂

public def Cst.Relation.toExprOrSpecial? : Cst.Relation → Option ExprOrSpecial
  | .rCommon initial extended =>
    if extended.length > 1 then none else do
    let first ← initial.toExprOrSpecial?
    match extended with
    | [] => some first
    | (op, x) :: tail =>
      let first ← first.toExpr?
      let second ← x.toAExpr?
      some (.expr (constructExprRel op first second))
  | _ => sorry



public def Cst.Expr.toAExpr? (e : Cst.Expr) : Option AExpr :=
  sorry


end
