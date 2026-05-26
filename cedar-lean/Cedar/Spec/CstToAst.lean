module

public import Cedar.Spec.Cst
public import Cedar.Spec.Expr
public import Cedar.Spec.Policy
public import Cedar.Spec.Value

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

private def String.toUnreservedId? (s : String) : Option String :=
  match s with
  | "principal" | "action" | "resource" | "context"
  | "true" | "false" | "permit" | "forbid"
  | "when" | "unless" | "in" | "has" | "like" | "is"
  | "if" | "then" | "else" => none
  | _ => some s

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

private def Cst.Ident.toUnreservedId? : Cst.Ident → Option String
  | .idIdent s => some s
  | _ => none

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

private def Var.toString : Var → String
  | .principal => "principal"
  | .action => "action"
  | .resource => "resource"
  | .context => "context"

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
  | .strLit s => do
      let unescapted ← s.unescape?
      some (.lit (.string unescapted))
  | .boolLit b => some (.lit (.bool b))
  | .name _ => none

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

private def constructExprRel (op : Cst.RelOp) (e₁ e₂ : Expr) : Expr :=
  match op with
  | .rLess => .binaryApp .less e₁ e₂
  | .rLessEq => .binaryApp .lessEq e₁ e₂
  | .rGreaterEq => .unaryApp .not (.binaryApp .less e₁ e₂)
  | .rGreater => .unaryApp .not (.binaryApp .lessEq e₁ e₂)
  | .rNotEq => .unaryApp .not (.binaryApp .eq e₁ e₂)
  | .rEq => .binaryApp .eq e₁ e₂
  | .rIn => .binaryApp .mem e₁ e₂

private def constructAttrsAux? : List Cst.MemAccess → Option (List String)
  | [] => some []
  | .field id :: rest => do
    let head ← id.toUnreservedId?
    let tail ← constructAttrsAux? rest
    head :: tail
  | .index e :: rest => none

-- `first` should already be verified to be unreserved
-- Verify all elements in `rest` are unreserved
private def constructAttrs? (first : String) (rest : List Cst.MemAccess) : Option (List String) := do
  let tail ← constructAttrsAux? rest
  some (first :: tail)

private def extendedHasAttr (target : Expr) (fields : List String) : Expr :=
  match fields with
  | [] => target
  | [f] => .hasAttr target f
  | f :: rest =>
    .and (.hasAttr target f) (extendedHasAttr (.getAttr target f) rest)

-- Begin code by Claude
private def toPatternAux (input : List Char) : Option Pattern :=
  match input with
  | [] => some []
  | '\\' :: '*'  :: cs => do let tail ← toPatternAux cs; some (.justChar '*' :: tail)
  | '\\' :: '\\' :: cs => do let tail ← toPatternAux cs; some (.justChar '\\' :: tail)
  | '\\' :: 'n'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\n' :: tail)
  | '\\' :: 'r'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\r' :: tail)
  | '\\' :: 't'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\t' :: tail)
  | '\\' :: '0'  :: cs => do let tail ← toPatternAux cs; some (.justChar '\x00' :: tail)
  | '\\' :: '"'  :: cs => do let tail ← toPatternAux cs; some (.justChar '"' :: tail)
  | '\\' :: '\'' :: cs => do let tail ← toPatternAux cs; some (.justChar '\'' :: tail)
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
      let tail ← toPatternAux remaining
      some (.justChar (Char.ofNat codepoint) :: tail)
    | _ => none
  | '\\' :: _ => none
  | '*' :: cs => do let tail ← toPatternAux cs; some (.star :: tail)
  | c :: cs => do let tail ← toPatternAux cs; some (.justChar c :: tail)
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

private def String.toPattern? (s : String) : Option Pattern :=
  toPatternAux s.toList
-- End code by Claude

mutual

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
    let aes ← es.mapM₁ (fun ⟨x, _⟩ => x.toAExpr?)
    some (.expr (.set aes))
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (rename_i h; have := List.sizeOf_lt_of_mem h; omega)

public def Cst.Member.toExprOrSpecial? (e : Cst.Member) : Option ExprOrSpecial := do
  let prim ← e.item.toExprOrSpecial?
  let accessors ← e.access.mapM (Cst.MemAccess.toAstAccessor?)
  memberAux prim accessors
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.Member.mk.sizeOf_spec]; omega)

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
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.Unary.mk.sizeOf_spec]; omega)

public def Cst.Unary.toAExpr? (e : Cst.Unary) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

private def Cst.MultExpr.foldExtended (acc : AExpr) (xs : List (Cst.MultOp × Cst.Unary)) : Option AExpr :=
  match xs with
  | [] => some acc
  | (op, u) :: rest => do
    let aval ← u.toAExpr?
    match op with
    | .mTimes => Cst.MultExpr.foldExtended (Cedar.Spec.Expr.binaryApp .mul acc aval) rest
    | _ => none
termination_by (sizeOf xs, 0)

public def Cst.MultExpr.toExprOrSpecial? (e : Cst.MultExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← Cst.MultExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.MultExpr.mk.sizeOf_spec]; omega)

public def Cst.MultExpr.toAExpr? (e : Cst.MultExpr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

private def Cst.AddExpr.foldExtended (acc : AExpr) (xs : List (Cst.AddOp × Cst.MultExpr)) : Option AExpr :=
  match xs with
  | [] => some acc
  | (op, m) :: rest => do
    let aval ← m.toAExpr?
    match op with
    | .aPlus  => Cst.AddExpr.foldExtended (Cedar.Spec.Expr.binaryApp .add acc aval) rest
    | .aMinus => Cst.AddExpr.foldExtended (Cedar.Spec.Expr.binaryApp .sub acc aval) rest
termination_by (sizeOf xs, 0)

public def Cst.AddExpr.toExprOrSpecial? (e : Cst.AddExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← Cst.AddExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.AddExpr.mk.sizeOf_spec]; omega)

public def Cst.AddExpr.toAExpr? (e : Cst.AddExpr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

-- In Rust, `to_has_rhs` has the output type `Option (String ⊕ UnreservedId)`.
-- `UnservedId` is essentially a string, but passed the check that it's not
-- a reserved keyword. In this implementation, we keep the output type `String`
-- and return a `none` if it is reserved.
private def Cst.AddExpr.toHasRhs? (e : Cst.AddExpr) : Option (String ⊕ List String) := do
  if (!e.extended.isEmpty) || (!e.initial.extended.isEmpty) || (!e.initial.initial.op.isNone) then none else
  let member := e.initial.initial.item
  match member.item with
  | .literal _ | .name _ =>
    let item ← member.item.toExprOrSpecial?
    match item, member.access with
    | .strLit lit, [] => lit.unescape?.map .inl
    | .var v, rest => (constructAttrs? (v.toString) rest).map .inr
    | .name n, rest => if !n.path.isEmpty then none else
      let first ← n.id.toUnreservedId?
      (constructAttrs? first rest).map .inr
    | _, _ => none
  | _ => none
termination_by (sizeOf e, 2)
decreasing_by
  all_goals
    have h1 : sizeOf e.initial.initial.item.item < sizeOf e := by
      rcases e with ⟨⟨⟨_, m⟩, _⟩, _⟩
      rcases m with ⟨_, _⟩
      simp only [Cst.AddExpr.mk.sizeOf_spec, Cst.MultExpr.mk.sizeOf_spec,
        Cst.Unary.mk.sizeOf_spec, Cst.Member.mk.sizeOf_spec]
      omega
    omega

private def Cst.AddExpr.toPattern? (e : Cst.AddExpr) : Option Pattern := do
  let eos ← e.toExprOrSpecial?
  match eos with
  | .strLit lit => String.toPattern? lit
  | _ => none
termination_by (sizeOf e, 2)

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
  | .rHas target field => do
    let maybe_target ← target.toAExpr?
    let maybe_fields ← field.toHasRhs?
    match maybe_fields with
    | .inl f => some (.expr (.hasAttr maybe_target f))
    | .inr fs => some (.expr (extendedHasAttr maybe_target fs))
  | .rLike target pattern => do
    let maybe_target ← target.toAExpr?
    let maybe_pattern ← pattern.toPattern?
    some (.expr (.unaryApp (.like maybe_pattern) maybe_target))
termination_by e => (sizeOf e, 0)

public def Cst.Relation.toAExpr? (e : Cst.Relation) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

private def Cst.AndExpr.foldExtended (acc : AExpr) (xs : List Cst.Relation) : Option AExpr :=
  match xs with
  | [] => some acc
  | rel :: rest => do
    let aval ← rel.toAExpr?
    Cst.AndExpr.foldExtended (Cedar.Spec.Expr.and acc aval) rest
termination_by (sizeOf xs, 0)

public def Cst.AndExpr.toExprOrSpecial? (e : Cst.AndExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← Cst.AndExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.AndExpr.mk.sizeOf_spec]; omega)

public def Cst.AndExpr.toAExpr? (e : Cst.AndExpr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

private def Cst.OrExpr.foldExtended (acc : AExpr) (xs : List Cst.AndExpr) : Option AExpr :=
  match xs with
  | [] => some acc
  | ande :: rest => do
    let aval ← ande.toAExpr?
    Cst.OrExpr.foldExtended (Cedar.Spec.Expr.or acc aval) rest
termination_by (sizeOf xs, 0)

public def Cst.OrExpr.toExprOrSpecial? (e : Cst.OrExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← Cst.OrExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.OrExpr.mk.sizeOf_spec]; omega)

public def Cst.OrExpr.toAExpr? (e : Cst.OrExpr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def Cst.ExprData.toExprOrSpecial? : Cst.ExprData → Option ExprOrSpecial
  | .edOr ore => ore.toExprOrSpecial?
  | .edIf i t e => do
    let maybe_guard ← i.toAExpr?
    let maybe_then ← t.toAExpr?
    let maybe_else ← e.toAExpr?
    some (.expr (.ite maybe_guard maybe_then maybe_else))
termination_by e => (sizeOf e, 0)

public def Cst.ExprData.toAExpr? (e : Cst.ExprData) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def Cst.ExprImpl.toExprOrSpecial? (e : Cst.ExprImpl) : Option ExprOrSpecial :=
  e.expr.toExprOrSpecial?
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.ExprImpl.mk.sizeOf_spec]; omega)

public def Cst.ExprImpl.toAExpr? (e : Cst.ExprImpl) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def Cst.Expr.toExprOrSpecial? : Cst.Expr → Option ExprOrSpecial
  | .expr impl => impl.toExprOrSpecial?
termination_by e => (sizeOf e, 0)

public def Cst.Expr.toAExpr? (e : Cst.Expr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

end
