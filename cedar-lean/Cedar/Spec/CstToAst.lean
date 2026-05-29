module

public import Cedar.Spec.Cst
public import Cedar.Spec.Expr
public import Cedar.Spec.Policy
public import Cedar.Spec.Value

private def String.toUnreservedId? (s : String) : Option String :=
  match s with
  | "principal" | "action" | "resource" | "context"
  | "true" | "false" | "permit" | "forbid"
  | "when" | "unless" | "in" | "has" | "like" | "is"
  | "if" | "then" | "else" | "__cedar" => none
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

public def Unreserved? (s : String) : Bool :=
  match s with
  | "principal" => false
  | "action" => false
  | "resource" => false
  | "context" => false
  | "true" => false
  | "false" => false
  | "permit" => false
  | "forbid" => false
  | "when" => false
  | "unless" => false
  | "in" => false
  | "has" => false
  | "like" => false
  | "is" => false
  | "if" => false
  | "then" => false
  | "else" => false
  | "__cedar" => false
  | _ => true

private def Cst.Ident.toUnreservedId? : Cst.Ident → Option String
  | .idIdent s => if Unreserved? s then some s else none
  | _ => none

public def Cst.Ident.toUnreservedString? : Cst.Ident → Option String
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
  | .field id => CstCommon.Ident.toString id
  | .index s => s

public def ExprOrSpecial.toExpr? : ExprOrSpecial → Option Expr
  | .expr e => some e
  | .var v => some (.var v)
  | .strLit s => do
      let unescaped ← Cedar.Spec.CstCommon.unescape? s
      some (.lit (.string unescaped))
  | .boolLit b => some (.lit (.bool b))
  | .name _ => none

public def Cst.Literal.toExprOrSpecial? (l : Cst.Literal) : Option ExprOrSpecial :=
  match l with
  | .liTrue => some (.boolLit true)
  | .liFalse => some (.boolLit false)
  | .liNum n => do
    let i ← Int64.ofInt? (n.toNat)
    some (.expr (.lit (.int i)))
  | .liStr s => some (.strLit s)

public def Cst.Name.toAName? (n : Cst.Name) : Option AName := do
  let id ← n.name.toUnreservedString?
  let path ← n.path.mapM (Cst.Ident.toUnreservedString?)
  some {id := id, path := path}

public def Cst.Name.toVar? (n : Cst.Name) : Option Var :=
  if !n.path.isEmpty then none
  else match n.name with
    | .idPrincipal => some .principal
    | .idAction => some .action
    | .idResource => some .resource
    | .idContext => some .context
    | _ => none

public def Cst.Ref.toExprOrSpecial? (r : Cst.Ref) : Option ExprOrSpecial :=
  match r with
  | .uid path eid => do
    let ty ← path.toAName?
    match eid with
    | .string s => do
      let unescaped ← Cedar.Spec.CstCommon.unescape? s
      some (.expr (.lit (.entityUID {ty := ty, eid := unescaped})))
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

public def Cst.MemAccess.toAstAccessor? (m : Cst.MemAccess) : Option AstAccessor :=
  match m with
  | .field i => match i with
    | .idIdent _ => some (.field i)
    | _ => none
  | .index e => do
    let s ← e.toStringLiteral?
    let s ← Cedar.Spec.CstCommon.unescape? s
    some (.index s)

public def memberAux :  ExprOrSpecial → List AstAccessor → Option ExprOrSpecial
  | prim, [] => prim
  | .expr e, hd :: tl => memberAux (.expr (.getAttr e hd.toString)) tl
  | prim@(.strLit _), hd :: tl => do
    let ret ← prim.toExpr?
    memberAux (.expr (.getAttr ret hd.toString)) tl
  | prim@(.boolLit _), hd :: tl => do
    let ret ← prim.toExpr?
    memberAux (.expr (.getAttr ret hd.toString)) tl
  | (.var v), (.field id) :: tl =>
    memberAux (.expr (.getAttr (.var v) (CstCommon.Ident.toString id))) tl
  | (.var v), (.index id) :: tl =>
    memberAux (.expr (.getAttr (.var v) id)) tl
  | (.name _), (.field _) :: _ => none
  | (.name _), (.index _) :: _ => none

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
  | .index _ :: _ => none

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

public def Cst.Primary.toAExpr? (e : Cst.Primary) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

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
      let xNat := x.toNat
      let minMagnitude := (Int64.MAX + 1).toNat
      match compare xNat minMagnitude with
      | .eq => some (.expr ((Expr.lit (.int (Int64.MIN).toInt64)).dashN (n-1).toNat))
      | .lt =>
        match Int64.ofInt? (Int.ofNat xNat) with
        | some y => some (.expr ((Expr.lit (.int (-y))).dashN (n-1).toNat))
        | none => none
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
-- "__cedar". In this implementation, we keep the output type `String`
-- and return a `none` if it is reserved.
private def Cst.AddExpr.toHasRhs? (e : Cst.AddExpr) : Option (String ⊕ List String) := do
  if (!e.extended.isEmpty) || (!e.initial.extended.isEmpty) || (!e.initial.initial.op.isNone) then none else
  let member := e.initial.initial.item
  match member.item with
  | .literal _ | .name _ =>
    let item ← member.item.toExprOrSpecial?
    match item, member.access with
    | .strLit lit, [] => (Cedar.Spec.CstCommon.unescape? lit).map .inl
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
  | .strLit lit => Cedar.Spec.CstCommon.toPattern? lit
  | _ => none
termination_by (sizeOf e, 2)

public def Cst.Relation.toExprOrSpecial? : Cst.Relation → Option ExprOrSpecial
  | .rCommon initial extended =>
    if extended.length > 1 then none else do
    let first ← initial.toExprOrSpecial?
    match extended with
    | [] => some first
    | (op, x) :: _ =>
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

public def Cst.ExprImpl.toExprOrSpecial? (e : Cst.ExprImpl) : Option ExprOrSpecial :=
  e.expr.toExprOrSpecial?
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Cst.ExprImpl.mk.sizeOf_spec]; omega)

public def Cst.ExprImpl.toAExpr? (e : Cst.ExprImpl) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def Cst.Expr.toExprOrSpecial? : Cst.Expr → Option ExprOrSpecial
  | .expr impl => impl.toExprOrSpecial?
termination_by e => (sizeOf e, 0)

public def Cst.Expr.toAExpr? (e : Cst.Expr) : Option AExpr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

end

private def Cst.Ident.toConditionKind? : Cst.Ident →  Option ConditionKind
  | .idWhen => some .when
  | .idUnless => some .unless
  | _ => none

public def Cst.Cond.toCondition? (cond : Cst.Cond) : Option Condition := do
  let kind ← cond.cond.toConditionKind?
  let body ← cond.expr.bind (Cst.Expr.toAExpr?)
  some {kind := kind, body := body}

public def toConditions? (conds : List Cst.Cond) : Option Conditions := do
  conds.mapM (·.toCondition?)

private def Cst.Ident.toVar? : Cst.Ident → Option Var
  | .idPrincipal => some .principal
  | .idAction => some .action
  | .idResource => some .resource
  | .idContext => some .context
  | _ => none

private def Cst.Ident.toEffect? : Cst.Ident → Option Effect
  | .idPermit => some .permit
  | .idForbid => some .forbid
  | _ => none

private def Cst.AddExpr.toEntityType? (e : Cst.AddExpr) : Option EntityType := do
  let eos ← e.toExprOrSpecial?
  match eos with
  | .name n => some n
  | .var  _ => none --  in Rust unqualified name
  | _ => none

-- Helper lemma: a `Primary` reachable through the AddExpr→Primary chain
-- has strictly smaller `sizeOf` than the surrounding `OrExpr`.
private theorem sizeOf_addExpr_primary_lt_orExpr (o : Cst.OrExpr) (ae : Cst.AddExpr) (ext : List (Cst.RelOp × Cst.AddExpr))
    (h : o.initial.initial = .rCommon ae ext) :
    sizeOf ae.initial.initial.item.item < sizeOf o := by
  -- ae.initial : MultExpr ⟨Unary, List _⟩
  -- ae.initial.initial : Unary ⟨Option NegOp, Member⟩
  -- ae.initial.initial.item : Member ⟨Primary, List MemAccess⟩
  -- ae.initial.initial.item.item : Primary
  obtain ⟨ae_mult, ae_ext⟩ := ae
  obtain ⟨ae_unary, ae_mult_ext⟩ := ae_mult
  obtain ⟨ae_op, ae_member⟩ := ae_unary
  obtain ⟨ae_prim, ae_access⟩ := ae_member
  obtain ⟨o_and, o_ext⟩ := o
  obtain ⟨o_rel, o_and_ext⟩ := o_and
  simp_all
  omega

mutual

private def Cst.Primary.toMultipleEntityUID? (p : Cst.Primary) : Option (EntityUID ⊕ List EntityUID) :=
  match p with
  | .literal _ | .name _ => none
  | .ref r => match r with
    | .uid path (.string s) => do
      let maybe_path ← path.toAName?
      let maybe_eid ← Cedar.Spec.CstCommon.unescape? s
      some (.inl {ty := maybe_path, eid := maybe_eid})
    | .ref _ _ => none
  | .expr e => e.toMultipleEntityUID?
  | .eList es => do
    let uids ← es.attach.mapM (fun ⟨x, hmem⟩ =>
      have : sizeOf x < sizeOf es := List.sizeOf_lt_of_mem hmem
      x.toMultipleEntityUID?)
    some (.inr (uids.flatMap (Sum.elim ([·]) id)))
termination_by (sizeOf p, 0)
decreasing_by
  all_goals (simp_wf; omega)

private def Cst.Expr.toMultipleEntityUID? (e : Cst.Expr) : Option (EntityUID ⊕ List EntityUID) :=
  match e with
  | .expr ⟨.edIf _ _ _⟩ => none
  | .expr ⟨.edOr o⟩ =>
    if !o.extended.isEmpty || !o.initial.extended.isEmpty then none
    else
      match h : o.initial.initial with
      | .rHas _ _ | .rLike _ _ => none
      | .rCommon ae ext =>
        if !ext.isEmpty || !ae.extended.isEmpty || !ae.initial.extended.isEmpty
            || !ae.initial.initial.op.isNone || !ae.initial.initial.item.access.isEmpty then none
        else
          have : sizeOf ae.initial.initial.item.item < sizeOf o :=
            sizeOf_addExpr_primary_lt_orExpr o ae ext h
          ae.initial.initial.item.item.toMultipleEntityUID?
termination_by (sizeOf e, 1)
decreasing_by
  all_goals (simp_wf; omega)

end

private def Cst.Expr.toEntityUID? (e : Cst.Expr) : Option EntityUID := do
  let erefs ← e.toMultipleEntityUID?
  match erefs with
  | .inl eref => some eref
  | .inr _ => none

private def Cst.Expr.toEntityUIDs? (e : Cst.Expr) : Option (List EntityUID) := do
  let erefs ← e.toMultipleEntityUID?
  match erefs with
  | .inl eref => some [eref]
  | .inr erefs => some erefs

-- To be used when translating a `VariableDef` to a `PrincipalScope` or
-- a `ResourceScope`
private def Cst.VariableDef.toPRScope? (v : Cst.VariableDef) : Option Scope:=
  match v.ineq, v.entityType with
  | none, none => some .any
  | some (op, e), _ => match op, v.entityType with
    | .rEq, none => do
      let eref ← e.toEntityUID?
      some (.eq eref)
    | .rEq, some _ => none
    | .rIn, none => do
      let eref ← e.toEntityUID?
      some (.mem eref)
    | .rIn, some t => do
      let eref ← e.toEntityUID?
      let ety ← t.toEntityType?
      some (.isMem ety eref)
    | _, _ => none
  | none, some t => do
    let ety ← t.toEntityType?
    some (.is ety)

public def Cst.VariableDef.toPrincipalScope? (v : Cst.VariableDef) : Option PrincipalScope :=
  match v.var with
  | .idPrincipal => do
    let scope ← v.toPRScope?
    some (.principalScope scope)
  | _ => none

public def Cst.VariableDef.toResourceScope? (v : Cst.VariableDef) : Option ResourceScope :=
  match v.var with
  | .idResource => do
    let scope ← v.toPRScope?
    some (.resourceScope scope)
  | _ => none

private def EntityUID.isAction? (uid : EntityUID) : Bool :=
  uid.ty.id == "Action"

-- Need to check `contains_only_action_types` before using the `ActionScope` output
private def Cst.VariableDef.toActionScopeAux? (v : Cst.VariableDef) : Option ActionScope :=
  match v.var with
  | .idAction => if v.entityType.isSome then none else
    match v.ineq with
    | none => some (.actionScope (.any))
    | some (op, e) => match op with
      | .rEq => do
        let eref ← e.toEntityUID?
        some (.actionScope (.eq eref))
      | .rIn => do
        let erefs ← e.toEntityUIDs?
        some (.actionInAny erefs)
      | _ => none
  | _ => none

private def ActionScope.containsOnlyActionTypes? (as : ActionScope) : Bool :=
  match as with
  | .actionScope scope => match scope with
    | .any => true
    | .eq eref => eref.isAction?
    | .mem eref => eref.isAction?
    | _ => false
  | .actionInAny erefs => erefs.all (·.isAction?)

public def Cst.VariableDef.toActionScope? (v : Cst.VariableDef) : Option ActionScope := do
  let as ← v.toActionScopeAux?
  if as.containsOnlyActionTypes? then some as else none

public def extractScope? (vars : List Cst.VariableDef) : Option (PrincipalScope × ActionScope × ResourceScope) := do
  match vars with
  | a :: b :: c :: .nil => do
    let ps ← a.toPrincipalScope?
    let as ← b.toActionScope?
    let rs ← c.toResourceScope?
    some (ps, as, rs)
  | _ => none

-- `id` to be filled in later
public def Cst.PolicyImpl.toPolicy? (p : Cst.PolicyImpl) : Option Cedar.Spec.Policy := do
  let effect ← p.effect.toEffect?
  let (ps, as, rs) ← extractScope? p.vars
  let conds ← toConditions? p.conds
  some {id := "", effect := effect, principalScope := ps, actionScope := as, resourceScope := rs, condition := conds}

public def Cst.Policy.toPolicy? : Cst.Policy → Option Cedar.Spec.Policy
  | .policy p => p.toPolicy?

public def Cst.Policies.toPolicies? (ps : Cst.Policies) : Option Cedar.Spec.Policies := do
  let rets ← ps.ps.mapM Cst.Policy.toPolicy?
  some (rets.mapIdx (fun i p => {p with id := s!"policy{i}"}))
