module

public import Cedar.Spec.Cst
public import Cedar.Spec.Entities
public import Cedar.Spec.Request
public import Cedar.Spec.Response
public import Cedar.Spec.Value
public import Cedar.Spec.Evaluator

namespace Cedar.Spec.Cst

open Cedar.Data

-- The hierarchy of Expr in the CST
-- Expr → ExprImpl → ExprData → OrExpr → AndExpr → Relation
-- → AddExpr → MultExpr → Unary → Member → Primary

-- Write an evaluator for every level

/- Lifting helpers -/

public def Expr.toPrimary (e : Expr) : Primary :=
  .expr e

public def Primary.toMember (p : Primary) : Member :=
  {item := p, access := []}

public def Member.toUnary (m : Member) : Unary :=
  {op := none, item := m}

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

/- Other lifting helpers -/

public def Expr.toRelation (e : Expr) : Relation :=
  e.toPrimary.toMember.toUnary.toMultExpr.toAddExpr.toRelation

public def Expr.toAddExpr (e : Expr) : AddExpr :=
  e.toPrimary.toMember.toUnary.toMultExpr.toAddExpr

public def Ident.varToAddExpr (id : Ident) : AddExpr :=
  (Primary.name {path := [], name := id}).toMember.toUnary.toMultExpr.toAddExpr

/- Constants and Combinators on Expr -/

public def Relation.tt : Relation :=
  (Primary.literal Literal.liTrue).toMember.toUnary.toMultExpr.toAddExpr.toRelation

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

-- Check whether this is needed
-- public def andReduce : List Expr → List Expr
--   | [] => []
--   | Expr.tt :: es => andReduce es
--   | e :: es => e :: (andReduce es)

public def Expr.foldAnd : List Expr → Expr
  | []      => Expr.tt
  | [e]     => e
  | e :: es =>
    let e' := e.toRelation
    let es' := es.map Expr.toRelation
    let a : AndExpr := { initial := e', extended := es' }
    a.toOrExpr.toExpr

/- Conversion to Expr -/

public def VariableDef.toAndExpr (vd : VariableDef) : AndExpr :=
  let var' := vd.var.varToAddExpr
  let isClause := match vd.entityType with
    | some et => Relation.rCommon var' [(.rIn, et)]
    | none => Relation.tt
  let ineqClause := match vd.ineq with
    | some (op, e) => Relation.rCommon var' [(op, e.toAddExpr)]
    | none => Relation.tt
  {initial := isClause, extended := [ineqClause]}

public def VariableDef.toExpr (vd : VariableDef) : Expr :=
  vd.toAndExpr.toOrExpr.toExpr

public def Cond.toExpr (c : Cond) : Expr :=
  match c.cond, c.expr with
  | .idWhen, some e => e
  | .idUnless, some e => Expr.not e
  | _, _ => Expr.tt

public def PolicyImpl.toExpr (p : PolicyImpl) : Expr :=
  let varExprs := List.map VariableDef.toExpr p.vars
  let condExprs := List.map Cond.toExpr p.conds
  Expr.foldAnd (varExprs ++ condExprs)

public def Policy.toExpr : Policy → Expr
  | policy p => PolicyImpl.toExpr p

public def Policies.toExpr (ps : Policies) : Expr :=
  let exprs := List.map Policy.toExpr ps.ps
  Expr.foldAnd exprs

/- Evaluator -/

private def Ident.toString : Ident → String
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

private def Ident.toUnreservedString? : Ident → Option String
  | .idIdent s => some s
  | _ => none

private def Expr.toStringLiteral? : Expr → Option String
  | .expr e => match e.expr with
    | .edIf _ _ _ => none
    | .edOr e => match e.initial.initial with
      | .rHas _ _ => none
      | .rLike _ _ => none
      | .rCommon i e => match i.initial.initial.item.item with
        | .literal l => match l with
          | .liStr s => some s
          | _ => none
        | _ => none

private def AttrChain? (ms : List MemAccess) : Option (List Attr) :=
  match ms with
  | [] => some []
  | m :: ms => match m with
    | .field i => match i.toUnreservedString? with
      | none => none
      | some s => (AttrChain? ms).map (s :: ·)
    | .index e => match e.toStringLiteral? with
      | none => none
      | some s => (AttrChain? ms).map (s :: ·)

private def Member.toAttrs? (e : Member) : Option (List Attr) :=
  match AttrChain? e.access with
  | none => none
  | some attrs => match e.item with
    | .literal (.liStr s) =>
      if attrs.isEmpty then some [s] else none
    | .literal _ => none
    | .name { path := [], name := id } => match id.toUnreservedString? with
      | some s => some (s :: attrs)
      | none   => none
    | .name _ => none
    | _ => none

-- RelOp: rLess, rLessEq, rGreaterEq, rGreater, rNotEq, rEq, rIn
private def applyRelOp (op : RelOp) (v₁ v₂ : Value) (es : Entities) : Result Value :=
  match op with
  | .rLess => apply₂ .less v₁ v₂ es
  | .rLessEq => apply₂ .lessEq v₁ v₂ es
  | .rGreater => apply₂ .less v₂ v₁ es
  | .rGreaterEq => apply₂ .lessEq v₂ v₁ es
  | .rEq => apply₂ .eq v₁ v₂ es
  | .rNotEq => do
    let eq ← apply₂ .eq v₁ v₂ es
    apply₁ .not eq
  | .rIn => apply₂ .mem v₁ v₂ es

-- When the list is all `field`s, return the converted list of `Attr`s
-- Otherwise return `none`
private def fieldChain? : List MemAccess → Option (List Attr)
  | [] => some []
  | .field id :: xs => (fieldChain? xs).map (id.toString :: ·)
  | _ :: _ => none

private def AddExpr.toAttrs? (e : AddExpr) : Option (List Attr) :=
  if !e.extended.isEmpty then none else
  let mult := e.initial
  if !mult.extended.isEmpty then none else
  let unary := mult.initial
  match unary.op with
  | some _ => none
  | none => let member := unary.item
    match fieldChain? member.access with
    | none => none
    | some fields => match member.item with
      | .literal (.liStr s) =>
        if fields.isEmpty then some [s] else none
      | .literal _ => none
      | .name { path := [], name := id } =>
        some (id.toString :: fields)
      | .name _ => none
      | _ => none

-- Only Literal.liStr s is allowed
private def AddExpr.toPatternString? (e : AddExpr) : Option String :=
  if !e.extended.isEmpty then none else
  let mult := e.initial
  if !mult.extended.isEmpty then none else
  let unary := mult.initial
  match unary.op with
  | some _ => none
  | none => let member := unary.item
    if !member.access.isEmpty then none else
    let item := member.item
    match item with
    | .literal (.liStr s) => some s
    | _ => none

-- TODO: Review this function, written by Claude
private def String.toPattern (s : String) : Pattern :=
  let rec go : List Char → Pattern
    | []                  => []
    | '\\' :: '*'  :: cs  => .justChar '*'  :: go cs
    | '\\' :: '\\' :: cs  => .justChar '\\' :: go cs
    | '\\' :: 'n'  :: cs  => .justChar '\n' :: go cs
    | '\\' :: 'r'  :: cs  => .justChar '\r' :: go cs
    | '\\' :: 't'  :: cs  => .justChar '\t' :: go cs
    | '\\' :: '0'  :: cs  => .justChar '\x00' :: go cs
    | '\\' :: '"'  :: cs  => .justChar '"'  :: go cs
    | '\\' :: '\'' :: cs  => .justChar '\'' :: go cs
    | '\\' :: c    :: cs  => .justChar c    :: go cs   -- swallow unknown escape
    | '\\' :: []          => []                        -- lone trailing backslash
    | '*'  :: cs          => .star          :: go cs
    | c    :: cs          => .justChar c    :: go cs
  go s.toList

mutual

public def Primary.evaluate (e : Primary) (req : Request) (es : Entities) : Result Value :=
  match e with
  | .literal l => match l with
    | .liTrue => .ok (.prim (.bool true))
    | .liFalse => .ok (.prim (.bool false))
    | .liNum n => match Int64.ofInt? n.toNat with
      | some i => .ok (.prim (.int i))
      | none => .error .arithBoundsError
    | .liStr s => .ok (.prim (.string s))
  | .name n =>
    -- Not implementing names with non-empty paths for now
    if !n.path.isEmpty then .error .typeError
    else match n.name with
      | .idPrincipal => .ok (.prim (.entityUID req.principal))
      | .idAction => .ok (.prim (.entityUID req.action))
      | .idResource => .ok (.prim (.entityUID req.resource))
      | .idContext => .ok (.record req.context)
      | _ => .error .typeError
  | .expr e => sorry -- e.evaluate req es
  | .eList xs => sorry -- do
    -- let vs ← xs.mapM (fun x => x.evaluate req es)
    -- .ok (.set (Set.make vs))
  | .ref r => match r with
    | .uid path (.string eid) =>
      let ids := path.path.map Ident.toString
      let last := path.name.toString
      let etype : Spec.Name := { id := last, path := ids }
      .ok (.prim (.entityUID { ty := etype, eid := eid }))
    | .ref _ _ => .error .typeError

-- Call `getAttr` recursively, a design choice that can be changed later
public def Member.evaluate (e : Member) (req : Request) (es : Entities) : Result Value := do
  let head ← e.item.evaluate req es
  match AttrChain? e.access with
  | none => .error .typeError
  | some attrs => attrs.foldlM (fun v a => getAttr v a es) head

-- NegOp: nBang i, nOverBang, nDash i, nOverDash
-- `.nDash` case is handled with more intricacy in cst_to_ast.rs,
-- mainly for the `(neg (I64::MIN))` case.
public def Unary.evaluate (e : Unary) (req : Request) (es : Entities) : Result Value :=
  match e.op with
  | none => e.item.evaluate req es
  | some op => do
      let mval ← e.item.evaluate req es
      match op with
        | .nBang n => if n % 2 == 0 then .ok mval else apply₁ .not mval
        | .nDash n => if n % 2 == 0 then .ok mval else apply₁ .neg mval
        | _ => .error .arithBoundsError

-- Division and Modulo are rejected in cst_to_ast.rs
public def MultExpr.evaluate (e : MultExpr) (req : Request) (es : Entities) : Result Value := do
  let b ← (e.initial.evaluate req es)
  let result ← e.extended.foldlM
    (fun acc a => do
      let aval ← a.2.evaluate req es
      match a.1 with
      | .mTimes => apply₂ .mul acc aval es
      | _ => .error .arithBoundsError )
    (init := b)
  .ok result

public def AddExpr.evaluate (e : AddExpr) (req : Request) (es : Entities) : Result Value := do
  let b ← (e.initial.evaluate req es)
  let result ← e.extended.foldlM
    (fun acc a => do
      let aval ← a.2.evaluate req es
      match a.1 with
      | .aPlus => apply₂ .add acc aval es
      | .aMinus => apply₂ .sub acc aval es )
    (init := b )
  .ok result

public def Relation.evaluate (e : Relation) (req : Request) (es : Entities) : Result Value :=
  match e with
  -- Currently assuming that the `RelOp` cannot be chained
  | .rCommon x xs => match xs with
    | [] => x.evaluate req es
    | [(op, y)] => do
      let v₁ ← x.evaluate req es
      let v₂ ← y.evaluate req es
      applyRelOp op v₁ v₂ es
    | _ => .error .typeError
  | .rHas t f => do
      let v ← t.evaluate req es
      match f.toAttrs? with
      | none => .error .typeError
      | some [] => .error .typeError
      | some (a :: as) =>
        -- For `r has x.y.z`: call `hasAttr r.x.y z es`
        let (v', last) ← as.foldlM
          (fun (acc : Value × Attr) attr => do
            let next ← getAttr acc.1 acc.2 es
            pure (next, attr))
          (v, a)
        hasAttr v' last es
  | .rLike t p => match p.toPatternString? with
    | none => .error .typeError
    | some s => do
      let v ← t.evaluate req es
      apply₁ (.like (String.toPattern s)) v

public def AndExpr.evaluate (e : AndExpr) (req : Request) (es : Entities) : Result Value := do
  let b ← (e.initial.evaluate req es).as Bool
  let result ← e.extended.foldlM
    (fun acc a => if !acc then .ok acc else (a.evaluate req es).as Bool)
    (init := b)
  .ok result

public def OrExpr.evaluate (e : OrExpr) (req : Request) (es : Entities) : Result Value := do
  let b ← (e.initial.evaluate req es).as Bool
  let result ← e.extended.foldlM
    (fun acc a => if acc then .ok acc else (a.evaluate req es).as Bool)
    (init := b)
  .ok result

public def ExprData.evaluate (e : ExprData) (req : Request) (es : Entities) : Result Value :=
  match e with
  | .edOr e => e.evaluate req es
  | .edIf i t f => do
    let b ← (i.evaluate req es).as Bool
    if b then t.evaluate req es else f.evaluate req es
termination_by sizeOf e

public def ExprImpl.evaluate (e : ExprImpl) (req : Request) (es : Entities) : Result Value :=
  e.expr.evaluate req es
termination_by sizeOf e
decreasing_by cases e; simp_wf

public def Expr.evaluate (e : Expr) (req : Request) (es : Entities) : Result Value :=
  match e with
  | .expr e => e.evaluate req es
termination_by sizeOf e

end
