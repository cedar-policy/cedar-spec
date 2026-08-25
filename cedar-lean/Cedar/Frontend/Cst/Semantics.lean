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


module

public import Cedar.Frontend.Cst.Syntax
public import Cedar.Frontend.Cst.Common
public import Cedar.Spec.Entities
public import Cedar.Spec.Request
public import Cedar.Spec.Response
public import Cedar.Spec.Value
public import Cedar.Spec.Evaluator

namespace Cedar.Frontend.Cst

open Cedar.Data
open Cedar


-- The hierarchy of Expr in the CST
-- Expr → ExprImpl → ExprData → OrExpr → AndExpr → Relation
-- → AddExpr → MultExpr → Unary → Member → Primary

/- Evaluator helpers -/




-- RelOp: rLess, rLessEq, rGreaterEq, rGreater, rNotEq, rEq, rIn
-- `rGreater`/`rGreaterEq` use the `not (less/lessEq v₁ v₂)` pattern to match
-- the translator's `constructExprRel`. Behaviorally equivalent on totally-
-- comparable values; for other values, the `apply₂` errors propagate through
-- the `not` consistently with the translator's AST output.
public def applyRelOp (op : RelOp) (v₁ v₂ : Spec.Value) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match op with
  | .rLess => Spec.apply₂ .less v₁ v₂ es
  | .rLessEq => Spec.apply₂ .lessEq v₁ v₂ es
  | .rGreater => do
    let r ← Spec.apply₂ .lessEq v₁ v₂ es
    Spec.apply₁ .not r
  | .rGreaterEq => do
    let r ← Spec.apply₂ .less v₁ v₂ es
    Spec.apply₁ .not r
  | .rEq => Spec.apply₂ .eq v₁ v₂ es
  | .rNotEq => do
    let eq ← Spec.apply₂ .eq v₁ v₂ es
    Spec.apply₁ .not eq
  | .rIn => Spec.apply₂ .mem v₁ v₂ es




/- Evaluators -/

public def Str.toUnescapedString : Str → Spec.Result String
  | .string s => match unescape? s with
    | some s' => .ok s'
    | none    => .error (.cstError .stringError)

/-- Evaluate the chain of attribute checks for `r has a₀.a₁.….aₙ` with
    short-circuiting on the inner `Spec.hasAttr` returning `false`. Mirrors the
    translator's `extendedHasAttr`, which builds nested `.and (Spec.hasAttr ...) ...`. -/
public def rHasChain (v : Spec.Value) (a : Spec.Attr) (rest : List Spec.Attr) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match rest with
  | [] => Spec.hasAttr v a es
  | b :: bs => do
    let h ← Spec.hasAttr v a es
    match h with
    | .prim (.bool false) => .ok (.prim (.bool false))
    | _ => do
      let v' ← Spec.getAttr v a es
      rHasChain v' b bs es
termination_by sizeOf rest

mutual

public def Primary.evaluate (e : Primary) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match e with
  | .literal l => match l with
    | .liTrue => .ok (.prim (.bool true))
    | .liFalse => .ok (.prim (.bool false))
    | .liNum n => match Int64.ofInt? n.toNat with
      | some i => .ok (.prim (.int i))
      | none => .error (.cstError .primaryOverflowError)
    | .liStr s => do
      let s' ← Str.toUnescapedString (.string s)
      .ok (.prim (.string s'))
  | .name n =>
    if !n.path.isEmpty then .error (.cstError .nameError)
    else match n.name with
      | .idPrincipal => .ok (.prim (.entityUID req.principal))
      | .idAction => .ok (.prim (.entityUID req.action))
      | .idResource => .ok (.prim (.entityUID req.resource))
      | .idContext => .ok (.record req.context)
      | _ => .error (.cstError .nameError)
  | .expr e => e.evaluate req es
  | .eList xs => do
    let vs ← xs.mapM (fun x => x.evaluate req es)
    .ok (.set (Set.make vs))
  | .ref r => match r with
    | .uid path eid => do
      let eid' ← Str.toUnescapedString eid
      match Name.toAName? path with
      | some etype => .ok (.prim (.entityUID { ty := etype, eid := eid' }))
      | none       => .error (.cstError .unsupportedError)
    | .ref _ _ => .error (.cstError .unsupportedError)
  | .rInits r => do
    let avs ← r.mapM₁ (fun ⟨ri, hmem⟩ =>
      have : sizeOf ri.value < 1 + sizeOf r := by
        have h1 := List.sizeOf_lt_of_mem hmem
        obtain ⟨k, v⟩ := ri
        simp only [RecInit.mk.sizeOf_spec] at h1
        show sizeOf v < 1 + sizeOf r
        omega
      match ri.attr.toAttr? with
      | none => .error (.cstError .stringError)
      | some attr => do
          let val ← ri.value.evaluate req es
          .ok (attr, val))
    .ok (.record (Map.make avs))
  | .slot _ => .error (.cstError .unsupportedError)
termination_by sizeOf e

public def Member.evaluate (e : Member) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match e with
  -- Function calls
  | { item := .name { path := [], name := .idIdent s _ }, access := .call args :: rest } =>
    match s.toCedarExtFun? with
    | none => .error (.cstError .unsupportedError)
    | some xfn => do
      let args ← args.mapM (fun a => a.evaluate req es)
      let v ← Spec.call xfn args
      Member.evalAccessors v rest req es
  -- Accessors
  | { item := item, access := access } => do
    let head ← item.evaluate req es
    Member.evalAccessors head access req es
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)

public def Member.evalAccessors (head : Spec.Value) (accs : List MemAccess)
    (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match accs with
  | [] => .ok head
  -- Method call `recv.m(args)`: a field naming the method, then its arguments.
  | .field i :: .call args :: rest =>
    match Ident.toUnreservedString? i with
    | none => .error (.cstError .stringError)
    | some m => match m.toCedarMethodOp? with
      | some (.inl bop) => match args with
        | [arg] => do
          let argVal ← arg.evaluate req es
          let v ← Spec.apply₂ bop head argVal es
          Member.evalAccessors v rest req es
        | _ => .error (.cstError .arityError)
      | some (.inr uop) =>
        if args.isEmpty then do
          let v ← Spec.apply₁ uop head
          Member.evalAccessors v rest req es
        else .error (.cstError .arityError)
      | none => .error (.cstError .unsupportedError)
  -- Attribute access `recv.attr`.
  | .field i :: rest =>
    match Ident.toUnreservedString? i with
    | none => .error (.cstError .stringError)
    | some attr => do
      let v ← Spec.getAttr head attr es
      Member.evalAccessors v rest req es
  -- Indexed attribute access `recv["attr"]`.
  | .index ex :: rest =>
    match Expr.toUnescapedStringLiteral? ex with
    | none => .error (.cstError .stringError)
    | some attr => do
      let v ← Spec.getAttr head attr es
      Member.evalAccessors v rest req es
  -- A call with no preceding field accessor is a call on a non-name value,
  -- which the translator rejects.
  | .call _ :: _ => .error (.cstError .unsupportedError)
termination_by sizeOf accs
decreasing_by
  all_goals simp_wf
  all_goals omega

-- NegOp: nBang i, nOverBang, nDash i, nOverDash
-- The `.nDash` numeric-literal case is handled specially so that the value
-- `-(Int64.MAX + 1) = Int64.MIN` is representable, matching the AST translator.
public def Unary.evaluate (e : Unary) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match e.op with
  | none => e.item.evaluate req es
  | some (.nBang n) =>
      if n == 0 then e.item.evaluate req es else do
        let mval ← e.item.evaluate req es
        -- error the non-bool
        match mval with
        | .prim (.bool b) =>
            if n % 2 == 0 then .ok (.prim (.bool b)) else .ok (.prim (.bool !b))
        | _ => .error .typeError
  | some (.nDash n) =>
      if n == 0 then e.item.evaluate req es else
      match Member.toLit? e.item with
      | some (.liNum x) =>
        let xNat := x.toNat
        let minMagnitude := (Int64.MAX + 1).toNat
        match compare xNat minMagnitude with
        | .eq =>
          -- AST translates to `(lit Int64.MIN).dashN (n-1)`.  Since
          -- `Int64.MIN.neg?` fails, only `n = 1` succeeds (zero further
          -- negations applied); any larger `n` errors on the first negation.
          if n == 1
          then .ok (.prim (.int Int64.MIN.toInt64))
          else .error .arithBoundsError
        | .lt =>
          match Int64.ofInt? (Int.ofNat xNat) with
          | some y =>
            if n % 2 == 0 then .ok (.prim (.int y)) else .ok (.prim (.int (-y)))
          | none => .error .arithBoundsError
        | .gt => .error .arithBoundsError
      | _ => do
          let mval ← e.item.evaluate req es
          -- Force the type check and error the non-ints. We must also check
          -- `i.neg?` *before* the parity shortcut: when `i = Int64.MIN`, the
          -- AST iterates `apply₁ .neg` and errors on the first step, so this
          -- case must error regardless of parity.
          match mval with
          | .prim (.int i) =>
              match i.neg? with
              | none => .error .arithBoundsError
              | some j =>
                  if n % 2 == 0 then .ok (.prim (.int i))
                  else .ok (.prim (.int j))
          | _ => .error .typeError
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

public def MultExpr.evaluate (e : MultExpr) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value := do
  let b ← e.initial.evaluate req es
  MultExpr.foldOps b e.extended req es
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

-- Division and Modulo are rejected in cst_to_ast.rs
public def MultExpr.foldOps (acc : Spec.Value) (xs : List (MultOp × Unary))
    (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match xs with
  | [] => .ok acc
  | (op, u) :: rest => do
    let aval ← u.evaluate req es
    let acc' ← match op with
      | .mTimes => Spec.apply₂ .mul acc aval es
      | _ => .error (.cstError .unsupportedError)
    MultExpr.foldOps acc' rest req es
termination_by sizeOf xs

public def AddExpr.evaluate (e : AddExpr) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value := do
  let b ← e.initial.evaluate req es
  AddExpr.foldOps b e.extended req es
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

public def AddExpr.foldOps (acc : Spec.Value) (xs : List (AddOp × MultExpr))
    (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match xs with
  | [] => .ok acc
  | (op, m) :: rest => do
    let aval ← m.evaluate req es
    let acc' ← match op with
      | .aPlus  => Spec.apply₂ .add acc aval es
      | .aMinus => Spec.apply₂ .sub acc aval es
    AddExpr.foldOps acc' rest req es
termination_by sizeOf xs

public def Relation.evaluate (e : Relation) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match e with
  -- `RelOp` cannot be chained
  | .rCommon x xs => match xs with
    | [] => x.evaluate req es
    | [(op, y)] => do
      let v₁ ← x.evaluate req es
      let v₂ ← y.evaluate req es
      applyRelOp op v₁ v₂ es
    | _ => .error (.cstError .unsupportedError)
  | .rHas t f => do
      let v ← t.evaluate req es
      match f.toAttrs? with
      | none => .error (.cstError .unsupportedError)
      | some [] => .error (.cstError .unsupportedError)
      | some (a :: as) =>
        -- For `r has x.y.z`: short-circuit on `false` between getAttr steps,
        -- mirroring the translator's `.and (hasAttr ...) (extendedHasAttr ...)`
        -- which short-circuits on the inner `hasAttr` returning `false`.
        rHasChain v a as es
  | .rLike t p => match p.toPatternString? with
    | none => .error (.cstError .stringError)
    | some s => do
      let v ← t.evaluate req es
      match toPattern? s with
      | some p => Spec.apply₁ (.like p) v
      | none => .error (.cstError  .stringError)
  | .rIsIn t ety inEntity => match ety.toEntityTypeName? with
    | none => .error (.cstError .nameError)
    | some etyName => do
      let v ← t.evaluate req es
      let isResult ← Spec.apply₁ (.is etyName) v
      match inEntity with
      | none => .ok isResult
      | some ie => do
        let b ← isResult.asBool
        if !b then .ok false
        else do
          let v₂ ← ie.evaluate req es
          Spec.apply₂ .mem v v₂ es
termination_by sizeOf e

public def AndExpr.evaluate (e : AndExpr) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value := do
  let acc ← e.initial.evaluate req es
  AndExpr.foldOps acc e.extended req es
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

-- Mirrors the AST `Expr.and acc rel` evaluation: coerce acc to Bool, short-circuit
-- on `false`, otherwise coerce rel.evaluate to Bool, wrap as a Value, recurse.
public def AndExpr.foldOps (acc : Spec.Value) (xs : List Relation)
    (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match xs with
  | [] => .ok acc
  | x :: rest => do
    let b ← acc.asBool
    if !b then .ok (.prim (.bool false)) else do
      let b' ← (x.evaluate req es).as Bool
      AndExpr.foldOps (.prim (.bool b')) rest req es
termination_by sizeOf xs

public def OrExpr.evaluate (e : OrExpr) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value := do
  let acc ← e.initial.evaluate req es
  OrExpr.foldOps acc e.extended req es
termination_by sizeOf e
decreasing_by
  all_goals cases e; simp_wf; omega

-- Mirrors the AST `Expr.or acc rhs` evaluation: coerce acc to Bool, short-circuit
-- on `true`, otherwise coerce rhs.evaluate to Bool, wrap as a Value, recurse.
public def OrExpr.foldOps (acc : Spec.Value) (xs : List AndExpr)
    (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match xs with
  | [] => .ok acc
  | x :: rest => do
    let b ← acc.asBool
    if b then .ok (.prim (.bool true)) else do
      let b' ← (x.evaluate req es).as Bool
      OrExpr.foldOps (.prim (.bool b')) rest req es
termination_by sizeOf xs

public def ExprData.evaluate (e : ExprData) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match e with
  | .edOr e => e.evaluate req es
  | .edIf i t f => do
    let b ← (i.evaluate req es).as Bool
    if b then t.evaluate req es else f.evaluate req es
termination_by sizeOf e

public def ExprImpl.evaluate (e : ExprImpl) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  e.expr.evaluate req es
termination_by sizeOf e
decreasing_by cases e; simp_wf

public def Expr.evaluate (e : Expr) (req : Spec.Request) (es : Spec.Entities) : Spec.Result Spec.Value :=
  match e with
  | .expr e => e.evaluate req es
termination_by sizeOf e

end

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

public def Relation.ff : Relation :=
  (Primary.literal Literal.liFalse).toMember.toUnary.toMultExpr.toAddExpr.toRelation

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
  match vd.entityType, vd.ineq with
  | some et, some (.rIn, e) =>
    {initial := Relation.rIsIn var' et (some e.toAddExpr), extended := []}
  | some et, none =>
    {initial := Relation.rIsIn var' et none, extended := []}
  | none, some (op, e) =>
    {initial := Relation.rCommon var' [(op, e.toAddExpr)], extended := []}
  | none, none =>
    {initial := Relation.tt, extended := []}
  | some _, some (_, _) =>
    -- entityType with a non-`in` operator (e.g., `==`) is not valid
    {initial := Relation.ff, extended := []}

public def VariableDef.toExpr (vd : VariableDef) : Expr :=
  vd.toAndExpr.toOrExpr.toExpr

public def Cond.toExpr (c : Cond) : Expr :=
  match c.kind with
  | .idWhen => c.body
  | .idUnless => Expr.not c.body
  | _ => Expr.tt

-- The `effect` field is not considered in this translation
public def PolicyImpl.toExpr (p : PolicyImpl) : Expr :=
  let varExprs := List.map VariableDef.toExpr p.vars
  let condExprs := List.map Cond.toExpr p.conds
  Expr.foldAnd (varExprs ++ condExprs)

public def Policy.toExpr : Policy → Expr
  | policy p => PolicyImpl.toExpr p

public def Policies.toExpr (ps : Policies) : Expr :=
  let exprs := List.map Policy.toExpr ps.ps
  Expr.foldAnd exprs

end Cedar.Frontend.Cst
