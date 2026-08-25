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
public import Cedar.Spec.Expr
public import Cedar.Spec.Policy
public import Cedar.Spec.Value

public def String.toUnreservedId? (s : String) : Option String :=
  match s with
  | "principal" | "action" | "resource" | "context"
  | "true" | "false" | "permit" | "forbid"
  | "when" | "unless" | "in" | "has" | "like" | "is"
  | "if" | "then" | "else" => none
  | _ => some s

namespace Cedar.Frontend.Cst

open Cedar

public abbrev CExpr := Expr
public abbrev CName := Name
public abbrev AName := Spec.Name

public inductive ExprOrSpecial where
  -- Any expression except a variable, name, string literal, or bool literal
  | expr (e : Spec.Expr)
  -- Variables, which act as expressions or names
  | var (v : Spec.Var)
  -- Name that isn't an expr and couldn't be converted to var
  | name (n : Spec.Name)
  -- String literal, not yet unescaped
  | strLit (lit : String)
  -- A boolean literal
  | boolLit (v : Bool)


public def Ident.toUnreservedId? : Ident → Option String
  | .idIdent s _ => if Unreserved? s then some s else none
  | _ => none

public def varToString : Spec.Var → String
  | .principal => "principal"
  | .action => "action"
  | .resource => "resource"
  | .context => "context"

public inductive AstAccessor where
  | field (id : Ident)
  | call (args : List Spec.Expr)
  | index (s : String)

public def AstAccessor.toString : AstAccessor → String
  | .field id => Ident.toString id
  | .index s => s
  | .call _ => "<call>"

public def ExprOrSpecial.toExpr? : ExprOrSpecial → Option Spec.Expr
  | .expr e => some e
  | .var v => some (.var v)
  | .strLit s => do
      let unescaped ← unescape? s
      some (.lit (.string unescaped))
  | .boolLit b => some (.lit (.bool b))
  | .name _ => none

public def Literal.toExprOrSpecial? (l : Literal) : Option ExprOrSpecial :=
  match l with
  | .liTrue => some (.boolLit true)
  | .liFalse => some (.boolLit false)
  | .liNum n => do
    let i ← Int64.ofInt? (n.toNat)
    some (.expr (.lit (.int i)))
  | .liStr s => some (.strLit s)

public def Ref.toExprOrSpecial? (r : Ref) : Option ExprOrSpecial :=
  match r with
  | .uid path eid => do
    let ty ← path.toAName?
    match eid with
    | .string s => do
      let unescaped ← unescape? s
      some (.expr (.lit (.entityUID {ty := ty, eid := unescaped})))
  | .ref _ _ => none

public def oneArg? (args : List Spec.Expr) : Option Spec.Expr :=
  match args with
  | e :: [] => some e
  | _ => none

public def toFunc? (n : Spec.Name) (args : List Spec.Expr) : Option Spec.Expr := do
  if n.path.isEmpty then (.call · args) <$> String.toExtFun? n.id else none

-- Remember to check that id is unreserved
public def Ident.toMeth? (id : Ident) (recv : Spec.Expr) (args : List Spec.Expr) : Option Spec.Expr :=
  match id with
  | .idIdent s _ => do
    let op ← String.toMethodOp? s
    match op with
    | .inl bop => let arg ← oneArg? args; some (.binaryApp bop recv arg)
    | .inr uop => if args.isEmpty then some (.unaryApp uop recv) else none
  | _ => none


public def memberAuxA : ExprOrSpecial → List AstAccessor → Option (ExprOrSpecial ⊕ (Spec.Expr × List AstAccessor))
  -- case 1: no accessors, return head immediately
  | prim, [] => some (.inl prim)

  -- case 2: access on arbitrary expression, defer to phase B
  | prim@(.expr _), asts@(_ :: _)
  | prim@(.strLit _), asts@(_ :: _)
  | prim@(.boolLit _), asts@(_ :: _) => do
    let e ← prim.toExpr?
    some (.inr (e, asts))

  -- case 3: function call
  | .name n, .call args :: rest => do
    let e ← toFunc? n args
    some (.inr (e, rest))

  -- case 4: variable function call, error
  | .var _, .call _ :: _ => none

  -- case 5: method call on name, error
  | .name _, .field _ :: .call _ :: _ => none

  -- case 6: method call on a variable
  | prim@(.var _), .field id :: .call args :: rest => do
    let recv ← prim.toExpr?
    let e ← id.toMeth? recv args
    some (.inr (e, rest))

  -- case 7: attribute access on a variable
  | .var v, .field id :: rest =>
    let e := .getAttr (.var v) (Ident.toString id)
    some (.inr (e, rest))

  -- case 8: attribute access on a name, error
  | .name _, .field _ :: _ => none

  -- case 9: index access on a name, error
  | .name _, .index _ :: _ => none

  -- case 10: index access on a variable
  | .var v, .index id :: rest =>
    let e := .getAttr (.var v) id
    some (.inr (e, rest))

public def memberAuxB (head : Spec.Expr) : List AstAccessor → Option Spec.Expr
  | .nil => some head

  -- function call on arbitrary expressions, error
  | .call _ :: _ => none

  -- method call on arbitrary expressions
  | .field id :: .call args :: rest => do
    let head' ← id.toMeth? head args
    memberAuxB head' rest

  -- field of arbitrary expressions
  | .field id :: rest => do
    memberAuxB (.getAttr head (Ident.toString id)) rest

  -- index into arbitrary expressions
  | .index id :: rest => do
    memberAuxB (.getAttr head id) rest

public def memberAux (prim : ExprOrSpecial) (accs : List AstAccessor) : Option ExprOrSpecial := do
  let reta ← memberAuxA prim accs
  match reta with
  | .inl eos => some eos
  | .inr (e, rest) =>
    let ret ← memberAuxB e rest
    some (.expr ret)

public def bangN (e : Spec.Expr) (n : Nat) : Spec.Expr :=
  if n == 0 then e else bangN (Spec.Expr.unaryApp .not e) (n-1)
  termination_by n
  decreasing_by rename_i h; simp at h; omega

public def dashN (e : Spec.Expr) (n : Nat) : Spec.Expr :=
  if n == 0 then e else dashN (Spec.Expr.unaryApp .neg e) (n-1)
  termination_by n
  decreasing_by rename_i h; simp at h; omega

public def constructExprRel (op : RelOp) (e₁ e₂ : Spec.Expr) : Spec.Expr :=
  match op with
  | .rLess => .binaryApp .less e₁ e₂
  | .rLessEq => .binaryApp .lessEq e₁ e₂
  | .rGreaterEq => .unaryApp .not (.binaryApp .less e₁ e₂)
  | .rGreater => .unaryApp .not (.binaryApp .lessEq e₁ e₂)
  | .rNotEq => .unaryApp .not (.binaryApp .eq e₁ e₂)
  | .rEq => .binaryApp .eq e₁ e₂
  | .rIn => .binaryApp .mem e₁ e₂

public def constructAttrsAux? : List MemAccess → Option (List String)
  | [] => some []
  | .field id :: rest => do
    let head ← id.toUnreservedId? -- move toUnreserbvedId to CstCommon later
    let tail ← constructAttrsAux? rest
    head :: tail
  | .index _ :: _ => none
  | .call _ :: _ => none

-- `first` should already be verified to be unreserved
-- Verify all elements in `rest` are unreserved
public def constructAttrs? (first : String) (rest : List MemAccess) : Option (List String) := do
  let tail ← constructAttrsAux? rest
  some (first :: tail)

public def extendedHasAttr (target : Spec.Expr) (fields : List String) : Spec.Expr :=
  match fields with
  | [] => target
  | [f] => .hasAttr target f
  | f :: rest =>
    .and (.hasAttr target f) (extendedHasAttr (.getAttr target f) rest)

public def ExprOrSpecial.toValidAttr? (eos : ExprOrSpecial) : Option Spec.Attr :=
  match eos with
  | .expr _ => none
  | .var v => some (varToString v)
  | .name n => if n.path.isEmpty then some (n.id) else none
  | .strLit lit => unescape? lit
  | .boolLit _ => none

mutual

public def rInitsToMap? (rs : List RecInit) : Option (List (Spec.Attr × Spec.Expr)) :=
  match rs with
  | [] => some []
  | r :: rs => do
    let attr_eos ← r.attr.toExprOrSpecial?
    let maybe_attr ← attr_eos.toValidAttr?
    let maybe_value ← r.value.toAExpr?
    let rest ← rInitsToMap? rs
    (maybe_attr, maybe_value) :: rest
termination_by (sizeOf rs, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (cases r; simp only [RecInit.mk.sizeOf_spec]; omega)

public def MemAccess.toAstAccessor? (m : MemAccess) : Option AstAccessor :=
  match m with
  | .field i => match i with
    | .idIdent s h => do
      let _ ← Ident.toUnreservedString? (.idIdent s h)
      some (.field (.idIdent s h))
    | _ => none
  | .index e => do
    let s ← Expr.toUnescapedStringLiteral? e
    some (.index s)
  | .call es => do
    let xs ← Expr.toAExprs? es
    some (.call xs)
termination_by (sizeOf m, 0)
decreasing_by
  all_goals simp_wf
  all_goals omega

public def Primary.toExprOrSpecial? (e : Primary) : Option ExprOrSpecial :=
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
  | .slot _ => none
  | .eList es => do
    let aes ← es.mapM₁ (fun ⟨x, _⟩ => x.toAExpr?)
    some (.expr (.set aes))
  | .rInits r => do
    let map ← rInitsToMap? r
    some (.expr (.record map))
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals first | omega | (rename_i h; have := List.sizeOf_lt_of_mem h; omega)

public def Primary.toAExpr? (e : Primary) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def Member.toExprOrSpecial? (e : Member) : Option ExprOrSpecial := do
  let prim ← e.item.toExprOrSpecial?
  let accessors ← e.access.mapM (MemAccess.toAstAccessor?)
  memberAux prim accessors
termination_by (sizeOf e, 0)
decreasing_by
  all_goals simp_wf
  all_goals
    (obtain ⟨item, access⟩ := e
     simp only [Member.mk.sizeOf_spec]
     first
       | omega
       | (have h := List.sizeOf_lt_of_mem (by assumption)
          dsimp only at h
          omega))

public def Member.toAExpr? (e : Member) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def Unary.toExprOrSpecial? (e : Unary) : Option ExprOrSpecial :=
  match e.op with
  | none => e.item.toExprOrSpecial?
  | some (.nDash 0) => e.item.toExprOrSpecial?
  | some (.nBang n) => do
    let eos ← e.item.toExprOrSpecial?
    let expr ← eos.toExpr?
    some (.expr (bangN expr (n.toNat)))
  | some (.nDash n) =>
    match Member.toLit? e.item with
    | some (.liNum x) =>
      let xNat := x.toNat
      let minMagnitude := (Int64.MAX + 1).toNat
      match compare xNat minMagnitude with
      | .eq => some (.expr (dashN (Spec.Expr.lit (.int (Int64.MIN).toInt64)) (n-1).toNat))
      | .lt =>
        match Int64.ofInt? (Int.ofNat xNat) with
        | some y => some (.expr (dashN (Spec.Expr.lit (.int (-y))) (n-1).toNat))
        | none => none
      | .gt => none
    | _ => do
      let eos ← e.item.toExprOrSpecial?
      let expr ← eos.toExpr?
      some (ExprOrSpecial.expr (dashN expr n.toNat))
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [Unary.mk.sizeOf_spec]; omega)

public def Unary.toAExpr? (e : Unary) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def MultExpr.foldExtended (acc : Spec.Expr) (xs : List (MultOp × Unary)) : Option Spec.Expr :=
  match xs with
  | [] => some acc
  | (op, u) :: rest => do
    let aval ← u.toAExpr?
    match op with
    | .mTimes => MultExpr.foldExtended (Spec.Expr.binaryApp .mul acc aval) rest
    | _ => none
termination_by (sizeOf xs, 0)

public def MultExpr.toExprOrSpecial? (e : MultExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← MultExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [MultExpr.mk.sizeOf_spec]; omega)

public def MultExpr.toAExpr? (e : MultExpr) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def AddExpr.foldExtended (acc : Spec.Expr) (xs : List (AddOp × MultExpr)) : Option Spec.Expr :=
  match xs with
  | [] => some acc
  | (op, m) :: rest => do
    let aval ← m.toAExpr?
    match op with
    | .aPlus  => AddExpr.foldExtended (Spec.Expr.binaryApp .add acc aval) rest
    | .aMinus => AddExpr.foldExtended (Spec.Expr.binaryApp .sub acc aval) rest
termination_by (sizeOf xs, 0)

public def AddExpr.toExprOrSpecial? (e : AddExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← AddExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [AddExpr.mk.sizeOf_spec]; omega)

public def AddExpr.toAExpr? (e : AddExpr) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def AddExpr.toEntityType? (e : AddExpr) : Option Spec.EntityType :=
  e.toEntityTypeName?


-- In Rust, `to_has_rhs` has the output type `Option (String ⊕ UnreservedId)`.
-- `UnservedId` is essentially a string, but passed the check that it's not
-- "__cedar". In this implementation, we keep the output type `String`
-- and return a `none` if it is reserved.
public def AddExpr.toHasRhs? (e : AddExpr) : Option (String ⊕ List String) := do
  if (!e.extended.isEmpty) || (!e.initial.extended.isEmpty) || (!e.initial.initial.op.isNone) then none else
  let member := e.initial.initial.item
  match member.item with
  | .literal _ | .name _ =>
    let item ← member.item.toExprOrSpecial?
    match item, member.access with
    | .strLit lit, [] => (unescape? lit).map .inl
    | .var v, rest => (constructAttrs? (varToString v) rest).map .inr
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
      simp only [AddExpr.mk.sizeOf_spec, MultExpr.mk.sizeOf_spec,
        Unary.mk.sizeOf_spec, Member.mk.sizeOf_spec]
      omega
    omega

public def AddExpr.toPattern? (e : AddExpr) : Option Spec.Pattern := do
  let s ← e.toPatternString?
  toPattern? s

public def Relation.toExprOrSpecial? : Relation → Option ExprOrSpecial
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
  | .rIsIn target ety inEntity => do
    let maybe_target ← target.toAExpr?
    let maybe_entity_type ← ety.toEntityType?
    let isExpr := Spec.Expr.unaryApp (.is maybe_entity_type) maybe_target
    match inEntity with
    | some ie => do
      let maybe_in ← ie.toAExpr?
      some (.expr (.and isExpr (.binaryApp .mem maybe_target maybe_in)))
    | none => some (.expr isExpr)
termination_by e => (sizeOf e, 0)

public def Relation.toAExpr? (e : Relation) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def AndExpr.foldExtended (acc : Spec.Expr) (xs : List Relation) : Option Spec.Expr :=
  match xs with
  | [] => some acc
  | rel :: rest => do
    let aval ← rel.toAExpr?
    AndExpr.foldExtended (Spec.Expr.and acc aval) rest
termination_by (sizeOf xs, 0)

public def AndExpr.toExprOrSpecial? (e : AndExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← AndExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [AndExpr.mk.sizeOf_spec]; omega)

public def AndExpr.toAExpr? (e : AndExpr) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def OrExpr.foldExtended (acc : Spec.Expr) (xs : List AndExpr) : Option Spec.Expr :=
  match xs with
  | [] => some acc
  | ande :: rest => do
    let aval ← ande.toAExpr?
    OrExpr.foldExtended (Spec.Expr.or acc aval) rest
termination_by (sizeOf xs, 0)

public def OrExpr.toExprOrSpecial? (e : OrExpr) : Option ExprOrSpecial :=
  match e.extended with
  | [] => e.initial.toExprOrSpecial?
  | _ => do
    let first ← e.initial.toAExpr?
    let result ← OrExpr.foldExtended first e.extended
    some (.expr result)
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [OrExpr.mk.sizeOf_spec]; omega)

public def OrExpr.toAExpr? (e : OrExpr) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def ExprData.toExprOrSpecial? : ExprData → Option ExprOrSpecial
  | .edOr ore => ore.toExprOrSpecial?
  | .edIf i t e => do
    let maybe_guard ← i.toAExpr?
    let maybe_then ← t.toAExpr?
    let maybe_else ← e.toAExpr?
    some (.expr (.ite maybe_guard maybe_then maybe_else))
termination_by e => (sizeOf e, 0)

public def ExprData.toAExpr? (e : ExprData) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def ExprImpl.toExprOrSpecial? (e : ExprImpl) : Option ExprOrSpecial :=
  e.expr.toExprOrSpecial?
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (cases e; simp only [ExprImpl.mk.sizeOf_spec]; omega)

public def ExprImpl.toAExpr? (e : ExprImpl) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?

public def Expr.toExprOrSpecial? : CExpr → Option ExprOrSpecial
  | .expr impl => impl.toExprOrSpecial?
termination_by e => (sizeOf e, 0)

public def Expr.toAExpr? (e : Expr) : Option Spec.Expr := do
  let ret ← e.toExprOrSpecial?
  ret.toExpr?
termination_by (sizeOf e, 1)

public def Expr.toAExprs? : List CExpr → Option (List Spec.Expr)
  | [] => some []
  | e :: es => do
    let a ← e.toAExpr?
    let as ← Expr.toAExprs? es
    some (a :: as)
termination_by es => (sizeOf es, 0)
decreasing_by
  all_goals simp_wf
  all_goals omega

end

public def Cond.toCondition? (cond : Cond) : Option Spec.Condition := do
  let kind ← cond.kind.toConditionKind?
  let body ← cond.body.toAExpr?
  some {kind := kind, body := body}

public def toConditions? (conds : List Cond) : Option Spec.Conditions := do
  conds.mapM (·.toCondition?)


mutual

public def Primary.toMultipleEntityUID? (p : Primary) : Option (Spec.EntityUID ⊕ List Spec.EntityUID) :=
  match p with
  | .literal _ | .name _ | .slot _ => none
  | .ref r => match r with
    | .uid path (.string s) => do
      let maybe_path ← path.toAName?
      let maybe_eid ← unescape? s
      some (.inl {ty := maybe_path, eid := maybe_eid})
    | .ref _ _ => none
  | .expr e => e.toMultipleEntityUID?
  | .eList es => do
    let uids ← es.attach.mapM (fun ⟨x, hmem⟩ =>
      have : sizeOf x < sizeOf es := List.sizeOf_lt_of_mem hmem
      match x.toMultipleEntityUID? with
      | some (.inl eref) => some eref
      | _ => none)
    some (.inr uids)
  | .rInits _ => none
termination_by (sizeOf p, 0)
decreasing_by
  all_goals (simp_wf; omega)

public def Expr.toMultipleEntityUID? (e : Expr) : Option (Spec.EntityUID ⊕ List Spec.EntityUID) :=
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
      | .rIsIn _ _ _ => none
termination_by (sizeOf e, 1)
decreasing_by
  all_goals (simp_wf; omega)

end

public def Expr.toEntityUID? (e : Expr) : Option Spec.EntityUID := do
  let erefs ← e.toMultipleEntityUID?
  match erefs with
  | .inl eref => some eref
  | .inr _ => none

public def Expr.toEntityUIDs? (e : Expr) : Option (List Spec.EntityUID) := do
  let erefs ← e.toMultipleEntityUID?
  match erefs with
  | .inl eref => some [eref]
  | .inr erefs => some erefs

-- To be used when translating a `VariableDef` to a `PrincipalScope` or
-- a `ResourceScope`
public def VariableDef.toPRScope? (v : VariableDef) : Option Spec.Scope:=
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

public def VariableDef.toPrincipalScope? (v : VariableDef) : Option Spec.PrincipalScope :=
  match v.var with
  | .idPrincipal => do
    let scope ← v.toPRScope?
    some (.principalScope scope)
  | _ => none

public def VariableDef.toResourceScope? (v : VariableDef) : Option Spec.ResourceScope :=
  match v.var with
  | .idResource => do
    let scope ← v.toPRScope?
    some (.resourceScope scope)
  | _ => none

public def isAction? (uid : Spec.EntityUID) : Bool :=
  uid.ty.id == "Action"

-- Need to check `contains_only_action_types` before using the `ActionScope` output
public def VariableDef.toActionScopeAux? (v : VariableDef) : Option Spec.ActionScope :=
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

public def containsOnlyActionTypes? (as : Spec.ActionScope) : Bool :=
  match as with
  | .actionScope scope => match scope with
    | .any => true
    | .eq eref => isAction? eref
    | .mem eref => isAction? eref
    | _ => false
  | .actionInAny erefs => erefs.all (isAction? ·)

public def VariableDef.toActionScope? (v : VariableDef) : Option Spec.ActionScope := do
  let as ← v.toActionScopeAux?
  if containsOnlyActionTypes? as then some as else none

public def extractScope? (vars : List VariableDef) : Option (Spec.PrincipalScope × Spec.ActionScope × Spec.ResourceScope) := do
  match vars with
  | a :: b :: c :: .nil => do
    let ps ← a.toPrincipalScope?
    let as ← b.toActionScope?
    let rs ← c.toResourceScope?
    some (ps, as, rs)
  | _ => none

public def PolicyImpl.toPolicy? (p : PolicyImpl) : Option Spec.Policy := do
  let effect ← Ident.toEffect? p.effect
  let (ps, as, rs) ← extractScope? p.vars
  let conds ← toConditions? p.conds
  some {id := p.id, effect := effect, principalScope := ps, actionScope := as, resourceScope := rs, condition := conds}

public def Policy.toPolicy? : Policy → Option Spec.Policy
  | .policy p => p.toPolicy?

public def Policies.toPolicies? (ps : Policies) : Option Spec.Policies := do
  ps.ps.mapM Policy.toPolicy?
