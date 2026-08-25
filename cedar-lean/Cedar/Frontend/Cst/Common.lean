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
public import Cedar.Frontend.StringParsing
public import Cedar.Spec.Wildcard
public import Cedar.Spec.Policy

namespace Cedar.Frontend.Cst

open Cedar


public def Member.toLit? (e : Member) : Option Literal :=
  if !e.access.isEmpty then none else
  match e.item with
  | .literal l => some l
  | _ => none

public def Unreserved? (s : String) : Bool :=
  match s with
  | "principal"
  | "action"
  | "resource"
  | "context"
  | "true"
  | "false"
  | "permit"
  | "forbid"
  | "when"
  | "unless"
  | "in"
  | "has"
  | "like"
  | "is"
  | "if"
  | "then"
  | "else" => false
  | _ => true

public def Ident.toUnreservedString? : Ident → Option String
  | .idIdent s _ => if (Unreserved? s) then some s else none
  | _ => none

/-- Convert an identifier to its string form, accepting variable/keyword
    identifiers that are valid as (parts of) entity-type names but rejecting
    the reserved keywords (`true`, `false`, `in`, `has`, `like`, `is`, `if`,
    `then`, `else`). Shared by the translator (`Name.toAName?`) and the
    evaluator. -/
public def Ident.toUnrestrictedString? : Ident → Option String
  | .idPrincipal => some "principal"
  | .idAction => some "action"
  | .idResource => some "resource"
  | .idContext => some "context"
  | .idPermit => some "permit"
  | .idForbid => some "forbid"
  | .idWhen => some "when"
  | .idUnless => some "unless"
  | .idIdent s _ => some s
  | _ => none

/-- Convert a CST name to an AST entity-type `Name`, failing if any component
    is a reserved keyword. Shared by the translator and the evaluator. -/
public def Name.toAName? (n : Name) : Option Spec.Name := do
  let id ← Ident.toUnrestrictedString? n.name
  let path ← n.path.mapM Ident.toUnrestrictedString?
  some {id := id, path := path}

/-- Classify a bare (unqualified) CST name as a reserved AST variable. Shared by
    the translator and the evaluator. -/
public def Name.toVar? (n : Name) : Option Spec.Var :=
  if !n.path.isEmpty then none
  else match n.name with
    | .idPrincipal => some .principal
    | .idAction => some .action
    | .idResource => some .resource
    | .idContext => some .context
    | _ => none

public def Ident.toEffect? : Ident → Option Spec.Effect
  | .idPermit => some .permit
  | .idForbid => some .forbid
  | _ => none

public def Ident.toConditionKind? : Ident → Option Spec.ConditionKind
  | .idWhen => some .when
  | .idUnless => some .unless
  | _ => none

public def Expr.toStringLiteral? : Expr → Option String
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
      | .rIsIn _ _ _ => none

public def Expr.toUnescapedStringLiteral? (e : Expr) : Option String := do
  let s ← Expr.toStringLiteral? e
  unescape? s

public def String.toExtFun? : String → Option Spec.ExtFun
  | "decimal" => some .decimal
  | "lessThan" => some .lessThan
  | "lessThanOrEqual" => some .lessThanOrEqual
  | "greaterThan" => some .greaterThan
  | "greaterThanOrEqual" => some .greaterThanOrEqual
  | "ip" => some .ip
  | "isIpv4" => some .isIpv4
  | "isIpv6" => some .isIpv6
  | "isLoopback" => some .isLoopback
  | "isMulticast" => some .isMulticast
  | "isInRange" => some .isInRange
  | "datetime" => some .datetime
  | "duration" => some .duration
  | "offset" => some .offset
  | "durationSince" => some .durationSince
  | "toDate" => some .toDate
  | "toTime" => some .toTime
  | "toMilliseconds" => some .toMilliseconds
  | "toSeconds" => some .toSeconds
  | "toMinutes" => some .toMinutes
  | "toHours" => some .toHours
  | "toDays" => some .toDays
  | _ => none

public def String.toMethodOp? : String → Option (Spec.BinaryOp ⊕ Spec.UnaryOp)
  | "contains" => some (.inl .contains)
  | "containsAll" => some (.inl .containsAll)
  | "containsAny" => some (.inl .containsAny)
  | "getTag" => some (.inl .getTag)
  | "hasTag" => some (.inl .hasTag)
  | "isEmpty" => some (.inr .isEmpty)
  | _ => none



-- Only Literal.liStr s is allowed
-- Mirrors the translator's `Cst.AddExpr.toPattern?`: the unary `op` may be
-- `none` or `some (.nDash 0)` (a structural no-op that the translator allows).
public def AddExpr.toPatternString? (e : AddExpr) : Option String :=
  if !e.extended.isEmpty then none else
  let mult := e.initial
  if !mult.extended.isEmpty then none else
  let unary := mult.initial
  match unary.op with
  | some (.nDash 0) | none =>
    let member := unary.item
    if !member.access.isEmpty then none else
    let item := member.item
    match item with
    | .literal (.liStr s) => some s
    | _ => none
  | some _ => none

-- Extracts an EntityType (Spec.Name) from an AddExpr that is a bare name.
public def AddExpr.toEntityTypeName? (e : AddExpr) : Option Spec.EntityType :=
  if !e.extended.isEmpty then none else
  let mult := e.initial
  if !mult.extended.isEmpty then none else
  let unary := mult.initial
  match unary.op with
  | some (.nDash 0) | none =>
    let member := unary.item
    if !member.access.isEmpty then none else
    match member.item with
    | .name n => match n.toVar? with
      | some _ => none
      | none   => Name.toAName? n
    | _ => none
  | some _ => none

-- When the list is all `.field id` with `id` unreserved, return the converted
-- list of `Attr`s. Otherwise return `none`. Matches the translator's
-- `constructAttrsAux?` filter.
public def fieldChain? : List MemAccess → Option (List Spec.Attr)
  | [] => some []
  | .field id :: xs => do
      let head ← Ident.toUnreservedString? id
      let tail ← fieldChain? xs
      some (head :: tail)
  | _ :: _ => none

/-- Attribute name of a `Primary` used as a record key. -/
public def Primary.toAttr? (p : Primary) : Option Spec.Attr :=
  match p with
  | .literal (.liStr s)              => unescape? s
  | .name { path := [], name := id } => Ident.toUnrestrictedString? id
  | _                                => none

/-- Extract a record-key attribute name from a CST expression, without
    translating it: the key must be a "bare" primary (no operators other than a
    no-op `-0`, no extended chains, no member accesses) that is a string literal
    or an identifier name.  This matches the keys the translator accepts. -/
public def Expr.toAttr? (e : Expr) : Option Spec.Attr :=
  match e with
  | .expr ⟨.edIf _ _ _⟩ => none
  | .expr ⟨.edOr o⟩ =>
    if !o.extended.isEmpty || !o.initial.extended.isEmpty then none
    else match o.initial.initial with
      | .rCommon ae ext =>
        if !ext.isEmpty || !ae.extended.isEmpty || !ae.initial.extended.isEmpty
            || !ae.initial.initial.item.access.isEmpty then none
        else match ae.initial.initial.op with
          | none            => Primary.toAttr? ae.initial.initial.item.item
          | some (.nDash 0) => Primary.toAttr? ae.initial.initial.item.item
          | _               => none
      | _ => none

-- Head string for a name appearing at the start of a `has` field chain.
-- Mirrors the translator's two paths:
--   * `.var v` arm (when `n.toVar? = some v`): use `v.toString` directly,
--     allowing the four var idents through without an unreserved check.
--   * `.name an` arm (when `n.toVar? = none`): filter via `toUnreservedId?`,
--     accepting only `.idIdent s` with `s` unreserved.
public def Ident.toHasHead? : Cst.Ident → Option String
  | .idPrincipal => some "principal"
  | .idAction    => some "action"
  | .idResource  => some "resource"
  | .idContext   => some "context"
  | .idIdent s _   => if Unreserved? s then some s else none
  | _            => none

public def AddExpr.toAttrs? (e : AddExpr) : Option (List Spec.Attr) :=
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
        -- Apply unescape? to mirror the translator's `(unescape? lit).map .inl`.
        if fields.isEmpty then (unescape? s).map (fun s' => [s'])
        else none
      | .literal _ => none
      | .name { path := [], name := id } =>
        -- Mirror the translator's combined `.var v` / `.name n` arms via
        -- the helper above.
        match Ident.toHasHead? id with
        | some idStr => some (idStr :: fields)
        | none       => none
      | .name _ => none
      | _ => none

-- Helper lemma: a `Primary` reachable through the AddExpr→Primary chain
-- has strictly smaller `sizeOf` than the surrounding `OrExpr`.
public theorem sizeOf_addExpr_primary_lt_orExpr (o : OrExpr) (ae : AddExpr) (ext : List (RelOp × AddExpr))
    (h : o.initial.initial = .rCommon ae ext) :
    sizeOf ae.initial.initial.item.item < sizeOf o := by
  obtain ⟨ae_mult, ae_ext⟩ := ae
  obtain ⟨ae_unary, ae_mult_ext⟩ := ae_mult
  obtain ⟨ae_op, ae_member⟩ := ae_unary
  obtain ⟨ae_prim, ae_access⟩ := ae_member
  obtain ⟨o_and, o_ext⟩ := o
  obtain ⟨o_rel, o_and_ext⟩ := o_and
  simp_all
  omega

mutual
public def Primary.uidTypes? : Primary → Option (Spec.Name ⊕ List Spec.Name)
  | .literal _ | .name _ | .slot _ => none
  | .ref r => match r with
    | .uid path (.string s) => do
      let ty ← path.toAName?
      let _ ← unescape? s
      some (.inl ty)
    | .ref _ _ => none
  | .expr e => e.uidTypes?
  | .eList es => do
    let tys ← es.attach.mapM (fun ⟨x, hmem⟩ =>
      have : sizeOf x < sizeOf es := List.sizeOf_lt_of_mem hmem
      match x.uidTypes? with
      | some (.inl ty) => some ty
      | _ => none)
    some (.inr tys)
  | .rInits _ => none
termination_by p => (sizeOf p, 0)
decreasing_by all_goals (simp_wf; omega)

public def Expr.uidTypes? : Expr → Option (Spec.Name ⊕ List Spec.Name)
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
          ae.initial.initial.item.item.uidTypes?
      | .rIsIn _ _ _ => none
termination_by e => (sizeOf e, 1)
decreasing_by all_goals (simp_wf; omega)
end

/-- Structural check that `e` denotes a single bare entity-UID reference
    (mirrors the translator's `toEntityUID?` succeeding). -/
public def Expr.isSingleUID? (e : Expr) : Bool :=
  match e.uidTypes? with
  | some (.inl _) => true
  | _             => false

/-- Validity of a principal/resource scope clause, mirroring `toPRScope?`. -/
public def VariableDef.prScopeValid? (v : VariableDef) : Bool :=
  match v.ineq, v.entityType with
  | none, none => true
  | some (op, e), _ => match op, v.entityType with
    | .rEq, none   => e.isSingleUID?
    | .rEq, some _ => false
    | .rIn, none   => e.isSingleUID?
    | .rIn, some t => e.isSingleUID? && t.toEntityTypeName?.isSome
    | _, _         => false
  | none, some t => t.toEntityTypeName?.isSome

/-- Validity of an action scope clause, mirroring `toActionScope?`
    (= `toActionScopeAux?` filtered by `containsOnlyActionTypes?`). -/
public def VariableDef.actionScopeValid? (v : VariableDef) : Bool :=
  v.entityType.isNone &&
  (match v.ineq with
   | none => true
   | some (op, e) => match op with
     | .rEq => match e.uidTypes? with
       | some (.inl ty) => ty.id == "Action"
       | _              => false
     | .rIn => match e.uidTypes? with
       | some (.inl ty)  => ty.id == "Action"
       | some (.inr tys) => tys.all (fun ty => ty.id == "Action")
       | none            => false
     | _ => false)

/-- Structural validity of a policy's scope: exactly a `principal`, `action`,
    `resource` triple in that order, each with a translatable clause. Mirrors
    the translator's `extractScope?` (kept in agreement in the Thm layer), but
    returns only validity — never builds the AST scope. -/
public def scopeValid? (vars : List VariableDef) : Bool :=
  match vars with
  | [a, b, c] =>
    (match a.var with | .idPrincipal => true | _ => false) && a.prScopeValid? &&
    (match b.var with | .idAction => true | _ => false) && b.actionScopeValid? &&
    (match c.var with | .idResource => true | _ => false) && c.prScopeValid?
  | _ => false

end Cedar.Frontend.Cst
