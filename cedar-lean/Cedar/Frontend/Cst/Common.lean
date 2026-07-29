
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
public import Cedar.Spec.Wildcard
public import Cedar.Spec.Policy

namespace Cedar.Frontend.Cst

open Cedar


public def Member.toLit? (e : Member) : Option Literal :=
  if !e.access.isEmpty then none else
  match e.item with
  | .literal l => some l
  | _ => none

-- TODO: Review this function, written by Claude

public def hexDigitToNat? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

public def toPatternAux (input : List Char) : Option Spec.Pattern :=
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

public def toPattern? (s : String) : Option Spec.Pattern :=
  toPatternAux s.toList

public def unescapeAux (input : List Char) : Option (List Char) :=
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

public def unescape? (s : String) : Option String := do
  let chars ← unescapeAux s.toList
  some (String.ofList chars)

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

public theorem unreserved_iff_not_in_keywords {s : String} :
    Unreserved? s = true ↔ s ∉ keywords := by
  simp only [Unreserved?, keywords, List.mem_cons, not_or, List.mem_nil_iff,
    not_false_eq_true, and_true]
  constructor
  · intro h
    split at h <;> simp_all
  · intro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩
    split <;> simp_all

public theorem not_in_keywords_unreserved {s : String} (h : s ∉ keywords) :
    Unreserved? s = true :=
  unreserved_iff_not_in_keywords.mpr h

public def Ident.toUnreservedString? : Ident → Option String
  | .idIdent s _ => if (Unreserved? s) then some s else none
  | _ => none

@[simp]
public theorem Ident.toUnreservedString?_idIdent (s : String) (h : s ∉ keywords) :
    Ident.toUnreservedString? (.idIdent s h) = some s := by
  simp [Ident.toUnreservedString?, not_in_keywords_unreserved h]

@[simp]
public theorem Ident.toString_idIdent (s : String) (h : s ∉ keywords) :
    Ident.toString (.idIdent s h) = s := rfl

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

public def String.isFunctionName? : String → Bool
  | "decimal"             ----- Decimal functions -----
  | "lessThan"
  | "lessThanOrEqual"
  | "greaterThan"
  | "greaterThanOrEqual"
  | "ip"                  ----- IpAddr functions -----
  | "isIpv4"
  | "isIpv6"
  | "isLoopback"
  | "isMulticast"
  | "isInRange"
  | "datetime"           ----- Datetime functions -----
  | "duration"
  | "offset"
  | "durationSince"
  | "toDate"
  | "toTime"
  | "toMilliseconds"
  | "toSeconds"
  | "toMinutes"
  | "toHours"
  | "toDays" => true
  | _ => false

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

public def String.isMethodName? : String → Bool
  | "contains"
  | "containsAll"
  | "containsAny"
  | "isEmpty"
  | "getTag"
  | "hasTag" => true
  | _ => false

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

end Cedar.Frontend.Cst
