
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

public def Ident.toEffect? : Ident → Option Spec.Effect
  | .idPermit => some .permit
  | .idForbid => some .forbid
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



end Cedar.Frontend.Cst
