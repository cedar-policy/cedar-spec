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

import Cedar.Frontend.Cst
import Std.Internal.Parsec.String

/-! This file defines a parser from Cedar policy text to the CST. -/

/-- Parses a character into a `Nat` number, assuming the character is the hex reprsentation of
that natural number. -/
def Char.asHexNat (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
    else .error s!"invalid hex digit: '{c}'"

/-- Parses a string into a `Nat` number, assuming the string is the hex representation of that
    natural number. -/
def String.asHexNat (s : String) : Except String Nat :=
  if s.isEmpty then .error "empty hex string"
  else if s.length > 6 then .error "hex string too long"
  else s.foldl (fun acc c => do
    let n ← acc
    let d ← c.asHexNat
    .ok (n * 16 + d)) (.ok 0)

namespace Except
open Std.Internal.Parsec String
def liftParser (r: Except String α) : Parser α :=
  match r with
  |.ok a => pure a
  |.error s => fail s
end Except

namespace Cedar.Spec.Cst.Parser

open Std.Internal.Parsec String

----- Utilities -----

/-- Skip whitespace and `//` line comments -/
partial def wsAndComments : Parser Unit := do
  ws
  if (← (attempt (skipString "//") *> pure true) <|> pure false) then
    skipLine
    wsAndComments
where
  skipLine : Parser Unit := do
    repeat
      match ← peek? with
      | none => return ()
      | some '\n' => skip ; return ()
      | some _ => skip

/-- Run a parser, then consume trailing whitespace/comments -/
@[inline] def tok {α : Type} (p : Parser α) : Parser α := do
  let a ← p ; wsAndComments ; return a

/-- Parse and skip a specific character, then whitespace -/
@[inline] def char' (c : Char) : Parser Unit := tok (skipChar c)

/-- Parse and skip a specific string, then whitespace -/
@[inline] def str' (s : String) : Parser Unit := tok (skipString s)

----- Identifiers -----

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

private def isIdentCont (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Parse a raw identifier string -/
private def rawIdent : Parser String := tok do
  let c ← satisfy isIdentStart
  let rest ← manyChars (satisfy isIdentCont)
  return String.ofList (c :: rest.toList)

/-- Classify a raw identifier string into an `Ident` -/
private def classifyIdent (s : String) : Ident :=
  match s with
  | "principal" => .idPrincipal
  | "action"    => .idAction
  | "resource"  => .idResource
  | "context"   => .idContext
  | "true"      => .idTrue
  | "false"     => .idFalse
  | "permit"    => .idPermit
  | "forbid"    => .idForbid
  | "when"      => .idWhen
  | "unless"    => .idUnless
  | "in"        => .idIn
  | "has"       => .idHas
  | "like"      => .idLike
  | "is"        => .idIs
  | "if"        => .idIf
  | "then"      => .idThen
  | "else"      => .idElse
  | s           => .idIdent s

/-- Parse an identifier -/
def parseIdent : Parser Ident := do
  return classifyIdent (← rawIdent)

/-- Expect a specific keyword -/
def keyword (s : String) : Parser Unit := do
  let i ← rawIdent
  if i != s then fail s!"expected '{s}', got '{i}'"

/-- Try to consume a keyword; return true if successful -/
def tryKeyword (s : String) : Parser Bool :=
  (attempt (keyword s) *> pure true) <|> pure false


----- Literals -----

/-- Parse a natural number -/
private def parseNat : Parser UInt64 := tok do
  let s ← many1Chars (satisfy Char.isDigit)
  match s.toNat? with
  | some n => return n.toUInt64
  | none => fail s!"invalid number: {s}"

/-- Parse a string literal (double-quoted, with escape sequences) -/
private partial def stringLit : Parser String := do
  skipChar '"'
  stringLitBody ""
where
  stringLitBody (s : String) : Parser String := do
    match ← any with
    | '"' =>
      wsAndComments
      return s
    | '\\' =>
      let c ← any
      let s ← match c with
        | 'n'  => pure (s.push '\n')
        | 'r'  => pure (s.push '\r')
        | 't'  => pure (s.push '\t')
        | '\\' => pure (s.push '\\')
        | '"'  => pure (s.push '"')
        | '\'' => pure (s.push '\'')
        | '0'  => pure (s.push '\x00')
        | 'x'  => do
          --
          let h ← hexDigit
          let l ← hexDigit
          let n := h * 16 + l
          pure (s.push (Char.ofNat n))
        | 'u'  => do
          skipChar '{'
          -- get all digits until next }
          let n ← do (← manyChars (satisfy fun c => c != '}')).asHexNat.liftParser
          skipChar '}'
          pure (s.push (Char.ofNat n))
        | c    => pure (s.push '\\' |>.push c)
      stringLitBody s
    | c => stringLitBody (s.push c)
  hexDigit : Parser Nat := do (← any).asHexNat.liftParser

/-- Parse a literal -/
def parseLiteral : Parser Literal :=
  (Literal.liStr <$> stringLit) <|>
  (Literal.liNum <$> parseNat) <|>
  (attempt (keyword "true") *> pure .liTrue) <|>
  (attempt (keyword "false") *> pure .liFalse)

----- RelOp parsing -----

private def tryRelOp : Parser (Option RelOp) :=
  (attempt (str' "<=" *> pure (some RelOp.rLessEq))) <|>
  (attempt (str' ">=" *> pure (some RelOp.rGreaterEq))) <|>
  (attempt (str' "!=" *> pure (some RelOp.rNotEq))) <|>
  (attempt (str' "==" *> pure (some RelOp.rEq))) <|>
  (attempt (do
    skipChar '<'
    notFollowedBy (satisfy (· == '='))
    wsAndComments
    pure (some RelOp.rLess))) <|>
  (attempt (do
    skipChar '>'
    notFollowedBy (satisfy (· == '='))
    wsAndComments
    pure (some RelOp.rGreater))) <|>
  (attempt (keyword "in" *> pure (some RelOp.rIn))) <|>
  pure none

----- Expression parsing (mutually recursive) -----

mutual

partial def expr : Parser Expr := do
  let ite ← (attempt do
    keyword "if"
    let cond ← expr
    keyword "then"
    let thenE ← expr
    keyword "else"
    let elseE ← expr
    return Expr.expr { expr := .edIf cond thenE elseE }
  ) <|> do
    let o ← orExpr
    return Expr.expr { expr := .edOr o }
  return ite

partial def orExpr : Parser OrExpr := do
  let initial ← andExpr
  let mut extended : List AndExpr := []
  while (← (attempt (str' "||") *> pure true) <|> pure false) do
    extended := extended ++ [← andExpr]
  return { initial, extended }

partial def andExpr : Parser AndExpr := do
  let initial ← relation
  let mut extended : List Relation := []
  while (← (attempt (str' "&&") *> pure true) <|> pure false) do
    extended := extended ++ [← relation]
  return { initial, extended }

partial def relation : Parser Relation := do
  let target ← addExpr
  (attempt (do
    keyword "has"
    let field ← addExpr
    return Relation.rHas target field
  )) <|> (attempt (do
    keyword "like"
    let pattern ← addExpr
    return Relation.rLike target pattern
  )) <|> (attempt (do
    keyword "is"
    let entityType ← addExpr
    let inEntity ← if (← tryKeyword "in") then some <$> addExpr else pure none
    return Relation.rIsIn target entityType inEntity
  )) <|> do
    let mut items : List (RelOp × AddExpr) := []
    while true do
      match ← tryRelOp with
      | some op =>
        let rhs ← addExpr
        items := items ++ [(op, rhs)]
      | none => break
    return Relation.rCommon target items

partial def addExpr : Parser AddExpr := do
  let initial ← multExpr
  let mut extended : List (AddOp × MultExpr) := []
  while true do
    let op ← (attempt (char' '+' *> pure (some AddOp.aPlus))) <|>
              (attempt (char' '-' *> pure (some AddOp.aMinus))) <|>
              pure none
    match op with
    | some o =>
      let rhs ← multExpr
      extended := extended ++ [(o, rhs)]
    | none => break
  return { initial, extended }

partial def multExpr : Parser MultExpr := do
  let initial ← unary
  let mut extended : List (MultOp × Unary) := []
  while true do
    let op ← (attempt (char' '*' *> pure (some MultOp.mTimes))) <|>
              (attempt (char' '/' *> pure (some MultOp.mDivide))) <|>
              (attempt (char' '%' *> pure (some MultOp.mMod))) <|>
              pure none
    match op with
    | some o =>
      let rhs ← unary
      extended := extended ++ [(o, rhs)]
    | none => break
  return { initial, extended }

partial def unary : Parser Unary := do
  match ← peek? with
  | some '!' =>
    let n ← countChar '!'
    let m ← member
    return { op := some (.nBang n), item := m }
  | some '-' =>
    let n ← countChar '-'
    let m ← member
    return { op := some (.nDash n), item := m }
  | _ =>
    let m ← member
    return { op := none, item := m }
where
  countChar (c : Char) : Parser UInt8 := do
    let mut n : UInt8 := 0
    while (← (attempt (skipChar c *> pure true)) <|> pure false) do
      n := n + 1
    wsAndComments
    return n

partial def member : Parser Member := do
  let item ← primary
  let mut access : List MemAccess := []
  while true do
    let acc ←
      (attempt (do
        char' '.'
        let i ← parseIdent
        return some (MemAccess.field i))) <|>
      (attempt (do
        char' '('
        let args ← exprListUntil ')'
        char' ')'
        return some (MemAccess.call args))) <|>
      (attempt (do
        char' '['
        let e ← expr
        char' ']'
        return some (MemAccess.index e))) <|>
      pure none
    match acc with
    | some a => access := access ++ [a]
    | none => break
  return { item, access }

partial def primary : Parser Primary := do
  match ← peek? with
  | some '"' => return .literal (.liStr (← stringLit))
  | some '?' =>
    skip
    let s ← rawIdent
    return .slot (.string s)
  | some '(' =>
    char' '('
    let e ← expr
    char' ')'
    return .expr e
  | some '[' =>
    char' '['
    let es ← exprListUntil ']'
    char' ']'
    return .eList es
  | some '{' =>
    char' '{'
    let rs ← recInitsUntil '}'
    char' '}'
    return .rInits rs
  | some c =>
    if c.isDigit then
      return .literal (.liNum (← parseNat))
    else if isIdentStart c then
      refOrNameOrLit
    else
      fail s!"unexpected character '{c}'"
  | none => fail "unexpected end of input"
where
  refOrNameOrLit : Parser Primary :=
    (attempt do
      let n ← parseName
      str' "::"
      match ← peek? with
      | some '"' =>
        let s ← stringLit
        return Primary.ref (.uid n (.string s))
      | some '{' =>
        char' '{'
        let inits ← refInitsUntil '}'
        char' '}'
        return Primary.ref (.ref n inits)
      | _ => fail "expected string or '{' after '::'") <|>
    (do
      let n ← parseName
      match n.path, n.name with
      | [], .idTrue  => return .literal .liTrue
      | [], .idFalse => return .literal .liFalse
      | _, _ => return .name n)
  parseName : Parser Name := do
    let first ← parseIdent
    let mut path : List Ident := []
    let mut last := first
    -- Consume '::' Ident, but not '::' followed by '"' or '{'
    while (← (attempt (do
      skipString "::"
      let c ← peek!
      if c == '"' || c == '{' then fail "ref separator"
      if !(isIdentStart c) then fail "not ident"
      pure true)) <|> pure false) do
      path := path ++ [last]
      last ← parseIdent
    return { path, name := last }
  refInitsUntil (closing : Char) : Parser (List RefInit) := do
    match ← peek? with
    | some c => if c == closing then return [] else refInitList
    | none => return []
  refInitList : Parser (List RefInit) := do
    let first ← parseRefInit
    let mut items := [first]
    while (← (attempt (char' ',') *> pure true) <|> pure false) do
      items := items ++ [← parseRefInit]
    return items
  parseRefInit : Parser RefInit := do
    let id ← parseIdent
    char' ':'
    let lit ← parseLiteral
    return { id, lit }
  recInitsUntil (closing : Char) : Parser (List RecInit) := do
    match ← peek? with
    | some c => if c == closing then return [] else recInitList
    | none => return []
  recInitList : Parser (List RecInit) := do
    let first ← parseRecInit
    let mut items := [first]
    while (← (attempt (char' ',') *> pure true) <|> pure false) do
      items := items ++ [← parseRecInit]
    return items
  parseRecInit : Parser RecInit := do
    let attr ← expr
    char' ':'
    let value ← expr
    return { attr, value }

/-- Parse a comma-separated list of expressions until a closing char -/
partial def exprListUntil (closing : Char) : Parser (List Expr) := do
  match ← peek? with
  | some c => if c == closing then return [] else exprList1
  | none => return []
where
  exprList1 : Parser (List Expr) := do
    let first ← expr
    let mut items := [first]
    while (← (attempt (char' ',') *> pure true) <|> pure false) do
      items := items ++ [← expr]
    return items

end

----- Policy-level parsing -----

/-- Parse a Cond (e.g., `when { expr }` or `unless { expr }`) -/
partial def parseCond : Parser Cond := do
  let kind ← parseCondKeyword
  char' '{'
  let body ← expr
  char' '}'
  return { kind, body }
where
  parseCondKeyword : Parser Ident := do
    let i ← rawIdent
    if i == "when" || i == "unless" then return classifyIdent i
    else fail s!"expected 'when' or 'unless', got '{i}'"

/-- Parse a VariableDef -/
partial def variableDef : Parser VariableDef := do
  let var ← parseIdent
  -- Optional: 'is' Add (entity type constraint)
  let entityType ← if (← tryKeyword "is") then some <$> addExpr else pure none
  -- Optional: RelOp Expr (inequality constraint)
  let ineq ← do
    match ← tryRelOp with
    | some op =>
      let e ← expr
      pure (some (op, e))
    | none => pure none
  return { var, entityType, ineq }

/-- Parse comma-separated variable defs until ')' -/
partial def varDefList : Parser (List VariableDef) := do
  match ← peek? with
  | some ')' => return []
  | _ =>
    let first ← variableDef
    let rest ← varDefListTail
    return first :: rest
where
  varDefListTail : Parser (List VariableDef) := do
    if (← (attempt (char' ',') *> pure true) <|> pure false) then
      let v ← variableDef
      let rest ← varDefListTail
      return v :: rest
    else
      return []

/-- Parse a Policy -/
partial def parsePolicy : Parser Policy := do
  -- Parse annotations
  let mut annotations : List Annotation := []
  while (← (attempt (skipChar '@' *> pure true)) <|> pure false) do
    let name ← parseIdent
    let value ← if (← (attempt (char' '(' *> pure true)) <|> pure false) then
      let s ← stringLit
      char' ')'
      pure (some (.string s))
    else
      pure none
    annotations := annotations ++ [{ name, value }]
  let effect ← parseIdent
  char' '('
  -- Parse variable defs separated by commas
  let vars ← varDefList
  char' ')'
  -- Parse conditions (when/unless blocks)
  let mut conds : List Cond := []
  while true do
    match ← (attempt (parseCond >>= fun c => pure (some c))) <|> pure none with
    | some c => conds := conds ++ [c]
    | none => break
  char' ';'
  return .policy { annotations, effect, vars, conds }

/-- Parse a Policies (sequence of policies) -/
partial def parsePolicies : Parser Policies := do
  wsAndComments
  let mut ps : List Policy := []
  while !(← isEof) do
    ps := ps ++ [← parsePolicy]
  return { ps }

/-- Top-level entry point: parse a string into a `Policies` CST -/
def parse (input : String) : Except String Policies :=
  match (parsePolicies <* eof).run input with
  | .ok res => .ok res
  | .error err => .error err

end Cedar.Spec.Cst.Parser
