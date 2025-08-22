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

import Cedar.Spec
import Cedar.SymCC.Encoder
import Cedar.SymCC.Interpretation
import Cedar.Validation
import Std.Internal.Parsec.Basic

/-!
This file functions for parsing SMT models produced by CVC5, and turning them
into `Interpretation`s, which can then be used to construct concrete
counterexamples for property violations (i.e., Cedar requests and entities).

The included parser recognizes the subset of SMTLib syntax that can appear in a
model of a formula emitted by `SymCC.Encoder`.

See also Appendix B of https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-04-09.pdf
-/

namespace Cedar.SymCC.Decoder

open Std.Internal.Parsec String Batteries
open Cedar.Spec Cedar.Validation Cedar.Data

----- Parsing functions for SMTLib syntax -----

def «(» : Parser Unit := do skipChar '(' ; ws

def «)» : Parser Unit := do skipChar ')' ; ws

def trim {α} (arg : α) : Parser α := do ws ; pure arg

def parseSymbol : Parser String := do
  simple <|> quoted
where
  isSimpleSymbolChar (c : Char) :=
    c.isAlphanum || "+-/*=%?!.$_˜&ˆ<>@".contains c
  simple := do
    let s₁ ← many1Chars (satisfy λ c => isSimpleSymbolChar c && !c.isDigit)
    let s₂ ← manyChars (satisfy isSimpleSymbolChar)
    trim (s₁ ++ s₂)
  quoted := do
    skipChar '|'
    let s ← manyChars (satisfy λ c => c != '|' && c != '\\')
    skipChar '|'
    trim s!"|{s}|"

def parseNat : Parser Nat := do trim (← digits)

/--
This function decodes a string encoded in SMT-LIB 2 format
as a Rust string.

It handles two escape sequences:
- Parser-level escape sequence `""` (which represents `"`)
  (per https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf)
- Theory-level escape sequence for Unicode characters:
  convert any of the following to the corresponding Unicode character
  (see https://smt-lib.org/theories-UnicodeStrings.shtml):
  - \ud₃d₂d₁d₀
  - \u{d₀}
  - \u{d₁d₀}
  - \u{d₂d₁d₀}
  - \u{d₃d₂d₁d₀}
  - \u{d₄d₃d₂d₁d₀}

See also:
- The (right) inverse: `encodeString` (not verified)
- The concrete C++ implementation in cvc5, which this function mimics
  https://github.com/cvc5/cvc5/blob/b78e7ed23348659db52a32765ad181ae0c26bbd5/src/util/string.cpp#L136
-/
def parseString : Parser String := do
  skipChar '"'
  let mut s := ""
  repeat
    match ← any with
    | '\\' =>
      let c ← unicodeEscapeBrace <|>
              unicodeEscapeNoBrace <|>
              (return '\\')
      s := s ++ c.toString
    | '"' =>
      match ← peek? with
      | .some '"' => s := s ++ (← pchar '"').toString
      | _         => break
    | c => s := s ++ c.toString
  trim s
where
  -- Parses a hex digit and returns its numeric value
  hex : Parser Nat := do
    let c ← any
    if '0' ≤ c ∧ c ≤ '9' then return c.toNat - '0'.toNat
    else if 'a' ≤ c ∧ c ≤ 'f' then return c.toNat - 'a'.toNat + 10
    else if 'A' ≤ c ∧ c ≤ 'F' then return c.toNat - 'A'.toNat + 10
    else fail s!"hex digit expected"
  -- Parses `ud₃d₂d₁d₀`
  unicodeEscapeNoBrace : Parser Char := attempt do
    skipChar 'u'
    let d₃ ← hex
    let d₂ ← hex
    let d₁ ← hex
    let d₀ ← hex
    return Char.ofNat (d₃ * 16^3 + d₂ * 16^2 + d₁ * 16 + d₀)
  -- Parses `u{d₁ ⋯ dₙ}`
  unicodeEscapeBrace : Parser Char := attempt do
    skipString "u{"
    let mut c ← hex
    for _ in [:4] do
      match ← optional (attempt hex) with
      | .some d => c := c * 16 + d
      | .none   => break
    skipChar '}'
    if c > Cedar.SymCC.Encoder.smtLibMaxCodePoint then
      fail s!"invalid Unicode code point {c} in SMT-LIB string"
    else
      return Char.ofNat c

def parseBinary : Parser (List Bool) := do
  skipString "#b"
  let s ← many1Chars (satisfy λ c => c = '0' || c = '1')
  trim (s.toList.map (· = '1'))

-- Limited s-expression syntax that CVC5 uses to output models for Cedar formula.
inductive SExpr where
  | bitvec  : ∀ {n}, BitVec n → SExpr
  | numeral : Nat → SExpr
  | string  : String → SExpr
  | symbol  : String → SExpr
  | sexpr   : List SExpr → SExpr
deriving Repr, Inhabited, BEq

partial def SExpr.parse : Parser SExpr := do
  bin <|> num <|> str <|> sym <|> sxp
where
  bin : Parser SExpr := do pure (.bitvec (BitVec.ofBoolListBE (← parseBinary)))
  num : Parser SExpr := do pure (.numeral (← parseNat))
  str : Parser SExpr := do pure (.string (← parseString))
  sym : Parser SExpr := do pure (.symbol (← parseSymbol))
  sxp : Parser SExpr := do
    «(»
    let xs ← many SExpr.parse
    «)»
    pure (.sexpr xs.toList)

----- Decoding functions for SExprs -----

abbrev StringOrd : String → String → Ordering := (compareOfLessAndEq · ·)

abbrev IdMap (α) := RBMap String α StringOrd

abbrev IdMap.ofList {α} : List (String × α) → IdMap α := (List.toRBMap · StringOrd)

structure IdMaps where
  types : IdMap TermType
  vars  : IdMap TermVar
  uufs  : IdMap UUF
  enums : IdMap EntityUID
deriving Repr, Inhabited

def IdMaps.ofEncoderState (enc : EncoderState) : IdMaps :=
  {
    types := IdMap.ofList (enc.types.toList.map swap),
    vars  := IdMap.ofList (enc.terms.toList.filterMap asStrVar?),
    uufs  := IdMap.ofList (enc.uufs.toList.map swap),
    enums := IdMap.ofList (enc.enums.toList.filterMap asStrEnum?).flatten
  }
where
  swap {α β} (p : α × β) : β × α := (p.snd, p.fst)
  asStrVar? : (Term × String) → Option (String × TermVar)
    | (.var v, s) => .some (s, v)
    | _           => .none
  asStrEnum? (enums : EntityType × List String) : Option (List (String × EntityUID)) := do
    let (ety, mems) := enums
    let etyId ← enc.types.find? (.entity ety)
    .some (mems.mapIdx λ i eid => (Encoder.enumId etyId i, ⟨ety, eid⟩))

abbrev Result (α) := Except String α

instance : Coe α (Result α) where
  coe := Except.ok

def SExpr.fail {α β} [Repr α] (expected : String) (actual : α) : Result β :=
  .error s!"expected {expected}, given {reprStr actual}"

partial def SExpr.decodeType (types : IdMap TermType) : SExpr → Result TermType
  | .symbol ty => atomic ty
  | .sexpr xs  => parameterized xs
  | other      => fail "type s-expr" other
where
  atomic : String → Result TermType
    | "Bool"     => TermType.bool
    | "String"   => TermType.string
    | "Decimal"  => TermType.ext .decimal
    | "IPAddr"   => TermType.ext .ipAddr
    | "Duration" => TermType.ext .duration
    | "Datetime" => TermType.ext .datetime
    | other      => -- entity or record type
      match types.find? other with
      | .some ty => ty
      | .none    => fail "atomic type name" other
  parameterized : List SExpr → Result TermType
    | [.symbol "_", .symbol "BitVec", .numeral n] => TermType.bitvec n
    | [.symbol "Option", x]                       => do TermType.option (← x.decodeType types)
    | [.symbol "Set", x]                          => do TermType.set (← x.decodeType types)
    | other                                       => fail "BitVec, Option, or Set" other

partial def SExpr.decodeLit (ids : IdMaps) : SExpr → Result Term
  | .bitvec bv      => Term.bitvec bv
  | .string s       => Term.string s
  | .symbol "true"  => Term.bool true
  | .symbol "false" => Term.bool false
  | .symbol e       => enumOrEmptyRecord e
  | .sexpr xs       => construct xs
  | other           => fail "literal expr" other
where
  enumOrEmptyRecord (s : String) : Result Term :=
    match ids.enums.find? s with
    | .some uid => Term.entity uid
    | .none     => constructEntityOrRecord s []
  constructEntityOrRecord tyId args : Result Term := do
    match ids.types.find? tyId, args with
    | .some (.entity ety), [SExpr.string eid] =>
      Term.entity ⟨ety, eid⟩
    | .some (.record (Map.mk rty)), _ =>
      let ts ← args.mapM (SExpr.decodeLit ids)
      if rty.length != ts.length then
        fail s!"record literal args of length {rty.length}" args
      for aty in rty, t in ts do
        if t.typeOf != aty.snd then
          fail s!"attribute {aty.fst} of type {reprStr aty.snd}" t
      let ats := rty.zipWith (λ (a, _) t => (a, t)) ts
      Term.record (Map.mk ats)
    | _, _  =>
        fail "entity or record literal" ((.symbol tyId) :: args)
  construct : List SExpr → Result Term
    | [.symbol "as", .symbol "none", oty] => do
      match (← oty.decodeType ids.types) with
      | .option ty => Term.none ty
      | other      => fail "option type" other
    | [.sexpr [.symbol "as", .symbol "some", oty], x] => do
      let t := Term.some (← x.decodeLit ids)
      let ty ← oty.decodeType ids.types
      if t.typeOf != ty then
        fail s!"term of type {reprStr ty}" t
      t
    | [.symbol "as", .symbol "set.empty", sty] => do
      match ← sty.decodeType ids.types with
      | .set ty => Term.set Set.empty ty
      | other   => fail "set type" other
    | [.symbol "set.singleton", x] => do
      let t ← x.decodeLit ids
      Term.set (Set.singleton t) t.typeOf
    | [.symbol "set.union", x₁, x₂] => do
      match ← x₁.decodeLit ids, ← x₂.decodeLit ids with
      | .set ts₁ ty, .set ts₂ _ => Term.set (ts₁ ∪ ts₂) ty
      | t₁, t₂                  => fail "sets" [t₁, t₂]
    | [.symbol "Decimal", @SExpr.bitvec 64 bv]  =>
      Term.ext (.decimal (Int64.ofBitVec bv))
    | [.symbol "Duration", @SExpr.bitvec 64 bv] =>
      Term.ext (.duration ⟨Int64.ofBitVec bv⟩)
    | [.symbol "Datetime", @SExpr.bitvec 64 bv] =>
      Term.ext (.datetime ⟨Int64.ofBitVec bv⟩)
    | [.symbol "V4", @SExpr.bitvec 32 a, opt] => do
      match (← opt.decodeLit ids) with
      | .some (.prim (@TermPrim.bitvec 5 p)) => Term.ext (.ipaddr (.V4 ⟨a, p⟩))
      | .none (.bitvec 5)                    => Term.ext (.ipaddr (.V4 ⟨a, .none⟩))
      | other                                => fail "Option (BitVec 5)" other
    | [.symbol "V6", @SExpr.bitvec 128 a, opt] => do
      match (← opt.decodeLit ids) with
      | .some (.prim (@TermPrim.bitvec 7 p)) => Term.ext (.ipaddr (.V6 ⟨a, p⟩))
      | .none (.bitvec 7)                    => Term.ext (.ipaddr (.V6 ⟨a, .none⟩))
      | other                                => fail "Option (BitVec 7)" other
    | (.symbol tyId) :: xs => constructEntityOrRecord tyId xs
    | other =>
      fail "literal expr" other

partial def SExpr.decodeUnaryFunctionTable (arg : String) (ids : IdMaps) : SExpr → Result ((List (Term × Term)) × Term)
  | .sexpr [.symbol "ite", .sexpr [.symbol "=", condExpr, .symbol v], thenExpr, elseExpr] => do
    if v != arg then
      fail arg v
    let condTerm ← condExpr.decodeLit ids
    let thenTerm ← thenExpr.decodeLit ids
    let (elseTable, dflt) ← elseExpr.decodeUnaryFunctionTable arg ids
    .ok ((condTerm, thenTerm) :: elseTable, dflt)
  | other => do
    .ok ([], ← other.decodeLit ids)

def SExpr.decodeVarBinding (v : TermVar) (ids : IdMaps) : List SExpr → Result Term
  | [.sexpr [], tyExpr, vExpr] => do
    let ty ← tyExpr.decodeType ids.types
    if ty != v.ty then
      fail s!"type {reprStr v.ty}" ty
    vExpr.decodeLit ids
  | other                      => fail "variable binding" other

def SExpr.decodeUUFBinding (f : UUF) (ids : IdMaps) : List SExpr → Result UDF
  | [.sexpr [.sexpr [.symbol v, inTyExpr]], outTyExpr, tblExpr] => do
    let tyᵢ ← inTyExpr.decodeType ids.types
    let tyₒ ← outTyExpr.decodeType ids.types
    if tyᵢ != f.arg then
      fail s!"type {reprStr f.arg}" tyᵢ
    if tyₒ != f.out then
      fail s!"type {reprStr f.out}" tyₒ
    let (tbl, dflt) ← tblExpr.decodeUnaryFunctionTable v ids
    .ok ⟨tyᵢ, tyₒ, Map.make tbl, dflt⟩
  | other                      => fail "UUF binding" other

abbrev VarMap := RBMap TermVar Term (compareOfLessAndEq · ·)
abbrev UUFMap := RBMap UUF UDF (compareOfLessAndEq · ·)

def SExpr.decodeModel (ids : IdMaps) : SExpr → Result (VarMap × UUFMap)
  | .sexpr bindings => do
    let mut vars : List (TermVar × Term) := []
    let mut uufs : List (UUF × UDF) := []
    for binding in bindings do
      match binding with
      | .sexpr ((.symbol "define-fun") :: (.symbol id) :: xs) =>
        if let .some v := ids.vars.find? id then
          vars := (v, (← SExpr.decodeVarBinding v ids xs)) :: vars
        else if let .some f := ids.uufs.find? id then
          uufs := (f, (← SExpr.decodeUUFBinding f ids xs)) :: uufs
        else
          fail "valid variable or UUF id" id
      | other =>
        fail "define-fun" other
    (vars.toRBMap (compareOfLessAndEq · ·), uufs.toRBMap (compareOfLessAndEq · ·))
  | other =>
    fail "model (list of define-fun)" other

----- Functions for constructing Interpretations from models -----

def defaultExt : ExtType → TermPrim
  | .decimal  => .ext (.decimal (Int64.ofBitVec 0#64))
  | .datetime => .ext (.datetime ⟨Int64.ofBitVec 0#64⟩)
  | .duration => .ext (.duration ⟨Int64.ofBitVec 0#64⟩)
  | .ipAddr   => .ext (.ipaddr (.V4 ⟨0#32, .none⟩))

def defaultPrim (eidOf : EntityType → String) : TermPrimType → TermPrim
  | .bool       => .bool false
  | .bitvec n   => .bitvec 0#n
  | .string     => .string ""
  | .entity ety => .entity ⟨ety, eidOf ety⟩
  | .ext xty    => defaultExt xty

def defaultLit (eidOf : EntityType → String) : TermType → Term
  | .prim pty            => .prim (defaultPrim eidOf pty)
  | .option ty           => .none ty
  | .set ty              => .set Set.empty ty
  | .record (Map.mk tys) =>
    let ts := tys.attach₂.map λ ⟨(a, ty), _⟩ => (a, defaultLit eidOf ty)
    .record (Map.mk ts)
termination_by ty => sizeOf ty
decreasing_by simp_wf ; simp at * ; omega

def defaultUDF (eidOf : EntityType → String) (f : UUF) : UDF :=
  ⟨f.arg, f.out, Map.empty, defaultLit eidOf f.out⟩

def eidOfForEntities (εs : SymEntities) (ety : EntityType) : String :=
  match εs.find? ety with
  | .some ⟨_, _, .some (Set.mk (eid :: _)), _⟩ => eid
  | _                                          => ""

def defaultInterpretation (εs : SymEntities) : Interpretation :=
  let eidOf := (eidOfForEntities εs)
  {
    vars := λ v => defaultLit eidOf v.ty,
    funs := λ f => defaultUDF eidOf f,
    partials := λ t => defaultLit eidOf t.typeOf
  }

/--
Returns an Interpretation that corresponds to the given `model`, generated by
CVC5 for a formula emitted by the encoder. This function assumes the EncoderSate
`enc` is produced by the encoder when applied to a set of terms `ts` and the
environment `εnv`. If `εnv` is well-formed, the terms `ts` are well-formed with
respect to `εnv.entities`, and CVC5 is sound, the the resulting Interpretation
satisfies `ts` and is well-formed with respect to `εnv.entities`.
-/
def decode (model : String) (enc : EncoderState) : Result Interpretation := do
  let x ← SExpr.parse |>.run model
  let ⟨vars, uufs⟩ ← x.decodeModel (IdMaps.ofEncoderState enc)
  let eidOf := λ ety =>
    match enc.enums.find? ety with
    | .some (eid :: _) => eid
    | _                => ""
  .ok {
    vars := λ v =>
      match vars.find? v with
      | .some t => t
      | .none   => defaultLit eidOf v.ty,
    funs := λ f =>
      match uufs.find? f with
      | .some d => d
      | .none   => defaultUDF eidOf f,
    partials := λ t =>
      defaultLit eidOf t.typeOf
  }


namespace Cedar.SymCC.Decoder
