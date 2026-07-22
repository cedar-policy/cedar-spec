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

import Cedar.Spec
public import Cedar.SymCC.Encoder
public import Cedar.SymCC.Interpretation
import Cedar.Validation
import Std.Internal.Parsec.Basic
import Std.Data.TreeMap

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
open Cedar.Validation Cedar.Data
open Cedar.Spec hiding Result

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

def parseHex : Parser (List Bool) := do
  skipString "#x"
  let s ← many1Chars (satisfy λ c => c.isHexDigit)
  trim (s.toList.flatMap hexDigitToBits)
where
  hexDigitToBits (c : Char) : List Bool :=
    let n := if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
             else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
             else c.toNat - 'A'.toNat + 10
    [n / 8 % 2 == 1, n / 4 % 2 == 1, n / 2 % 2 == 1, n % 2 == 1]

-- Limited s-expression syntax that CVC5 uses to output models for Cedar formula.
inductive SExpr where
  | bitvec  : ∀ {n}, BitVec n → SExpr
  | numeral : Nat → SExpr
  | string  : String → SExpr
  | symbol  : String → SExpr
  | sexpr   : List SExpr → SExpr
deriving Repr, Inhabited, BEq

partial def SExpr.parse : Parser SExpr := do
  bv <|> num <|> str <|> sym <|> sxp
where
  bv : Parser SExpr := do
    pure (.bitvec (BitVec.ofBoolListBE (← parseBinary <|> parseHex)))
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

abbrev IdMap (α) := Std.TreeMap String α StringOrd

abbrev IdMap.ofList {α} : List (String × α) → IdMap α := (Std.TreeMap.ofList · StringOrd)

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
    let etyId ← enc.types.get? (.entity ety)
    .some (mems.mapIdx λ i eid => (Encoder.enumId etyId i, ⟨ety, eid⟩))

public abbrev Result (α) := Except String α

instance : Coe α (Result α) where
  coe := Except.ok

def SExpr.isAppOf (fn : String) : SExpr → Bool
  | .sexpr ((.symbol fn') :: _)  => fn == fn'
  | _ => false

def SExpr.fail {α β} [Repr α] (expected : String) (actual : α) : Result β :=
  .error s!"expected {expected}, but got {reprStr actual}"

def SExpr.decodeType (types : IdMap TermType) : SExpr → Result TermType
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
      match types.get? other with
      | .some ty => ty
      | .none    => fail "atomic type name" other
  parameterized : List SExpr → Result TermType
    | [.symbol "_", .symbol "BitVec", .numeral n] => TermType.bitvec n
    | [.symbol "Option", x]                       => do TermType.option (← x.decodeType types)
    | [.symbol "Set", x]                          => do TermType.set (← x.decodeType types)
    | other                                       => fail "BitVec, Option, or Set" other

mutual

def SExpr.decodeLit (ids : IdMaps) (expectedTy : Option TermType := .none) : SExpr → Result Term
  | .bitvec bv      => Term.bitvec bv
  | .string s       => Term.string s
  | .symbol "true"  => Term.bool true
  | .symbol "false" => Term.bool false
  | .symbol "none"  =>
    match expectedTy with
    | .some (.option ty) => Term.none ty
    | _                  => fail "option type for bare 'none'" expectedTy
  | .symbol e       =>
    match ids.enums.get? e with
    | .some uid => Term.entity uid
    | .none     => SExpr.constructEntityOrRecord ids e []
  | .sexpr xs       => SExpr.decodeLitConstruct ids expectedTy xs
  | other           => fail "literal expr" other
termination_by s => sizeOf s
decreasing_by
  all_goals simp
  simp [sizeOf, String._sizeOf_1] ; omega

private def SExpr.constructEntityOrRecord (ids : IdMaps) (tyId : String) (args : List SExpr) : Result Term := do
  match ids.types.get? tyId with
  | .some (.entity ety) =>
    match args with
    | [SExpr.string eid] => Term.entity ⟨ety, eid⟩
    | _ => fail "entity literal" args
  | .some (.record (Map.mk rty)) =>
    if rty.length != args.length then
      fail s!"record literal args of length {rty.length}" args
    let ts ← (rty.zip args).mapM₁ λ ⟨((_, fieldTy), arg), h⟩ =>
      have : sizeOf arg < sizeOf args :=
        have ⟨_, hb⟩ := List.of_mem_zip h
        List.sizeOf_lt_of_mem hb
      arg.decodeLit ids (.some fieldTy)
    for aty in rty, t in ts do
      if t.typeOf != aty.snd then
        fail s!"attribute {aty.fst} of type {reprStr aty.snd}" t
    let ats := rty.zipWith (λ (a, _) t => (a, t)) ts
    Term.record (Map.mk ats)
  | _ =>
      fail "entity or record literal" ((.symbol tyId) :: args)
termination_by sizeOf args

private def SExpr.decodeLitConstruct (ids : IdMaps) (expectedTy : Option TermType := .none) : List SExpr → Result Term
  | [.symbol "as", .symbol "none", oty] => do
    match (← oty.decodeType ids.types) with
    | .option ty => Term.none ty
    | other      => fail "option type" other
  | [.sexpr [.symbol "as", .symbol "some", oty], x] => do
    let ty ← oty.decodeType ids.types
    let innerTy? := match ty with | .option inner => .some inner | _ => .none
    let t := Term.some (← x.decodeLit ids innerTy?)
    if t.typeOf != ty then
      fail s!"term of type {reprStr ty}" t
    t
  | [.symbol "some", x] => do
    let innerTy := match expectedTy with
    | .some (.option ty) => .some ty
    | _ => .none
    let t ← x.decodeLit ids innerTy
    Term.some t
  | [.symbol "as", .symbol "set.empty", sty] => do
    match ← sty.decodeType ids.types with
    | .set ty => Term.set Set.empty ty
    | other   => fail "set type" other
  | [.symbol "set.singleton", x] => do
    let eltTy := match expectedTy with
    | .some (.set ty) => .some ty
    | _ => .none
    let t ← x.decodeLit ids eltTy
    Term.set (Set.singleton t) t.typeOf
  | [.symbol "set.union", x₁, x₂] => do
    match ← x₁.decodeLit ids expectedTy, ← x₂.decodeLit ids expectedTy with
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
  | [.symbol "_", .symbol bvStr, .numeral w] =>
    if bvStr.startsWith "bv" then
      match (bvStr.drop 2).toNat? with
      | .some val =>
        if w == 0 then fail "non-zero width" w
        else if val >= 2^w then fail s!"value fitting in {w} bits" val
        else Term.bitvec (BitVec.ofNat w val)
      | .none => fail "numeric bv value" bvStr
    else fail "indexed bitvec (_ bvN W)" bvStr
  | (.symbol tyId) :: xs => SExpr.constructEntityOrRecord ids tyId xs
  | other =>
    fail "literal expr" other
termination_by xs => sizeOf xs

end

def SExpr.decodeUnaryFunctionIteTable (arg : String) (ids : IdMaps) (retTy : Option TermType := .none) : SExpr → Result ((List (Term × Term)) × Term)
  | .sexpr [.symbol "ite", .sexpr [.symbol "=", condExpr, .symbol v], thenExpr, elseExpr]
  | .sexpr [.symbol "ite", .sexpr [.symbol "=", .symbol v, condExpr], thenExpr, elseExpr] => do
    if v == arg then
      let condTerm ← condExpr.decodeLit ids
      let thenTerm ← thenExpr.decodeLit ids retTy
      let (elseTable, dflt) ← elseExpr.decodeUnaryFunctionIteTable arg ids retTy
      .ok ((condTerm, thenTerm) :: elseTable, dflt)
    else
      fail arg v
  | other => do
    .ok ([], ← other.decodeLit ids retTy)

def SExpr.decodeUnaryFunctionOrTable (arg : String) (ids : IdMaps) : SExpr → Result ((List (Term × Term)) × Term)
  | .sexpr ((.symbol "or") :: disjuncts) => do
    let trueTerms ← disjuncts.mapM λ d =>
      match d with
      | .sexpr [(.symbol "="), condExpr, .symbol v]
      | .sexpr [(.symbol "="), .symbol v, condExpr] => do
        if v == arg then
          condExpr.decodeLit ids
        else
          fail arg v
      | _ => fail "=" d
    (trueTerms.map λ t => (t, Term.prim (.bool true)), Term.prim (.bool false))
  | other => fail "or" other

def SExpr.decodeUnaryFunctionEqTable (arg : String) (ids : IdMaps) : SExpr → Result ((List (Term × Term)) × Term)
  | .sexpr [(.symbol "="), condExpr, .symbol v]
  | .sexpr [(.symbol "="), .symbol v, condExpr] => do
    if v == arg then
      ([(←condExpr.decodeLit ids, Term.prim (.bool true))], Term.prim (.bool false))
    else
      fail arg v
  | other => fail "=" other

def SExpr.decodeVarBinding (v : TermVar) (ids : IdMaps) : List SExpr → Result Term
  | [.sexpr [], tyExpr, vExpr] => do
    let ty ← tyExpr.decodeType ids.types
    if ty != v.ty then
      fail s!"type {reprStr v.ty}" ty
    vExpr.decodeLit ids (.some ty)
  | other                      => fail "variable binding" other

def SExpr.decodeUUFBinding (f : UUF) (ids : IdMaps) : List SExpr → Result UDF
  | [.sexpr [.sexpr [.symbol v, inTyExpr]], outTyExpr, tblExpr] => do
    let tyᵢ ← inTyExpr.decodeType ids.types
    let tyₒ ← outTyExpr.decodeType ids.types
    if tyᵢ != f.arg then
      fail s!"type {reprStr f.arg}" tyᵢ
    if tyₒ != f.out then
      fail s!"type {reprStr f.out}" tyₒ
    let (tbl, dflt) ←
      if tblExpr.isAppOf "or" then
        tblExpr.decodeUnaryFunctionOrTable v ids
      else if tblExpr.isAppOf "=" then
        tblExpr.decodeUnaryFunctionEqTable v ids
      else
        tblExpr.decodeUnaryFunctionIteTable v ids (.some tyₒ)
    .ok ⟨tyᵢ, tyₒ, Map.make tbl, dflt⟩
  | other                      => fail "UUF binding" other

abbrev VarMap := Std.TreeMap TermVar Term (compareOfLessAndEq · ·)
abbrev UUFMap := Std.TreeMap UUF UDF (compareOfLessAndEq · ·)

def SExpr.decodeModel (ids : IdMaps) : SExpr → Result (VarMap × UUFMap)
  | .sexpr bindings => do
    let mut vars : List (TermVar × Term) := []
    let mut uufs : List (UUF × UDF) := []
    for binding in bindings do
      match binding with
      | .sexpr ((.symbol "define-fun") :: (.symbol id) :: xs) =>
        if let .some v := ids.vars.get? id then
          vars := (v, (← SExpr.decodeVarBinding v ids xs)) :: vars
        else if let .some f := ids.uufs.get? id then
          uufs := (f, (← SExpr.decodeUUFBinding f ids xs)) :: uufs
        else
          pure () -- skip unknown define-funs (e.g., Z3 intermediate terms)
      | other =>
        fail "define-fun" other
    (Std.TreeMap.ofList vars (compareOfLessAndEq · ·), Std.TreeMap.ofList uufs (compareOfLessAndEq · ·))
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

public def defaultLit (eidOf : EntityType → String) : TermType → Term
  | .prim pty   => .prim (defaultPrim eidOf pty)
  | .option ty  => .none ty
  | .set ty     => .set Set.empty ty
  | .record tys => .record (tys.mapOnValues₂ λ ⟨ty, _⟩ => defaultLit eidOf ty)

public def defaultUDF (eidOf : EntityType → String) (f : UUF) : UDF :=
  ⟨f.arg, f.out, Map.empty, defaultLit eidOf f.out⟩

public def eidOfForEntities (εs : SymEntities) (ety : EntityType) : String :=
  match εs.find? ety with
  | .some ⟨_, _, .some (Set.mk (eid :: _)), _⟩ => eid
  | _                                          => ""

public def defaultInterpretation (εs : SymEntities) : Interpretation :=
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
public def decode (model : String) (enc : EncoderState) : Result Interpretation := do
  let x ← SExpr.parse |>.run model
  let ⟨vars, uufs⟩ ← x.decodeModel (IdMaps.ofEncoderState enc)
  let eidOf := λ ety =>
    match enc.enums.get? ety with
    | .some (eid :: _) => eid
    | _                => ""
  .ok {
    vars := λ v =>
      match vars.get? v with
      | .some t => t
      | .none   => defaultLit eidOf v.ty,
    funs := λ f =>
      match uufs.get? f with
      | .some d => d
      | .none   => defaultUDF eidOf f,
    partials := λ t =>
      defaultLit eidOf t.typeOf
  }


namespace Cedar.SymCC.Decoder
