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

import Cedar.SymCC.Env
import Cedar.SymCC.Factory
import Cedar.SymCC.Solver
import Batteries.Data.RBMap

/-!
This file defines the Cedar encoder, which translates a list of boolean Terms
into a list of SMT assertions. Term encoding is trusted.

 We will use the following type representations for primitive types:
 * `TermType.bool`:     builtin SMT `Bool` type
 * `TermType.string`:   builtin SMT `String` type
 * `TermType.bitvec n`: builtin SMT `(_ BitVec n)` type

 We will represent non-primitive types as SMT algebraic datypes:
 * `TermType.option T`: a parameterized SMT algebraic datatype of the same name,
   and with the constructors `(some (val T))` and `(none)`. For each constructor
   argument, SMTLib introduces a corresponding (total) selector function. We
   will translate `Term.some` nodes in the Term language as applications of the
   `val` selector function.
 * `TermType.entity E`: we represent Cedar entities of entity type E as values
   of the SMT algebraic datatype E with a single constructor, `(E (eid String))`.
   Each entity type E gets an uninterpreted function `f: E → Record_E` that maps
   instances of E to their attributes.  Similarly, each E
   gets N uninterpreted functions `g₁: E → Set E₁, ..., gₙ: E → Set Eₙ` that map
   each instance of E to its ancestor sets of the given types, as specified by
   the `memberOf` relation in the schema.
 * `TermType.Record (Map Attr TermType)`: we represent each record term type as
   an SMT algebraic datatype with a single constructor. The order of arguments
   to the constructor (the attributes) is important, so we fix that to be the
   lexicographic order on the attribute names of the underlying record type. We
   use the argument selector functions to translate `record.get` applications.
   We can't use raw Cedar attribute names for argument names because they may
   not be valid SMT identifiers. So, we'll keep a mapping from the attribute
   names to their unique SMT ids. In general, we'll name SMT record types as
   "R<i>" where <i> is a natural number and attributes within the record as
   "R<i>a<j>", where <j> is the attribute's position in the constructor argument
   list.

 Similarly to types and attributes, all uninterpreted functions, variables, and
 Terms are mapped to their SMT encoding that conforms to the SMTLib syntax. We
 keep track of these mappings to ensure that each Term construct is translated
 to its SMT encoding exactly once.  This translation invariant is necessary for
 correctness in the case of record type declarations, UF names, and variable
 names; and it is neccessary for compactness in the case of terms. In
 particular, the resulting SMT encoding will be in A-normal form (ANF): the body
 of every s-expression in the encoding consists of atomic subterms (identifiers
 or literals).
-/

namespace Cedar.SymCC

open Cedar.Spec Cedar.Validation
open Solver Batteries

structure EncoderState where
  terms : RBMap Term String (compareOfLessAndEq · ·)
  types : RBMap TermType String (compareOfLessAndEq · ·)
  uufs  : RBMap UUF String (compareOfLessAndEq · ·)
  enums : RBMap EntityType (List String) (compareOfLessAndEq · ·)

def EncoderState.init (εnv : SymEnv) : EncoderState :=
  let enums := εnv.entities.toList.filterMap λ (ety, d) => do (ety, (← d.members).toList)
  ⟨RBMap.empty, RBMap.empty, RBMap.empty, RBMap.ofList enums (compareOfLessAndEq · ·)⟩

abbrev EncoderM (α) := StateT EncoderState SolverM α

namespace Encoder

def termId (n : Nat)                    : String := s!"t{n}"
def uufId (n : Nat)                     : String := s!"f{n}"
def entityTypeId (n : Nat)              : String := s!"E{n}"
def enumId (E : String) (n : Nat)       : String := s!"{E}_m{n}"
def recordTypeId (n : Nat)              : String := s!"R{n}"
def recordAttrId (R : String) (a : Nat) : String := s!"{R}_a{a}"

def typeNum : EncoderM Nat := do return (← get).types.size
def termNum : EncoderM Nat := do return (← get).terms.size
def uufNum  : EncoderM Nat := do return (← get).uufs.size

def declareType (id : String) (mks : List String) : EncoderM String := do
  declareDatatype id [] mks
  return id

def declareEntityType (ety : EntityType) : EncoderM String := do
  let etyId := entityTypeId (← typeNum)
  match (← get).enums.find? ety with
  | .some members =>
    comment s!"{toString ety}::[{String.intercalate ", " members}]"
    declareType etyId (members.mapIdx λ i _ => s!"({enumId etyId i})")
  | .none =>
    comment s!"{toString ety}"
    declareType etyId [s!"({etyId} (eid String))"]

def declareExtType : ExtType → EncoderM String
  | .decimal =>
    declareType "Decimal" ["(Decimal (decimalVal (_ BitVec 64)))"]
  | .ipAddr  =>
    declareType "IPAddr"
      ["(V4 (addrV4 (_ BitVec 32)) (prefixV4 (Option (_ BitVec 5))))",
       "(V6 (addrV6 (_ BitVec 128)) (prefixV6 (Option (_ BitVec 7))))"]
  | .datetime =>
    declareType "Datetime" ["(Datetime (datetimeVal (_ BitVec 64)))"]
  | .duration =>
    declareType "Duration" ["(Duration (durationVal (_ BitVec 64)))"]

def declareRecordType (rty : List (Attr × String)) : EncoderM String := do
  let rtyId := recordTypeId (← typeNum)
  let attrs := rty.mapIdx (λ i (_, ty) => s!"({recordAttrId rtyId i} {ty})")
  comment s!"\{{String.intercalate ", " (rty.map Prod.fst)}}"
  declareType rtyId [s!"({rtyId} {String.intercalate " " attrs})"]

def encodeType (ty : TermType) : EncoderM String := do
  if let (.some enc) := (← get).types.find? ty then return enc
  let enc ←
    match ty with
    | .bool             => return "Bool"
    | .string           => return "String"
    | .bitvec n         => return s!"(_ BitVec {n})"
    | .option oty       => return s!"(Option {← encodeType oty})"
    | .set sty          => return s!"(Set {← encodeType sty})"
    | .entity ety       => declareEntityType ety
    | .ext xty          => declareExtType xty
    | .record (.mk rty) => declareRecordType (← rty.mapM₃ (λ ⟨(aᵢ, tyᵢ), _⟩ => do return (aᵢ, (← encodeType tyᵢ))))
  modifyGet λ state => (enc, {state with types := state.types.insert ty enc})

/--
The maximum Unicode code point supported in SMT-LIB 2.7.
Also see `num_codes` in cvc5:
https://github.com/cvc5/cvc5/blob/b78e7ed23348659db52a32765ad181ae0c26bbd5/src/util/string.h#L53
-/
def smtLibMaxCodePoint : Nat := 196607

/-
This function needs to encode unicode strings with two levels of
escape sequences:
- At the string theory level, we need to encode all non-printable
  unicode characters as `\u{xxxx}`, where a character is printable
  if its code point is within [32, 126] (see also the note on string
  literals in https://smt-lib.org/theories-UnicodeStrings.shtml).
- At the parser level, we need to replace any single `"` character
  with `""`, according to the SMT-LIB 2.7 standard on string literals:
  https://smt-lib.org/papers/smt-lib-reference-v2.7-r2025-07-07.pdf

Note in particular that `\\` is NOT an escape sequence,
so cvc5 will read `\\u{0}` as a two-character string with
characters `\u{5c}` and `\0`.
-/
def encodeString (s : String) : IO String := do
  let l ← s.toList.mapM (λ c =>
      if c = '"' then return "\"\""
      else if c = '\\' then
        -- This is to avoid unexpectedly escaping some characters
        return "\\u{5c}"
      else if 32 ≤ c.toNat ∧ c.toNat ≤ 126 then return s!"{c}"
      else
        if c.toNat ≤ smtLibMaxCodePoint then
          return ("\\u{" ++ (Nat.toDigits 16 c.toNat).toString ++ "}")
        else
          -- Invalid code point for SMT-LIB
          throw (IO.userError s!"Code point {c.toNat} not supported in SMT-LIB: {s}")
    )
  return String.join l

def encodeBitVec {n : Nat} (bv : _root_.BitVec n) : String :=
  s!"(_ bv{bv.toNat} {n})"

def encodeIPAddrPrefix {w} (pre : Ext.IPAddr.IPNetPrefix w) : String :=
  match pre with
  | .some p => s!"(some {encodeBitVec p})"
  | .none   => s!"(as none (Option (_ BitVec {w})))"

def encodeExt : Ext → String
  | .decimal d =>
    let bvEnc := encodeBitVec (BitVec.ofInt 64 d)
    s!"(Decimal {bvEnc})"
  | .ipaddr (.V4 ⟨addrV4, preV4⟩) =>
    let addr := encodeBitVec addrV4
    let pre  := encodeIPAddrPrefix preV4
    s!"(V4 {addr} {pre})"
  | .ipaddr (.V6 ⟨addrV6, preV6⟩) =>
    let addr := encodeBitVec addrV6
    let pre  := encodeIPAddrPrefix preV6
    s!"(V6 {addr} {pre})"
  | .datetime dt =>
    let bvEnc := encodeBitVec (BitVec.ofInt 64 dt.val)
    s!"(Datetime {bvEnc})"
  | .duration d =>
    let bvEnc := encodeBitVec (BitVec.ofInt 64 d.val)
    s!"(Duration {bvEnc})"

def declareVar (v : TermVar) (tyEnc : String) : EncoderM String := do
  let id := (termId (← termNum))
  comment (reprStr v.id)
  declareConst id tyEnc
  return id

def defineTerm (tyEnc tEnc : String) : EncoderM String := do
  let id := termId (← termNum)
  defineFun id [] tyEnc tEnc
  return id

def defineSet (tyEnc : String) (tEncs : List String) : EncoderM String := do
  defineTerm tyEnc (tEncs.foldl (λ acc t => s!"(set.insert {t} {acc})") s!"(as set.empty {tyEnc})")

def defineRecord (tyEnc : String) (tEncs : List String) : EncoderM String := do
  defineTerm tyEnc s!"({tyEnc} {String.intercalate " " tEncs})"

def encodeUUF (uuf : UUF) : EncoderM String := do
  if let (.some enc) := (← get).uufs.find? uuf then return enc
  let id := uufId (← uufNum)
  comment uuf.id
  declareFun id [(← encodeType uuf.arg)] (← encodeType uuf.out)
  modifyGet λ state => (id, {state with uufs := state.uufs.insert uuf id})

def encodeExtOp : ExtOp → String
  | .decimal.val       => "decimalVal"
  | .ipaddr.isV4       => "(_ is V4)"
  | .ipaddr.addrV4     => "addrV4"
  | .ipaddr.prefixV4   => "prefixV4"
  | .ipaddr.addrV6     => "addrV6"
  | .ipaddr.prefixV6   => "prefixV6"
  | .datetime.val      => "datetimeVal"
  | .datetime.ofBitVec => "Datetime"
  | .duration.val      => "durationVal"
  | .duration.ofBitVec => "Duration"

 def encodeOp : Op → String
  | .eq            => "="
  | .zero_extend n => s!"(_ zero_extend {n})"
  | .option.get    => "val"
  | .ext xop       => encodeExtOp xop
  | op             => op.mkName

def encodePatElem : PatElem → EncoderM String
  | .star       => return "(re.* re.allchar)"
  | .justChar c => return s!"(str.to_re \"{← encodeString c.toString}\")"

def encodePattern : Pattern → EncoderM String
  | []  => return "(str.to_re \"\")"
  | [e] => encodePatElem e
  | p   => return s!"(re.++ {String.intercalate " " (← p.mapM encodePatElem)})"

def defineEntity (tyEnc : String) (entity : EntityUID) : EncoderM String := do
  match (← get).enums.find? entity.ty with
  | .some members => return s!"{enumId tyEnc (members.idxOf entity.eid)}"
  | .none         => defineTerm tyEnc s!"({tyEnc} \"{← encodeString entity.eid}\")"

private def indexOfAttr (a : Attr) : TermType → EncoderM Nat
  | .record (.mk rty) => return rty.findIdx (Prod.fst · = a)
  | ty                => throw (IO.userError s!"Bad term: (record.get {a} {reprStr ty})")

def defineRecordGet (tyEnc a tEnc : String) (ty : TermType) : EncoderM String := do
  let rId := (← get).types.find! ty
  let aId ← indexOfAttr a ty
  defineTerm tyEnc s!"({recordAttrId rId aId} {tEnc})"

def defineApp (tyEnc : String) (op : Op) (tEncs : List String) (ts : List Term): EncoderM String := do
  let args := String.intercalate " " tEncs
  match op with
  | .record.get a  => defineRecordGet tyEnc a args ts.head!.typeOf
  | .string.like p => defineTerm tyEnc s!"(str.in_re {args} {← encodePattern p})"
  | .uuf f         => defineTerm tyEnc s!"({← encodeUUF f} {args})"
  | _              => defineTerm tyEnc s!"({encodeOp op} {args})"

def encodeTerm (t : Term) : EncoderM String := do
  if let (.some enc) := (← get).terms.find? t then return enc
  let tyEnc ← encodeType t.typeOf
  let enc ←
    match t with
    | .var v            => declareVar v tyEnc
    | .prim p           =>
      match p with
      | .bool b         => return if b then "true" else "false"
      | .bitvec bv      => return encodeBitVec bv
      | .string s       => return s!"\"{← encodeString s}\""
      | .entity e       => defineEntity tyEnc e
      | .ext x          => defineTerm tyEnc (encodeExt x)
    | .none _           => defineTerm tyEnc s!"(as none {tyEnc})"
    | .some t₁          => defineTerm tyEnc s!"(some {← encodeTerm t₁})"
    | .set (.mk ts) _   => defineSet tyEnc (← ts.mapM₁ (λ ⟨tᵢ, _⟩ => encodeTerm tᵢ))
    | .record (.mk ats) => defineRecord tyEnc (← ats.mapM₃ (λ ⟨(_, tᵢ), _⟩ => encodeTerm tᵢ))
    | .app .bvnego [t] .bool =>
      -- don't encode bvnego itself, for compatibility with older CVC5 (bvnego was
      -- introduced in CVC5 1.1.2)
      -- this rewrite is done in the encoder and is thus trusted; cdiss@ has some work
      -- towards doing this rewrite in Factory.lean instead, and adjusting the proofs
      -- appropriately, so coordinate with him before starting that work afresh
      match t.typeOf with
      | .bitvec n =>
        -- more fancy and possibly more optimized, but hard to prove termination:
        -- encodeTerm (Factory.eq t (BitVec.intMin n))
        defineApp tyEnc .eq [← encodeTerm t, encodeBitVec (BitVec.intMin n)] [t, BitVec.intMin n]
      | _ =>
        -- we could put anything here and be sound, because `bvnego` should only be
        -- applied to Terms of type .bitvec
        return "false"
    | .app op ts _      => defineApp tyEnc op (← ts.mapM₁ (λ ⟨tᵢ, _⟩ => encodeTerm tᵢ)) ts
  modifyGet λ state => (enc, {state with terms := state.terms.insert t enc})

/--
Once you've generated `Asserts` with one of the functions in Verifier.lean, you
can use this function to encode them as SMTLib assertions.

To actually solve these SMTLib assertions, you want to combine this `encode`
action with other `SolverM` actions, such as `Solver.check-sat` at a minimum.

Then you can run any `SolverM` action `act` with `act |>.run solver`, where
`solver` is a `Solver` instance you can construct using functions in
Solver.lean.

Note that `encode` itself first resets the solver in order to define datatypes
etc.
-/
def encode (ts : List Term) (εnv : SymEnv) (produceModels : Bool := false) : SolverM EncoderState := do
  Solver.reset
  Solver.setOptionProduceModels produceModels
  Solver.setLogic "ALL"
  Solver.declareDatatype "Option" ["X"] ["(none)", "(some (val X))"]
  let (ids, s) ← ts.mapM encodeTerm |>.run (EncoderState.init εnv)
  for id in ids do
    Solver.assert id
  return s

end Encoder

namespace Cedar.SymCC
