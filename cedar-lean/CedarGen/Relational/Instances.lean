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

import Cedar.Validation.Relational.Typing
import CedarGen.Relational.Decidables
import CedarGen.Relational.DeadOperand
import Specimen
import Specimen.Basalt

/-! # Specimen instances for the relational typing spec

* decision procedures (`DecOpt`) for the relations the derived generators check rather than
  produce;
* generators for the leaf relations whose witnesses are strings the parsers must accept
  (decimal, IP address, datetime and duration literals);
* `Arbitrary` and `Enum` instances for the values the derived generators draw freely. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Plausible

instance : DecOpt (CapMem x k c) where
  decOpt _ := .ok (c.any (fun (x', k') => x' == x && k' == k))

instance : DecOpt (CapTagMem x e c) where
  decOpt _ := .ok (c.any (fun (x', k') => x' == x && k' == .tag e))

instance : DecOpt (CapAttrMem x a c) where
  decOpt _ := .ok (c.any (fun (x', k') => x' == x && k' == .attr a))

instance [BEq α] [BEq β] : DecOpt (MapContains k v (m : Map α β)) where
  decOpt _ := .ok (match m with | .mk l => l.any (fun (k', v') => k' == k && v' == v))

instance [DecidableEq α] [BEq α] : DecOpt (MapNotContainsKey (α := α) (β := β) k (m : Map α β)) where
  decOpt _ := .ok (match m with | .mk l => l.all (fun (k', _) => k' != k))

instance [BEq α] : DecOpt (SetContains x (s : Set α)) where
  decOpt _ := .ok (match s with | .mk l => l.any (· == x))

/-- The first entry with the key, as the relation reads the map: its `nextA`/`nextB` pass only entries
    with other keys. -/
instance [BEq v] : DecOpt (MapContainsPairKey (v := v) a b va m) where
  decOpt _ := .ok (match m with
    | .mk l =>
      match l.find? (fun (uid, _) => uid.ty == a && uid.eid == b) with
      | some (_, val) => val == va
      | none => false)

instance : DecOpt (MapContainsAncestors ety ancs (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨a, _, _⟩ => a == ancs | _ => false))

instance : DecOpt (MapContainsAttrs ety attrs (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨_, a, _⟩ => a == attrs | _ => false))

instance : DecOpt (MapContainsTagType ety ty (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨_, _, .some t⟩ => t == ty | _ => false))

instance : DecOpt (MapContainsNoTags ety (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with | .mk l => l.any (fun (k, v) => k == ety &&
    match v with | .standard ⟨_, _, .none⟩ => true | _ => false))

/-- The first entry with the key, as the relation reads the schema: its `there` passes only entries
    with other keys. -/
instance : DecOpt (MapContainsEnum ety eids (ets : EntitySchema)) where
  decOpt _ := .ok (match ets with
    | .mk l =>
      match l.find? (fun (k, _) => k == ety) with
      | some (_, .enum e) => e == eids
      | _ => false)

/-- `ActionDescendentOf` as the relation states it, over any entry for the action, rather than
    `ActionSchema.descendentOf`, which reads only the first. -/
def actionInSetB (acts : ActionSchema) (uid₁ : EntityUID) (xs : List Expr) : Bool :=
  xs.any (fun x => match x with
    | .lit (.entityUID uid₂) => acts.toList.any (fun (k, e) => k == uid₁ &&
        (uid₁ == uid₂ || match e.ancestors with | .mk l => l.any (· == uid₂)))
    | _ => false)

/-- (The test named, so that its laws are about it: an inlined `match` is a matcher of its own in
    each declaration, and a law stated with another never applies.) -/
instance : DecOpt (ActionInSet acts uid₁ xs) where
  decOpt _ := .ok (actionInSetB acts uid₁ xs)

/-- `ParserImage` decided by its structural test: a derived checker has no rule for the `∀ x ∈ xs`
    premises of set, record and call literals, and is incomplete there. -/
instance : DecOpt (ParserImage x) where
  decOpt _ := .ok (parserImageB x)

instance : DecOpt (ValidDecimal s) where
  decOpt _ := .ok (Cedar.Spec.Ext.Decimal.decimal s).isSome

instance : DecOpt (ValidIP s) where
  decOpt _ := .ok (Cedar.Spec.Ext.IPAddr.ip s).isSome

instance : DecOpt (ValidDatetime s) where
  decOpt _ := .ok (Cedar.Spec.Ext.Datetime.parse s).isSome

instance : DecOpt (ValidDuration s) where
  decOpt _ := .ok (Cedar.Spec.Ext.Datetime.Duration.parse s).isSome

/-! ### Full-coverage generators for extension-function literal strings.
Each builds a value from independently-generated components that span the full
valid space (per the parsers in `Cedar/Spec/Ext/`), formats it to the string the
parser expects, and keeps the parser check as a safety net so out-of-range /
overflow combinations simply retry. -/

/-- Left-pad `n` with `'0'` to at least `width` characters. -/
private def zeroPad (n width : Nat) : String :=
  let s := toString n
  if s.length < width then String.ofList (List.replicate (width - s.length) '0') ++ s else s

/-- Lowercase hexadecimal string of `n` (no padding), for IPv6 groups. -/
private partial def toHexLower (n : Nat) : String :=
  let digit (d : Nat) : Char :=
    if d < 10 then Char.ofNat ('0'.toNat + d) else Char.ofNat ('a'.toNat + (d - 10))
  if n < 16 then String.singleton (digit n)
  else toHexLower (n / 16) ++ String.singleton (digit (n % 16))

/-- A string of `n` `'0'` characters, for value-preserving leading-zero forms. -/
private def leadZeros (n : Nat) : String := String.ofList (List.replicate n '0')

/-- Draw 0..2 leading zeros — a distinct, parser-accepted spelling of the same
    quantity (`String.toNat?` accepts "007"). Exercised on ~2/3 of quantities. -/
private def genLeadZeros {G : Type → Type} [_root_.Gen G] : G String := do
  let lz := (← chooseNat 0 2); pure (leadZeros lz)

/-- One duration unit: with prob. 1/2 present with an arbitrary quantity in
    `0..hi` (optionally leading-zero padded), else omitted (units may be dropped,
    but the whole string must be ordered largest→smallest, enforced at the call
    site). -/
private def genDurUnit {G : Type → Type} [_root_.Gen G] (suffix : String) (hi : Nat) : G String := do
  let incl := (← chooseNat 0 1)
  if incl == 0 then pure ""
  else do
    let q := (← chooseNat 0 hi)
    let lz ← genLeadZeros
    pure s!"{lz}{q}{suffix}"

/-- `g`, and rarely any string `ok` accepts, so that every one can be drawn: the extension-literal
    producers write their own spellings of the literals the parser takes, and not all of them. -/
def orParsing {G : Type → Type} [Gen G] [Specimen.Pick G] [Specimen.Fail G] (ok : String → Bool)
    (leaf : Nat) (g : G String) : G String :=
  frequency [
    (9, fun _ => g),
    (1, fun _ => do
      let s : String ← Basalt.ArbitrarySized.arbitrarySized leaf
      if ok s then return s else Specimen.Fail.fail)]

instance : BacktrackGenFor String ValidDecimal where
  gen _ leaf := orParsing (fun s => (Cedar.Spec.Ext.Decimal.decimal s).isSome) leaf <| do
    -- integer part spans the full `Int64 / 10^4` range; sign is explicit so
    -- negative values with a zero integer part (e.g. `-0.5`) are reachable.
    let neg := (← chooseNat 0 1)
    let mag := (← chooseNat 0 922337203685477)
    let fracDigits := (← chooseNat 1 4)
    -- `fracVal` left-padded to `fracDigits` covers both `.05` and `.50` spellings.
    let fracVal := (← chooseNat 0 (Nat.pow 10 fracDigits - 1))
    -- leading zeros on the integer part are value-preserving but a distinct
    -- parser input (`String.toInt?` accepts "007" / "-007"); exercise them often.
    let intLeadZeros := (← chooseNat 0 3)
    let magStr := leadZeros intLeadZeros ++ toString mag
    -- sign is unconditional (allows negative zero "-0.0", which parses to 0; only
    -- the bare "-" left part is rejected, and `magStr` is never empty).
    let signStr := if neg == 1 then "-" else ""
    let s := s!"{signStr}{magStr}.{zeroPad fracVal fracDigits}"
    match Cedar.Spec.Ext.Decimal.decimal s with
    | some _ => return s
    | none => Specimen.Fail.fail

instance : BacktrackGenFor String ValidIP where
  gen _ leaf := orParsing (fun s => (Cedar.Spec.Ext.IPAddr.ip s).isSome) leaf <| do
    -- one IPv6 group: value as lowercase hex, then left-padded with zeros to a
    -- random width in 1..4 (never truncating). Leading-zero groups like `00ff` /
    -- `0001` are a distinct, parser-accepted spelling. Since ~94% of full-range
    -- 16-bit values are already 4 hex digits (no room to pad), half the groups
    -- are drawn from a small range (0..0xff) so leading zeros are non-rare while
    -- the full 0..0xffff range stays covered by the other half.
    let genGroup := do
      let big := (← chooseNat 0 1)
      let g := (← chooseNat 0 (if big == 1 then 65535 else 255))
      let hx := toHexLower g
      let w := (← chooseNat 1 4)
      pure (if hx.length < w then leadZeros (w - hx.length) ++ hx else hx)
    -- variant 0/1: IPv4 (plain / CIDR); 2/3: IPv6 full 8-group (plain / CIDR);
    -- 4/5: IPv6 `::`-compressed (plain / CIDR), exercising the parser's
    -- `splitOn "::"` fill branch that the full form never reaches.
    let variant := (← chooseNat 0 5)
    let s ← match variant with
      | 0 | 1 => do
        let a := (← chooseNat 0 255)
        let b := (← chooseNat 0 255)
        let c := (← chooseNat 0 255)
        let d := (← chooseNat 0 255)
        let base := s!"{a}.{b}.{c}.{d}"
        if variant == 0 then pure base
        else do let p := (← chooseNat 0 32); pure s!"{base}/{p}"
      | 2 | 3 => do
        let mut groups : List String := []
        for _ in List.range 8 do groups := groups ++ [← genGroup]
        let base := String.intercalate ":" groups
        if variant == 2 then pure base
        else do let p := (← chooseNat 0 128); pure s!"{base}/{p}"
      | _ => do
        -- `::` stands in for one-or-more zero groups, so the explicit groups
        -- must number strictly fewer than 8 (parser requires `len < 8`).
        let k := (← chooseNat 0 7)      -- explicit group count
        let nl := (← chooseNat 0 k)     -- groups left of `::`
        let mut ls : List String := []
        for _ in List.range nl do ls := ls ++ [← genGroup]
        let mut rs : List String := []
        for _ in List.range (k - nl) do rs := rs ++ [← genGroup]
        let base := String.intercalate ":" ls ++ "::" ++ String.intercalate ":" rs
        if variant == 4 then pure base
        else do let p := (← chooseNat 0 128); pure s!"{base}/{p}"
    match Cedar.Spec.Ext.IPAddr.ip s with
    | some _ => return s
    | none => Specimen.Fail.fail

/-- A datetime string in one of the five formats, before the parser has checked it. -/
def datetimeCandidate {G : Type → Type} [_root_.Gen G] : G String := do
    let year := (← chooseNat 1 9999)
    let month := (← chooseNat 1 12)
    -- day 1..31; invalid day/month combinations (e.g. Feb 30) are rejected below.
    let day := (← chooseNat 1 31)
    let datePart := s!"{zeroPad year 4}-{zeroPad month 2}-{zeroPad day 2}"
    -- fmt 0: date only, 1: UTC, 2: UTC+ms, 3: offset, 4: offset+ms.
    let fmt := (← chooseNat 0 4)
    let s ← match fmt with
      | 0 => pure datePart
      | f => do
        let hh := (← chooseNat 0 23)
        let mm := (← chooseNat 0 59)
        let ss := (← chooseNat 0 59)
        let time := s!"{zeroPad hh 2}:{zeroPad mm 2}:{zeroPad ss 2}"
        let msPart ← if f == 2 || f == 4 then do
            let ms := (← chooseNat 0 999); pure s!".{zeroPad ms 3}"
          else pure ""
        let tz ← if f == 1 || f == 2 then pure "Z"
          else do
            let sign := (← chooseNat 0 1)
            let oh := (← chooseNat 0 23)
            let om := (← chooseNat 0 59)
            pure s!"{if sign == 0 then "+" else "-"}{zeroPad oh 2}{zeroPad om 2}"
        pure s!"{datePart}T{time}{msPart}{tz}"
    pure s

instance : BacktrackGenFor String ValidDatetime where
  gen _ leaf := orParsing (fun s => (Cedar.Spec.Ext.Datetime.parse s).isSome) leaf <| do
    let s ← datetimeCandidate
    match Cedar.Spec.Ext.Datetime.parse s with
    | some _ => return s
    | none => Specimen.Fail.fail

instance : BacktrackGenFor String ValidDuration where
  gen _ leaf := orParsing (fun s => (Cedar.Spec.Ext.Datetime.Duration.parse s).isSome) leaf <| do
    let neg := (← chooseNat 0 1)
    let signStr := if neg == 1 then "-" else ""
    -- mode 0: a single unit whose quantity spans that unit's full Int64 range
    --   (reaches high-magnitude durations; the cap is `⌊Int64.max / mult⌋`, so
    --   the summed value always fits — no overflow retries).
    -- mode 1: several units, each with a modest quantity, exercising the ordered
    --   multi-pair form. A rare summed-value overflow simply retries.
    let mode := (← chooseNat 0 1)
    let body ← if mode == 0 then do
        let u := (← chooseNat 0 4)
        let (suffix, hi) := match u with
          | 0 => ("d",  106751991167)
          | 1 => ("h",  2562047788015)
          | 2 => ("m",  153722867280912)
          | 3 => ("s",  9223372036854775)
          | _ => ("ms", 9223372036854775807)
        let q := (← chooseNat 0 hi)
        let lz ← genLeadZeros
        pure s!"{lz}{q}{suffix}"
      else do
        -- units ordered largest→smallest, each optionally present with a quantity.
        let d  ← genDurUnit "d" 10000
        let h  ← genDurUnit "h" 100000
        let m  ← genDurUnit "m" 1000000
        let sc ← genDurUnit "s" 1000000
        let ms ← genDurUnit "ms" 100000000
        let b := d ++ h ++ m ++ sc ++ ms
        pure (if b.isEmpty then "0ms" else b)
    let s := signStr ++ body
    match Cedar.Spec.Ext.Datetime.Duration.parse s with
    | some _ => return s
    | none => Specimen.Fail.fail

-- Extension-function typing is inlined directly into `HasType` (see the
-- `call*` constructors): each function's argument types are constants, so the
-- rules state them as direct `HasType` premises rather than routing a `tys`
-- signature list through an auxiliary relation + `HasTypeList`.

/-- The tests of the literal checks below, named, so that the checks' laws are stated in the terms
a derived generator's soundness proof sees: an inlined `match` is a different matcher in each. -/
def bothLitB (x₁ x₂ : Expr) : Bool :=
  match x₁, x₂ with | .lit _, .lit _ => true | _, _ => false

def isActionLitMemB (x₁ x₂ : Expr) (acts : ActionSchema) : Bool :=
  match x₁, x₂ with
  | .lit (.entityUID uid₁), .lit (.entityUID _) => acts.contains uid₁
  | _, _ => false

def isActionLitMemSetB (x₁ x₂ : Expr) (acts : ActionSchema) : Bool :=
  match x₁, x₂ with
  | .lit (.entityUID uid₁), .set xs =>
    acts.contains uid₁ && xs.all (match · with | .lit (.entityUID _) => true | _ => false)
  | _, _ => false

instance : DecOpt (BothLit x₁ x₂) where
  decOpt _ := .ok (bothLitB x₁ x₂)

instance : DecOpt (IsActionLitMem x₁ x₂ acts) where
  decOpt _ := .ok (isActionLitMemB x₁ x₂ acts)

instance : DecOpt (IsActionLitMemSet x₁ x₂ acts) where
  decOpt _ := .ok (isActionLitMemSetB x₁ x₂ acts)

instance : DecOpt (NotFf b) where
  decOpt _ := .ok (b != .ff)

instance : DecOpt (BoolTypeNeq a b) where
  decOpt _ := .ok (a != b)

/-- Whether `c` interleaves `c₁` and `c₂`, an entry common to both heads taken once (`CapMerge`). -/
def capMergeB : Capabilities → Capabilities → Capabilities → Bool
  | c₁, c₂, [] => c₁.isEmpty && c₂.isEmpty
  | c₁, c₂, p :: c =>
    (match c₁ with | q :: c₁' => q == p && capMergeB c₁' c₂ c | [] => false) ||
    (match c₂ with | q :: c₂' => q == p && capMergeB c₁ c₂' c | [] => false) ||
    (match c₁, c₂ with
      | q₁ :: c₁', q₂ :: c₂' => q₁ == p && q₂ == p && capMergeB c₁' c₂' c
      | _, _ => false)

instance : DecOpt (CapMerge c₁ c₂ c) where
  decOpt _ := .ok (capMergeB c₁ c₂ c)

instance : DecOpt (KeyAbove lb a) where
  decOpt _ := .ok (match lb with | none => true | some b => decide (b < a))

/-- Written against `BacktrackGenFor` (polymorphic over Basalt's `Gen`) rather than
    `ArbitrarySizedSuchThat`. `Specimen.BasaltBridge` derives the narrow instance from the broad one, so
    a single definition serves both the Plausible path and `specimen.emitBasalt`; the reverse direction
    does not exist, so a narrow-only instance is invisible to a Basalt-emitted caller. -/
instance (b : Attr) : BacktrackGenFor Attr (fun a => b < a) where
  gen size leafSize := frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (size + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    -- rarely any attribute above `b`, so that every one can be drawn
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized leafSize
      if decide (b < a) then return a else Specimen.Fail.fail)]

/-- The enumerator counterpart, for the enumerators `HasTypeRecord` is derived to (record
    literals under a checker's search). -/
instance (b : Attr) : EnumFor Attr (fun a => b < a) where
  enum size leafSize := frequency [
    (9, fun _ => do
      let n ← chooseNat 1 (size + 1)
      return b ++ String.ofList (List.replicate n 'a')),
    -- and any attribute above `b`, drawn freely, so that every one is enumerated (completeness)
    (1, fun _ => do
      let a : Attr ← Basalt.ArbitrarySized.arbitrarySized leafSize
      if decide (b < a) then return a else Specimen.Fail.fail)]

/-- An attribute below `b`, for the derived enumerators of `InsertSortedField` (`here`, with the
    inserted key unknown): drawn freely and kept if below. -/
instance (b : Attr) : EnumFor Attr (fun a => a < b) where
  enum _ leafSize := do
    let a : Attr ← Basalt.ArbitrarySized.arbitrarySized leafSize
    if decide (a < b) then return a else Specimen.Fail.fail

/-! ## Unconstrained values -/

instance [Arbitrary α] [Arbitrary β] [LT α] [DecidableLT α] : Arbitrary (Map α β) where
  arbitrary := do
    let ⟨len, _⟩ ← Gen.choose Nat 0 4 (by omega)
    let mut pairs : List (α × β) := []
    for _ in List.range len do
      pairs := (← Arbitrary.arbitrary, ← Arbitrary.arbitrary) :: pairs
    return Map.make pairs

instance [Enum α] [Enum β] [LT α] [DecidableLT α] : Enum (Map α β) where
  enum := do
    let pairs ← Enum.enum (α := List (α × β))
    return Map.make pairs

deriving instance Arbitrary for Attr
deriving instance Arbitrary for
  Var, ExtFun, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp,
  BinaryOp, Qualified, CedarType, Effect

/-- Expressions and capability keys are what the relations produce, never draw freely. -/
instance : Arbitrary Expr where
  arbitrary := return .lit (.bool true)

instance : Arbitrary Key where
  arbitrary := return .attr ""

instance : Enum Expr where
  enum := pure (.lit (.bool true))

instance : Enum Key where
  enum := pure (.attr "")

deriving instance Enum for
  Var, ExtFun, UInt64, Int64, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp,
  BinaryOp, Qualified

deriving instance Enum for EntityType

instance : Enum CedarType where
  enum := EnumeratorCombinators.oneOfWithDefault (pure .int) [
    pure .int,
    pure .string,
    do let b ← Enum.enum (α := BoolType); return .bool b,
    do let x ← Enum.enum (α := ExtType); return .ext x]

/-- Map values a generator has to fill in where only the key matters (`MapNotContainsKey`). -/
instance : Arbitrary EntitySchemaEntry where
  arbitrary := Gen.elements
    [.standard { ancestors := Set.empty, attrs := Map.empty, tags := none },
     .enum (Set.make ["a", "b"])] (by simp)

instance : Enum EntitySchemaEntry where
  enum := EnumeratorCombinators.oneOfWithDefault
    (pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none })) [
    pure (.standard { ancestors := Set.empty, attrs := Map.empty, tags := none }),
    pure (.enum (Set.make ["a", "b"]))]

instance : Enum ActionSchemaEntry where
  enum := pure { appliesToPrincipal := Set.empty, appliesToResource := Set.empty,
                 ancestors := Set.empty, context := Map.empty }

deriving instance DecidableEq for ActionSchemaEntry

/-! ## Producers for the generic map and set relations

Under `specimen.emitBasalt`, Specimen cannot derive a producer for a relation with type parameters: it
would need `Basalt.ArbitrarySized` for them. So the modes the derived generators use are written here,
once for every key and value type. Each draws arbitrary entries and places, or removes, the one the
relation is about. -/

/-- Insert `x` at a random position of `xs`. -/
def insertSomewhere {G : Type → Type} [_root_.Gen G] (x : α) (xs : List α) : G (List α) := do
  let i ← chooseNat 0 xs.length
  pure (xs.take i ++ x :: xs.drop i)

/-- A random permutation of `xs`: each element inserted at a random position of the rest. -/
def shuffle {G : Type → Type} [_root_.Gen G] : List α → G (List α)
  | [] => pure []
  | x :: xs => do insertSomewhere x (← shuffle xs)

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] {k : α} {v : β} :
    BacktrackGenFor (Map α β) (fun m => MapContains k v m) where
  gen _ leafSize := do
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized leafSize
    return Map.mk (← insertSomewhere (k, v) rest)

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] {k : α} :
    BacktrackGenFor (β × Map α β) (fun (v, m) => MapContains k v m) where
  gen _ leafSize := do
    let v : β ← Basalt.ArbitrarySized.arbitrarySized leafSize
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized leafSize
    return (v, Map.mk (← insertSomewhere (k, v) rest))

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [DecidableEq α] {k : α} :
    BacktrackGenFor (Map α β) (fun m => MapNotContainsKey k m) where
  gen _ leafSize := do
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized leafSize
    return Map.mk (rest.filter (fun p => p.1 ≠ k))

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [DecidableEq α] :
    BacktrackGenFor (α × Map α β) (fun (k, m) => MapNotContainsKey k m) where
  gen _ leafSize := do
    let k : α ← Basalt.ArbitrarySized.arbitrarySized leafSize
    let rest : List (α × β) ← Basalt.ArbitrarySized.arbitrarySized leafSize
    return (k, Map.mk (rest.filter (fun p => p.1 ≠ k)))

instance [Basalt.ArbitrarySized α] [DecidableEq α] {m : Map α β} :
    BacktrackGenFor α (fun k => MapNotContainsKey k m) where
  gen _ leafSize := do
    let k : α ← Basalt.ArbitrarySized.arbitrarySized leafSize
    if m.toList.any (fun p => decide (p.1 = k)) then Specimen.Fail.fail else return k

instance [Basalt.ArbitrarySized α] :
    BacktrackGenFor (α × Set α) (fun (x, s) => SetContains x s) where
  gen _ leafSize := do
    let x : α ← Basalt.ArbitrarySized.arbitrarySized leafSize
    let rest : List α ← Basalt.ArbitrarySized.arbitrarySized leafSize
    return (x, Set.mk (← insertSomewhere x rest))

/-! ## Unconstrained values for Basalt-emitted generators

Under `specimen.emitBasalt` a derived generator asks for `Basalt.ArbitrarySized`, which the
`Plausible.Arbitrary` instances above cannot serve. Each instance here mirrors one above, so both
paths draw from the same pools. -/

instance [Basalt.ArbitrarySized α] [Basalt.ArbitrarySized β] [LT α] [DecidableLT α] :
    Basalt.ArbitrarySized (Map α β) where
  -- `vectorOf` rather than a `for` loop, which `walk` has no rule for: the entries are drawn
  -- independently either way, so the distribution is the same.
  arbitrarySized n := do
    let len ← chooseNat 0 4
    let pairs ← vectorOf len (do
      let a ← Basalt.ArbitrarySized.arbitrarySized n
      let b ← Basalt.ArbitrarySized.arbitrarySized n
      pure (a, b))
    return Map.make pairs

instance : Basalt.ArbitrarySized Int64 where
  arbitrarySized n := do
    let i : Int ← Basalt.ArbitrarySized.arbitrarySized n
    return Int64.ofInt i

-- Outside the namespace: the handler names its helpers relative to the current namespace, and a
-- `Cedar.Validation.Relational.Cedar.Spec` namespace would capture later `open Cedar.Spec`s.
end Cedar.Validation.Relational

open Cedar.Spec Cedar.Validation in
deriving instance Basalt.ArbitrarySized for
  Var, ExtFun, BoolType, ExtType, Name, EntityUID, Prim, PatElem, UnaryOp, BinaryOp, Qualified,
  Effect

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-- An action of the schema, or (less often) any entity. -/
def actionOrAnyUID {G : Type → Type} [Gen G] [Specimen.Pick G] (acts : ActionSchema) (leaf : Nat) :
    G EntityUID :=
  frequency [
    (3, fun _ => do
      let i ← chooseNat 0 (acts.toList.length - 1)
      return (acts.toList.getD i default).1),
    (1, fun _ => Basalt.ArbitrarySized.arbitrarySized leaf)]

/-- An action literal and a set of entity literals: a derived producer has no rule for the premise
    `∀ x ∈ xs, ∃ uid, x = .lit (.entityUID uid)`, and draws nothing. -/
instance {acts : ActionSchema} :
    BacktrackGenFor (Expr × Expr) (fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) where
  gen _ leaf := do
    let i ← chooseNat 0 (acts.toList.length - 1)
    let uid₁ := (acts.toList.getD i default).1
    let n ← chooseNat 0 leaf
    let uids ← vectorOf n (actionOrAnyUID acts leaf)
    let x₁ := Expr.lit (.entityUID uid₁)
    let x₂ := Expr.set (uids.map fun u => .lit (.entityUID u))
    if isActionLitMemSetB x₁ x₂ acts then return (x₁, x₂) else Specimen.Fail.fail

/-- The enumerator counterpart, for the checkers that search for the pair: the derived enumerator,
    with no rule for the `∀` premise either, enumerates nothing (and is incomplete). -/
instance {acts : ActionSchema} :
    EnumFor (Expr × Expr) (fun (x₁, x₂) => IsActionLitMemSet x₁ x₂ acts) where
  enum _ leaf := do
    let i ← chooseNat 0 (acts.toList.length - 1)
    let uid₁ := (acts.toList.getD i default).1
    let n ← chooseNat 0 leaf
    let uids ← vectorOf n (actionOrAnyUID acts leaf)
    let x₁ := Expr.lit (.entityUID uid₁)
    let x₂ := Expr.set (uids.map fun u => .lit (.entityUID u))
    if isActionLitMemSetB x₁ x₂ acts then return (x₁, x₂) else Specimen.Fail.fail

/-- Any type of depth at most `n`; `record` nests `Map Attr (Qualified CedarType)`, which the deriving
    handler rejects. -/
def anyCedarType {G : Type → Type} [Gen G] [Specimen.Pick G] : Nat → G CedarType
  | 0 => frequency [
      (1, fun _ => pure .int),
      (1, fun _ => pure .string),
      (1, fun _ => .bool <$> Basalt.ArbitrarySized.arbitrarySized 0),
      (1, fun _ => .entity <$> Basalt.ArbitrarySized.arbitrarySized 0),
      (1, fun _ => .ext <$> Basalt.ArbitrarySized.arbitrarySized 0)]
  | n + 1 => frequency [
      (2, fun _ => pure .int),
      (2, fun _ => pure .string),
      (2, fun _ => .bool <$> Basalt.ArbitrarySized.arbitrarySized n),
      (2, fun _ => .entity <$> Basalt.ArbitrarySized.arbitrarySized n),
      (2, fun _ => .ext <$> Basalt.ArbitrarySized.arbitrarySized n),
      (1, fun _ => .set <$> anyCedarType n),
      (1, fun _ => do
        let k ← chooseNat 0 n
        let fs ← vectorOf k (do
          let a ← Basalt.ArbitrarySized.arbitrarySized n
          let q ← frequency [
            (1, fun _ => .required <$> anyCedarType n),
            (1, fun _ => .optional <$> anyCedarType n)]
          pure (a, q))
        pure (.record (Map.mk fs)))]

/-- The flat pool it was (as for `Enum CedarType`), and otherwise any type (`anyCedarType`), so that
    every one can be drawn. -/
instance : Basalt.ArbitrarySized CedarType where
  arbitrarySized n := frequency [
    (9, fun _ => oneOf [
      fun _ => pure .int,
      fun _ => pure .string,
      fun _ => .bool <$> Basalt.ArbitrarySized.arbitrarySized n,
      fun _ => .entity <$> Basalt.ArbitrarySized.arbitrarySized n,
      fun _ => .ext <$> Basalt.ArbitrarySized.arbitrarySized n]),
    (1, fun _ => anyCedarType n)]


/-- Map values a generator has to fill in where only the key matters (`MapNotContainsKey`). -/
instance : Basalt.ArbitrarySized EntitySchemaEntry where
  arbitrarySized _ := elements
    [.standard { ancestors := Set.empty, attrs := Map.empty, tags := none },
     .enum (Set.make ["a", "b"])]

/-! ## Strict-mode premises

`HasType true true` (the mode the generators derive from) adds premises the derivation cannot
produce well by itself. -/

/-- `MaybeActionDescendentOf` is `ActionSchema.maybeDescendentOf` (`maybeActionDescendentOf_iff`). -/
instance : DecOpt (MaybeActionDescendentOf acts ety₁ ety₂) where
  decOpt _ := .ok (acts.maybeDescendentOf ety₁ ety₂)

/-- The entity types of the ancestors of the actions of type `ety₁`. -/
def maybeActionAncestorTypes (acts : ActionSchema) (ety₁ : EntityType) : List EntityType :=
  acts.toList.flatMap fun (uid, e) => if uid.ty == ety₁ then e.ancestors.toList.map (·.ty) else []

/-- An ancestor type of some action of type `ety₁`: the relation's conclusion projects `.ty` out of
    the action and its ancestor, which a derived producer cannot invert. -/
instance {acts : ActionSchema} {ety₁ : EntityType} :
    BacktrackGenFor EntityType (fun ety₂ => MaybeActionDescendentOf acts ety₁ ety₂) where
  gen _ _ := do
    let cands := maybeActionAncestorTypes acts ety₁
    let i ← chooseNat 0 (cands.length - 1)
    let t := cands.getD i default
    if acts.maybeDescendentOf ety₁ t then return t else Specimen.Fail.fail

/-! ## Any expression -/

/-- Any expression, its leaves (literals and variables) more often than any one of its other
constructors: at most `f` constructors deep (the recursion's fuel), and of depth at most `b` (its
budget), counting the attributes of an extended `has`, which spend the budget. -/
def anyExprB {G : Type → Type} [Gen G] [Specimen.Pick G] : Nat → Nat → G Expr
  | f + 1, m + 1 => frequency [
      (6, fun _ => .lit <$> Basalt.ArbitrarySized.arbitrarySized f),
      (6, fun _ => .var <$> Basalt.ArbitrarySized.arbitrarySized f),
      (1, fun _ => do
        let a ← anyExprB f m
        let b ← anyExprB f m
        let c ← anyExprB f m
        pure (.ite a b c)),
      (1, fun _ => do
        let a ← anyExprB f m
        let b ← anyExprB f m
        pure (.and a b)),
      (1, fun _ => do
        let a ← anyExprB f m
        let b ← anyExprB f m
        pure (.or a b)),
      (1, fun _ => do
        let op ← Basalt.ArbitrarySized.arbitrarySized f
        let a ← anyExprB f m
        pure (.unaryApp op a)),
      (1, fun _ => do
        let op ← Basalt.ArbitrarySized.arbitrarySized f
        let a ← anyExprB f m
        let b ← anyExprB f m
        pure (.binaryApp op a b)),
      (1, fun _ => do
        let a ← anyExprB f m
        let k ← Basalt.ArbitrarySized.arbitrarySized f
        pure (.getAttr a k)),
      (1, fun _ => do
        let a ← anyExprB f m
        let k ← Basalt.ArbitrarySized.arbitrarySized f
        pure (.hasAttr a k)),
      (1, fun _ => do
        let j ← chooseNat 0 m
        let ks ← vectorOf j (Basalt.ArbitrarySized.arbitrarySized f)
        let k ← Basalt.ArbitrarySized.arbitrarySized f
        let a ← anyExprB f (m - j)
        pure (.extHasAttr a k ks)),
      (1, fun _ => do
        let k ← chooseNat 0 f
        let xs ← vectorOf k (anyExprB f m)
        pure (.set xs)),
      (1, fun _ => do
        let k ← chooseNat 0 f
        let axs ← vectorOf k (do
          let a ← Basalt.ArbitrarySized.arbitrarySized f
          let x ← anyExprB f m
          pure (a, x))
        pure (.record axs)),
      (1, fun _ => do
        let f' ← Basalt.ArbitrarySized.arbitrarySized f
        let k ← chooseNat 0 f
        let xs ← vectorOf k (anyExprB f m)
        pure (.call f' xs))]
  | _, _ => frequency [
      (1, fun _ => .lit <$> Basalt.ArbitrarySized.arbitrarySized 0),
      (1, fun _ => .var <$> Basalt.ArbitrarySized.arbitrarySized 0)]

/-- Any expression of depth at most `n`: `anyExprB` with fuel and budget `n`. -/
def anyExpr {G : Type → Type} [Gen G] [Specimen.Pick G] (n : Nat) : G Expr := anyExprB n n

/-- Expressions and capability keys are mostly what the relations produce; a free draw is mostly a
constant, and otherwise any expression (`anyExpr`), so that every one can be drawn. -/
instance : Basalt.ArbitrarySized Expr where
  arbitrarySized n := frequency [
    (9, fun _ => pure (.lit (.bool true))),
    (1, fun _ => anyExpr n)]

instance : Basalt.ArbitrarySized Key where
  arbitrarySized n := frequency [
    (9, fun _ => pure (.attr "")),
    (1, fun _ => .attr <$> Basalt.ArbitrarySized.arbitrarySized n),
    (1, fun _ => .tag <$> anyExpr n)]

/-! ## The producer and the check -/

/-- The expressions the dead-operand producer usually emits: literals other than entity literals,
    and variables. They meet `EntitiesDeclared` and `ParserImage` in every environment. -/
def deadOperandB : Expr → Bool
  | .lit (.bool _) | .lit (.int _) | .lit (.string _) | .var _ => true
  | _ => false

/-- A skipped operand (`DeadOperand`, the untaken branch of an `if` or the right operand of a
    short-circuited `&&`/`||`): usually a small literal or variable, and otherwise any expression
    meeting the flags' conditions. -/
instance {decl syn : Bool} {env : TypeEnv} :
    BacktrackGenFor Expr (fun x => DeadOperand decl syn env x) where
  gen _ leafSize := frequency [
    (3, fun _ => do
      let k ← chooseNat 0 3
      let b : Bool ← Basalt.ArbitrarySized.arbitrarySized leafSize
      let i : Int ← Basalt.ArbitrarySized.arbitrarySized leafSize
      let s : String ← Basalt.ArbitrarySized.arbitrarySized leafSize
      let v : Var ← Basalt.ArbitrarySized.arbitrarySized leafSize
      let x : Expr :=
        if k == 0 then .lit (.bool b)
        else if k == 1 then .lit (.int (Int64.ofInt i))
        else if k == 2 then .lit (.string s)
        else .var v
      if deadOperandB x then return x else Specimen.Fail.fail),
    (1, fun _ => do
      let x ← anyExpr leafSize
      if deadOperandOk decl syn env x then return x else Specimen.Fail.fail)]

/-- The check decides the conditions. -/
instance : DecOpt (DeadOperand decl syn env x) where
  decOpt _ := .ok (deadOperandOk decl syn env x)

/-! ### Record literals: `SortsTo`

`SortsTo axs axs'` is an insertion sort, so it is a function of `axs`. The generators' modes and the
check are written here: a derived producer of `axs` from `axs'` would search the permutations of
`axs'`. The enumerators (for the derived checkers' searches) are derived. -/

/-- `InsertSortedField`, as a function: `none` on a key already in the list. -/
def insertStrict (ax : Attr × Expr) : List (Attr × Expr) → Option (List (Attr × Expr))
  | [] => some [ax]
  | (a', x') :: rest =>
    if ax.1 < a' then some (ax :: (a', x') :: rest)
    else if a' < ax.1 then (insertStrict ax rest).map ((a', x') :: ·)
    else none

/-- `SortsTo`, as a function: the attributes sorted by key, `none` on a duplicate key. -/
def sortStrict : List (Attr × Expr) → Option (List (Attr × Expr))
  | [] => some []
  | ax :: axs => (sortStrict axs).bind (insertStrict ax)

/-- Strictly sorted by key (`<` between neighbours). -/
def strictSortedB : List (Attr × Expr) → Bool
  | (a, _) :: (b, y) :: rest => decide (a < b) && strictSortedB ((b, y) :: rest)
  | _ => true

/-- `axs` sorts to `axs'`, by computing the sort. -/
def sortsToB (axs axs' : List (Attr × Expr)) : Bool :=
  match sortStrict axs with
  | some l => l == axs'
  | none => false

instance : DecOpt (SortsTo axs axs') where
  decOpt _ := .ok (sortsToB axs axs')

/-- The sorted attributes, `axs` sorted. -/
instance {axs : List (Attr × Expr)} :
    BacktrackGenFor (List (Attr × Expr)) (fun axs' => SortsTo axs axs') where
  gen _ _ := match sortStrict axs with
    | some l => return l
    | none => Specimen.Fail.fail

/-- A record literal whose sorted attributes are `axs'`: mostly `axs'` itself, which `HasTypeRecord`
    produces strictly sorted, and otherwise a permutation of it, so every literal that sorts to it. -/
instance {axs' : List (Attr × Expr)} :
    BacktrackGenFor (List (Attr × Expr)) (fun axs => SortsTo axs axs') where
  gen _ _ := frequency [
    (3, fun _ => if strictSortedB axs' then return axs' else Specimen.Fail.fail),
    (1, fun _ => do
      let axs ← shuffle axs'
      if sortsToB axs axs' then return axs else Specimen.Fail.fail)]

end Cedar.Validation.Relational
