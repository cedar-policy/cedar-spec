module

public import Cedar.Spec.Ext.Decimal
public import Std.Data.String
public import Cedar.Thm.Data.String

import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

/-! # Decimal grammar: definitions

This file contains only the grammar-level definitions — the well-formedness predicates and the
value function — as a direct, parser-independent transcription of the decimal grammar. Each
production becomes a predicate, and `IsWfDecimal` says the string is their rendering. The lemmas
connecting these definitions to `Decimal.parse` (in particular the digit-string ↔
`toInt?'`/`toNat?'` bridges) live in `Cedar.Thm.Ext.Decimal.Lemmas`.

`Sign ::= ['-']` uses the shared `IsWfSign` predicate. The decimal-specific `Natural` and
`Fraction` productions are named locally using the shared digit predicates `IsDigits` and
`IsDigitsUpTo`; their string-to-number bridges live in `Cedar.Thm.Data.String`. -/

/-- The grammar's `Natural ::= Digit⁺`: the unsigned natural-number production. An `abbrev` for
    the shared `IsDigits` predicate, so every `IsDigits` lemma applies without unfolding. -/
-- ANCHOR: IsNatural
public abbrev IsNatural (s : String) : Prop := IsDigits s
-- ANCHOR_END: IsNatural

/-- The grammar's `Fraction ::= Digit{1,4}`: 1 to `DECIMAL_DIGITS` digits, an instance of the
    shared bounded-digits predicate. -/
-- ANCHOR: IsWfFrac
public def IsWfFrac (s : String) : Prop :=
  IsDigitsUpTo DECIMAL_DIGITS s
-- ANCHOR_END: IsWfFrac

/-- Well-formed decimal syntax: `s` is the rendering of a well-formed `Sign ::= ['-']`,
    `Natural ::= Digit⁺`, `'.'`, and `Fraction ::= Digit{1,4}`, concatenated in that order.
    Phrasing well-formedness existentially over the rendering bakes in the separator and field
    order without introducing a record for this single flat production. This is a direct
    transcription of the grammar's character-level productions, independent of any
    string-to-number parser. -/
-- ANCHOR: IsWfDecimal
public def IsWfDecimal (s : String) : Prop :=
  ∃ sign natural fraction,
    s = sign ++ natural ++ "." ++ fraction ∧
    IsWfSign sign ∧
    IsNatural natural ∧
    IsWfFrac fraction
-- ANCHOR_END: IsWfDecimal

/-- Compute the integer value that a decimal string represents, or `none` if its unsigned body
    does not split into parsable `Natural` and `Fraction` fields. This directly implements the
    grammar's value function:

      value = sign × (nat(Natural) × 10⁴ + nat(Fraction) × 10^(4 − |Fraction|))
      where sign = −1 if Sign is '-', else 1
 -/
-- ANCHOR: computeValue
public def computeValue (s : String) : Option Int :=
  let (sign, body) :=
    if s.front = '-' then ((-1 : Int), (s.drop 1).copy) else (1, s)
  match body.splitToList (· = '.') with
  | [natural, fraction] =>
    match toNat?' natural, toNat?' fraction with
    | some n, some f =>
      some (sign * (n * Int.pow 10 DECIMAL_DIGITS
        + f * Int.pow 10 (DECIMAL_DIGITS - fraction.length)))
    | _, _ => none
  | _ => none
-- ANCHOR_END: computeValue

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (s : String) : Option String := (Decimal.parse s).map toString

end Cedar.Thm.Decimal
