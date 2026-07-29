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

/-- Split a character sequence at its first decimal point. Unlike `String.splitToList`, this
    follows the grammar's one `Natural '.' Fraction` production directly. -/
public def splitAtDecimalPoint : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c = '.' then
      some ([], rest)
    else
      match splitAtDecimalPoint rest with
      | some (natural, fraction) => some (c :: natural, fraction)
      | none => none

/-- Compute the integer value represented by already-separated grammar fields:

      value = sign × (nat(Natural) × 10⁴ + nat(Fraction) × 10^(4 − |Fraction|))
      where sign = −1 if Sign is '-', else 1

    `toInt?'` reads the sign together with the natural digits, so the sign is already carried by
    the whole part and the explicit factor is needed only for the fraction. This is an equivalent
    regrouping of the displayed formula. -/
public def valueOfParts (sign natural fraction : String) : Option Int :=
  match toInt?' (sign ++ natural), toNat?' fraction with
  | some whole, some frac =>
    let polarity : Int := if (sign ++ natural).startsWith "-" then -1 else 1
    some (whole * Int.pow 10 DECIMAL_DIGITS
      + polarity * frac * Int.pow 10 (DECIMAL_DIGITS - fraction.length))
  | _, _ => none

/-- Compute the integer value that a decimal string represents, or `none` when the string does not
    contain a decimal point or one of its numeric fields does not parse. It peels the optional
    leading sign and follows the grammar's single `Natural '.' Fraction` production directly,
    without splitting the string into an arbitrary list of fields. -/
-- ANCHOR: computeValue
public def computeValue (s : String) : Option Int :=
  let (sign, body) := match s.toList with
    | [] => ("", [])
    | c :: rest => if c = '-' then ("-", rest) else ("", c :: rest)
  match splitAtDecimalPoint body with
  | some (natural, fraction) =>
    valueOfParts sign (String.ofList natural) (String.ofList fraction)
  | none => none
-- ANCHOR_END: computeValue

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (s : String) : Option String := (Decimal.parse s).map toString

end Cedar.Thm.Decimal
