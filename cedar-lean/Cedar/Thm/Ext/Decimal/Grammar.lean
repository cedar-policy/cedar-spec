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
production becomes a predicate, and `IsWfDecimal` says the string is the rendering of well-formed
components — the same shape used by the duration and datetime grammars. The lemmas connecting
these definitions to `Decimal.parse` (in particular the digit-string ↔ `toInt?'`/`toNat?'`
bridges) live in `Cedar.Thm.Ext.Decimal.Lemmas`.

`Sign ::= ['-']` and `Natural ::= Digit⁺` are spelled with the shared `IsWfSign` and `IsDigits`
predicates directly, so only the decimal-specific `Fraction` needs a local definition. Those
shared predicates — along with the width refinements `IsFixedDigits`/`IsDigitsUpTo` and the
`toNat?'` bridges — live in `Cedar.Thm.Data.String`. -/

/-- The grammar's `Fraction ::= Digit{1,4}`: 1 to `DECIMAL_DIGITS` digits, an instance of the
    shared bounded-digits predicate. -/
-- ANCHOR: IsWfFrac
public def IsWfFrac (s : String) : Prop :=
  IsDigitsUpTo DECIMAL_DIGITS s
-- ANCHOR_END: IsWfFrac

/-- Well-formed decimal syntax: `s` is the rendering of a well-formed `Sign ::= ['-']`,
    `Natural ::= Digit⁺`, `'.'`, and `Fraction ::= Digit{1,4}`, concatenated in that order.
    Phrasing well-formedness existentially over the rendering bakes in the separator and the field
    order, exactly as the duration and datetime grammars do — and, unlike a split-based phrasing,
    it names the optional sign as its own production rather than folding it into the integer part.
    This is a direct transcription of the grammar's character-level productions, independent of any
    string-to-number parser. -/
-- ANCHOR: IsWfDecimal
public def IsWfDecimal (s : String) : Prop :=
  ∃ sign natural fraction,
    s = sign ++ natural ++ "." ++ fraction ∧
    IsWfSign sign ∧
    IsDigits natural ∧
    IsWfFrac fraction
-- ANCHOR_END: IsWfDecimal

/-- Compute the integer value that a decimal string represents, or `none` if the string does not
    split into an integer part and a fraction part. The grammar's value function is

      value = sign × (nat(Natural) × 10⁴ + nat(Fraction) × 10^(4 − |Fraction|))
      where sign = −1 if Sign is '-', else 1

    and this computes an equivalent regrouping of it: `toInt?'` reads the `Sign` together with the
    `Natural` digits, so the sign is already carried by the integer part and the explicit `sign`
    factor is only needed to negate the fraction.
-/
-- ANCHOR: computeValue
public def computeValue (s : String) : Option Int :=
  match s.splitToList (· = '.') with
  | [left, right] =>
    match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let sign : Int := if left.startsWith "-" then -1 else 1
        some (l * Int.pow 10 DECIMAL_DIGITS
          + sign * r * Int.pow 10 (DECIMAL_DIGITS - right.length))
      | _, _ => none
  | _ => none
-- ANCHOR_END: computeValue

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (s : String) : Option String := (Decimal.parse s).map toString

end Cedar.Thm.Decimal
