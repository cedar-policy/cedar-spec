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
production (`Sign`, `Natural`, `Fraction`) gets its own predicate, and `IsWfDecimal` says the
string is the rendering of well-formed components, the same shape used by the duration and
datetime grammars. The lemmas connecting these definitions to `Decimal.parse` (in particular the
digit-string ↔ `toInt?'`/`toNat?'` bridges) live in `Cedar.Thm.Ext.Decimal.Lemmas`. The `Digit⁺`
predicate `IsDigits` and its `toNat?'` bridges are shared with the duration grammar and live in
`Cedar.Thm.Data.String`. -/

/-- The grammar's `Sign ::= ['-']`: the optional leading minus, present or absent. -/
-- ANCHOR: IsWfSign
public def IsWfSign (s : String) : Prop :=
  s = "-" ∨ s = ""
-- ANCHOR_END: IsWfSign

/-- The grammar's `Natural ::= Digit⁺`: a non-empty digit string. -/
-- ANCHOR: IsWfNat
public def IsWfNat (s : String) : Prop :=
  IsDigits s
-- ANCHOR_END: IsWfNat

/-- The grammar's `Fraction ::= Digit{1,4}`: 1 to `DECIMAL_DIGITS` digits. `IsDigits` supplies
    the lower bound (at least one digit) and the length constraint supplies the upper bound. -/
-- ANCHOR: IsWfFrac
public def IsWfFrac (s : String) : Prop :=
  IsDigits s ∧ s.length ≤ DECIMAL_DIGITS
-- ANCHOR_END: IsWfFrac

/-- Well-formed decimal syntax: `s` is the rendering of a well-formed `Sign`, `Natural`, `'.'`,
    and `Fraction`, concatenated in that order. Phrasing well-formedness existentially over the
    rendering bakes in the separator and the field order, exactly as the duration and datetime
    grammars do — and, unlike a split-based phrasing, it names the optional sign as its own
    production rather than folding it into the integer part. This is a direct transcription of the
    grammar's character-level productions, independent of any string-to-number parser. -/
-- ANCHOR: IsWfDecimal
public def IsWfDecimal (s : String) : Prop :=
  ∃ sign natural fraction,
    s = sign ++ natural ++ "." ++ fraction ∧
    IsWfSign sign ∧
    IsWfNat natural ∧
    IsWfFrac fraction
-- ANCHOR_END: IsWfDecimal

/-- Compute the integer value that a decimal string represents, or `none` if the string does not
    split into an integer part and a fraction part. This mirrors the
    grammar's value function directly:

      value = int(Integer) × 10⁴ + sign × nat(Fraction) × 10^(4 − |Fraction|)
      where sign = −1 if Integer starts with '-', else 1
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
