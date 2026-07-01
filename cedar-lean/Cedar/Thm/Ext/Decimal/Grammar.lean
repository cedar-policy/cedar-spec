module

public import Cedar.Spec.Ext.Decimal
public import Std.Data.String

import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

/-! # Decimal grammar: definitions

This file contains only the grammar-level definitions — the well-formedness predicates and the
value function — as a direct, parser-independent transcription of the decimal grammar. The lemmas
connecting these definitions to `Decimal.parse` (in particular the digit-string ↔ `toInt?'`/
`toNat?'` bridges) live in `Cedar.Thm.Ext.Decimal.Lemmas`. -/

/-- `Digit⁺`: a non-empty string all of whose characters are decimal digits. -/
public def IsDigits (s : String) : Prop :=
  0 < s.length ∧ ∀ c ∈ s.toList, c.isDigit = true

/-- The grammar's `Integer ::= ['-'] Digit⁺`: either a bare non-empty digit string, or a
    `'-'` followed by one. The `∃ t` branch requires `IsDigits t`, so a bare `"-"` is
    excluded — this is what the grammar's `Digit⁺` (at least one digit) buys us. -/
public def IsWfInt (s : String) : Prop :=
  IsDigits s ∨ ∃ t, s = "-" ++ t ∧ IsDigits t

/-- Well-formed decimal syntax: `s` splits on `.` into exactly two parts, where the left part
    matches the grammar's `Integer ::= ['-'] Digit⁺` and the right part is a fraction of 1 to
    `DECIMAL_DIGITS` digits (`Digit{1,4}`). This is a direct transcription of the grammar's
    character-level productions, independent of any string-to-number parser. -/
public def IsWfStr (s : String) : Prop :=
 ∃ left right,
    s.splitToList (· = '.') = [left, right] ∧
    IsWfInt left ∧
    IsDigits right ∧
    right.length ≤ DECIMAL_DIGITS

/-- Compute the integer value that a decimal string represents, or `none` if the string does not
    split into an integer part and a fraction part. This mirrors the
    grammar's value function directly:

      value = int(Integer) × 10⁴ + sign × nat(Fraction) × 10^(4 − |Fraction|)
      where sign = −1 if Integer starts with '-', else 1
-/
public def computeValue (s : String) : Option Int :=
  match s.splitToList (· = '.') with
  | [left, right] =>
    match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let sign : Int := if left.startsWith "-" then -1 else 1
        some (l * Int.pow 10 DECIMAL_DIGITS
          + sign * (r : Int) * Int.pow 10 (DECIMAL_DIGITS - right.length))
      | _, _ => none
  | _ => none

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (s : String) : Option String := (Decimal.parse s).map toString

end Cedar.Thm.Decimal
