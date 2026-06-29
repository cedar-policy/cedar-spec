module

public import Cedar.Spec.Ext.Decimal

import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext

public def IsWfStr (s : String) : Prop :=
 ∃ left right,
    s.splitToList (· = '.') = [left, right] ∧
    left ≠ "-" ∧
    0 < right.length ∧
    right.length ≤ DECIMAL_DIGITS ∧
    (toInt?' left).isSome ∧
    (toNat?' right).isSome

/-- Compute the integer value that a well-formed decimal string represents.
    Returns a junk value (0) for malformed inputs; only meaningful under `IsWfStr`. -/
public def computeValue (s : String) : Int :=
  match s.splitToList (· = '.') with
  | [left, right] =>
    let rlen := right.length
    match toInt?' left, toNat?' right with
      | .some l, .some r =>
        let l' := l * (Int.pow 10 DECIMAL_DIGITS)
        let r' := r * (Int.pow 10 (DECIMAL_DIGITS - rlen))
        let i  := if !left.startsWith "-" then l' + r' else l' - r'
        i
      | _, _ => 0
  | _ => 0

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (s : String) : Option String := (Decimal.parse s).map toString

end Cedar.Thm.Decimal
