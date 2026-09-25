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

public import Cedar.Spec.Ext.Decimal
public import Std.Data.String
public import Cedar.Thm.Data.String

import all Cedar.Spec.Ext.Decimal
import all Cedar.Spec.Ext.Util

namespace Cedar.Thm.Decimal
open Cedar.Spec.Ext
open String

/-! # Decimal grammar: definitions

This file contains only the grammar-level definitions — the well-formedness predicates and the
value relation — as a direct, parser-independent transcription of the decimal grammar.
`DecimalProduction` relates a rendering to its grammar fields, `IsWfDecimal` existentially hides
those fields, `value` gives their denotation, and `IsDecimalValue s v` adds that denotation to the
same production witness. The lemmas connecting these definitions to `Decimal.parse` (in
particular the digit-string ↔ `toInt?'`/`toNat?'` bridges) live in
`Cedar.Thm.Ext.Decimal.Lemmas`.

`Sign ::= ['-']` uses the shared `IsWfSign` predicate. The decimal-specific `Natural` and
`Fraction` productions are named locally using the shared digit predicates `IsDigits` and
`IsAtMostNDigits`. Their value readers (`natOf`, `signOf`, and `lenOf`) and string-to-number bridges
live in `Cedar.Thm.Data.String`. -/

/-- The grammar's `Natural ::= Digit⁺`: the unsigned natural-number production. An `abbrev` for
    the shared `IsDigits` predicate, so every `IsDigits` lemma applies without unfolding. -/
-- ANCHOR: IsNatural
public abbrev IsNatural (s : String) : Prop := IsDigits s
-- ANCHOR_END: IsNatural

/-- The grammar's `Fraction ::= Digit{1,4}`: 1 to `DECIMAL_DIGITS` digits, an instance of the
    shared bounded-digits predicate. -/
-- ANCHOR: IsWfFrac
public def IsWfFrac (s : String) : Prop :=
  IsAtMostNDigits DECIMAL_DIGITS s
-- ANCHOR_END: IsWfFrac

/-- A decimal grammar production: `s` is the rendering of well-formed `Sign`, `Natural`, and
    `Fraction` fields, concatenated around the literal decimal point. -/
-- ANCHOR: DecimalProduction
public def DecimalProduction (s sign natural fraction : String) : Prop :=
  s = sign ++ natural ++ "." ++ fraction ∧
  IsWfSign sign ∧
  IsNatural natural ∧
  IsWfFrac fraction
-- ANCHOR_END: DecimalProduction

/-- Well-formed decimal syntax: `s` is the rendering of a well-formed `Sign ::= ['-']`,
    `Natural ::= Digit⁺`, `'.'`, and `Fraction ::= Digit{1,4}`, concatenated in that order.
    This is the direct grammar transcription; it does not compute a value or invoke a parser. -/
-- ANCHOR: IsWfDecimal
public def IsWfDecimal (s : String) : Prop :=
  ∃ sign natural fraction, DecimalProduction s sign natural fraction
-- ANCHOR_END: IsWfDecimal

/-- The grammar's value function, applied to an already-decomposed literal:

      value = sign × (nat(Natural) × 10⁴ + nat(Fraction) × 10^(4 − |Fraction|))

    `IsWfFrac fraction` bounds `lenOf fraction ≤ DECIMAL_DIGITS`, so converting the second
    exponent to `Nat` does not clamp a negative value on a well-formed field. -/
-- ANCHOR: value
public def value (sign natural fraction : String) : Int :=
  signOf sign *
    ((natOf natural : Int) * Int.pow 10 DECIMAL_DIGITS
     + (natOf fraction : Int) * Int.pow 10 ((DECIMAL_DIGITS : Int) - lenOf fraction).toNat)
-- ANCHOR_END: value

/-- `v` is the value of the decimal literal `s`: `s` is the rendering of a well-formed
    `Sign ::= ['-']`, `Natural ::= Digit⁺`, `'.'`, and `Fraction ::= Digit{1,4}`, concatenated in
    that order, and `v` is what the grammar's value function assigns to those fields.

    The existential supplies the split, so no string surgery (`front`/`drop`/`splitToList`) and no
    `Option` appear here. The relation is single-valued (`isDecimalValue_unique`), and a string is
    well-formed exactly when it has some value (`wf_iff_exists_value`). -/
-- ANCHOR: IsDecimalValue
public def IsDecimalValue (s : String) (v : Int) : Prop :=
  ∃ sign natural fraction,
    DecimalProduction s sign natural fraction ∧
    v = value sign natural fraction
-- ANCHOR_END: IsDecimalValue

/-- Canonical-form normalizer: parse the string and re-serialize.
    Returns `none` for malformed or out-of-range inputs. -/
public def normalize (s : String) : Option String := (Decimal.parse s).map toString

end Cedar.Thm.Decimal
