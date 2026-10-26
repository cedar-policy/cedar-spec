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

public import CedarRustModel.Ext.Datetime
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.CheckedOps.Mul

/-! The duration parser of the model computes `XL.parseDuration`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model

@[expose] public section

namespace XL

def takeUnit (u : Char) (noS : Bool) (l : _root_.List Char) : Option (_root_.List Char) × _root_.List Char :=
  if l.takeWhile Char.isDigit = [] then (none, l)
  else match l.dropWhile Char.isDigit with
    | [] => (none, l)
    | c :: rest2 =>
      if c = u then (if noS ∧ rest2.head? = some 's' then (none, l) else (some (l.takeWhile Char.isDigit), rest2))
      else (none, l)

def takeMs (l : _root_.List Char) : Option (_root_.List Char) × _root_.List Char :=
  if l.takeWhile Char.isDigit = [] then (none, l)
  else match takeChar 'm' (l.dropWhile Char.isDigit) with
    | none => (none, l)
    | some r1 => match takeChar 's' r1 with
      | none => (none, l)
      | some r2 => (some (l.takeWhile Char.isDigit), r2)

structure DP where
  d : Option (_root_.List Char)
  h : Option (_root_.List Char)
  m : Option (_root_.List Char)
  s : Option (_root_.List Char)
  ms : Option (_root_.List Char)

def durBody : _root_.List Char → _root_.List Char
  | [] => []
  | c :: rest => if c = '-' then rest else c :: rest

def durationRegex (l : _root_.List Char) : Option DP :=
  let b := durBody l
  let (d, r1) := takeUnit 'd' false b
  let (h, r2) := takeUnit 'h' false r1
  let (m, r3) := takeUnit 'm' true r2
  let (sec, r4) := takeUnit 's' false r3
  let (ms, r5) := takeMs r4
  if r5 = [] then some ⟨d, h, m, sec, ms⟩ else none

def durQuantity : Option (_root_.List Char) → Option Nat
  | none => some 0
  | some ds => parseU64' ds

def durStep (acc : Int) (y : Nat) (mul : Int) (neg : Bool) : Option Int :=
  if y > 9223372036854775807 then none
  else if inI64 (y * mul) then chk (if neg then acc - y * mul else acc + y * mul)
  else none

def durInit (ms : Nat) (neg : Bool) : Option Int :=
  if neg then (if ms ≤ 9223372036854775808 then some (-(ms : Int)) else none)
  else (if ms ≤ 9223372036854775807 then some ms else none)

def parseDuration (l : _root_.List Char) : Option Int :=
  if l = [] then none
  else if l = ['-'] then none
  else match durationRegex l with
    | none => none
    | some p =>
      let neg := decide (l.head? = some '-')
      match durQuantity p.d, durQuantity p.h, durQuantity p.m, durQuantity p.s, durQuantity p.ms with
      | some d, some h, some m, some sec, some ms =>
        (durInit ms neg).bind fun a0 => (durStep a0 sec 1000 neg).bind fun a1 =>
          (durStep a1 m 60000 neg).bind fun a2 => (durStep a2 h 3600000 neg).bind fun a3 =>
            durStep a3 d 86400000 neg
      | _, _, _, _, _ => none

end XL

end

public section

def optToSpec (o : Option (value.List Char)) : Option (_root_.List Char) := o.map List.toList

@[step] theorem take_unit_spec (s : value.List Char) (u : Char) (noS : Bool) :
    ext.take_unit s u noS ⦃ r => XL.takeUnit u noS (List.toList s) = (optToSpec r.1, List.toList r.2) ⦄ := by
  unfold ext.take_unit
  obtain ⟨⟨ds, rest⟩, h1, hds, hrest⟩ := spec_ok_exists (span_digits_spec s)
  rw [h1]; simp only [bind_ok]
  simp only [XL.takeUnit, ← hds, ← hrest]
  cases ds with
  | Nil => simp [ext.is_empty, clone_str_ok, WP.spec_ok, optToSpec]
  | Cons d ds =>
    cases rest with
    | Nil => simp [ext.is_empty, clone_str_ok, WP.spec_ok, optToSpec]
    | Cons c rest2 =>
      by_cases hc : c = u
      · subst hc
        cases noS <;> cases rest2 <;>
          simp [ext.is_empty, ext.starts_with, clone_str_ok, WP.spec_ok, optToSpec] <;> split <;> simp_all
      · simp [ext.is_empty, clone_str_ok, WP.spec_ok, optToSpec, hc]


@[step] theorem take_ms_spec (s : value.List Char) :
    ext.take_ms s ⦃ r => XL.takeMs (List.toList s) = (optToSpec r.1, List.toList r.2) ⦄ := by
  unfold ext.take_ms
  xstep
  all_goals (subst_vars; simp_all [XL.takeMs, optToSpec, clone_str_ok])

def dpToSpec (p : ext.DurParts) : XL.DP :=
  ⟨optToSpec p.d, optToSpec p.h, optToSpec p.m, optToSpec p.s, optToSpec p.ms⟩

@[step] theorem duration_regex_spec (s : value.List Char) :
    ext.duration_regex s ⦃ r => XL.durationRegex (List.toList s) = r.map dpToSpec ⦄ := by
  unfold ext.duration_regex
  cases s with
  | Nil =>
    simp only [bind_ok]
    xstep
    all_goals (subst_vars; simp_all [XL.durationRegex, XL.durBody, dpToSpec, optToSpec])
  | Cons c rest =>
    by_cases hc : c = '-'
    · simp only [hc, ite_true, clone_str_ok, bind_ok]
      xstep
      all_goals (subst_vars; simp_all [XL.durationRegex, XL.durBody, dpToSpec, optToSpec])
    · simp only [hc, ite_false, clone_str_ok, bind_ok]
      xstep
      all_goals (subst_vars; simp_all [XL.durationRegex, XL.durBody, dpToSpec, optToSpec])

@[step] theorem dur_quantity_spec (q : Option (value.List Char)) :
    ext.dur_quantity q ⦃ r => XL.durQuantity (optToSpec q) = r.map (·.val) ⦄ := by
  unfold ext.dur_quantity
  cases q with
  | none => simp [XL.durQuantity, optToSpec, WP.spec_ok]
  | some ds => simpa [XL.durQuantity, optToSpec] using parse_u64_spec ds

@[step] theorem dur_step_spec (acc : I64) (y : U64) (mul : I64) (neg : Bool) :
    ext.dur_step acc y mul neg ⦃ r => XL.durStep acc.val y.val mul.val neg = r.map (·.val) ⦄ := by
  unfold ext.dur_step
  by_cases hy : y > 9223372036854775807#u64
  · have : y.val > 9223372036854775807 := by scalar_tac
    simp [hy, XL.durStep, this, WP.spec_ok]
  · have hy' : ¬ y.val > 9223372036854775807 := by scalar_tac
    simp only [hy, ite_false]
    step*
    all_goals (try rw [I64.checked_add_val])
    all_goals (try rw [I64.checked_sub_val])
    all_goals (simp only [XL.durStep, hy', ite_false]; simp_all [XL.chk])

@[step] theorem dur_init_spec (ms : U64) (neg : Bool) :
    ext.dur_init ms neg ⦃ r => XL.durInit ms.val neg = r.map (·.val) ⦄ := by
  unfold ext.dur_init
  cases neg <;> step* <;> simp_all [XL.durInit] <;> scalar_tac

@[step] theorem parse_duration_spec (s : value.List Char) :
    ext.parse_duration s ⦃ r => XL.parseDuration (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.parse_duration
  xstep
  all_goals (subst_vars; simp_all [XL.parseDuration, dpToSpec, ms_per_day_val])

end

end CedarRustModel
