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

public import CedarRustModel.Ext.Convert
public import CedarRustModel.Lemmas.Basic
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.CheckedOps.Mul

/-!
Characters, strings and integer parsing in the extension model: each model
function computes a pure Lean function on lists (the "shadow" of the model
function, in namespace `CedarRustModel.XL`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model

/-- Closes `b = decide p` given `b = decide q` (with `p ↔ q` by `omega`) -/
macro "dec_tac" : tactic => `(tactic| first
  | (subst_vars; simp only [decide_eq_decide]; constructor <;> intro <;> scalar_tac)
  | (simp only [@eq_comm _ false, @eq_comm _ true, decide_eq_false_iff_not, decide_eq_true_eq];
     scalar_tac))

/-- `step*`, destructuring pairs as they appear -/
macro "xstep" : tactic => `(tactic| (step*; repeat' (casesm _ × _; try step*)))

@[expose] public section

/-! ## Shadows -/

namespace XL

/-- The UTF-8 length of a list of characters -/
def utf8Len (l : _root_.List Char) : Nat := (l.map Char.utf8Size).sum

/-- `l` split at the first `c` -/
def splitFirst (c : Char) : _root_.List Char → Option (_root_.List Char × _root_.List Char)
  | [] => none
  | d :: l => if d = c then some ([], l) else (splitFirst c l).map fun (a, b) => (d :: a, b)

/-- Adds `d` to the front of the first part -/
def consFirst (d : Char) : _root_.List (_root_.List Char) → _root_.List (_root_.List Char)
  | p :: ps => (d :: p) :: ps
  | [] => [[d]]

/-- `l` split at every `c` -/
def splitAll (c : Char) : _root_.List Char → _root_.List (_root_.List Char)
  | [] => [[]]
  | d :: l => if d = c then [] :: splitAll c l else consFirst d (splitAll c l)

/-- The value of a list of digits, accumulated onto `acc` -/
def digitsVal (acc : Nat) (l : _root_.List Char) : Nat :=
  l.foldl (fun a c => a * 10 + (c.toNat - 48)) acc

def allDigits (l : _root_.List Char) : Bool := l.all Char.isDigit

def inI64 (i : Int) : Bool := decide (I64.min ≤ i ∧ i ≤ I64.max)

/-- `i64::from_str` -/
def parseI64 : _root_.List Char → Option Int
  | [] => none
  | c :: rest =>
    if c = '-' then
      if rest ≠ [] ∧ allDigits rest ∧ inI64 (-(digitsVal 0 rest : Int)) then
        some (-(digitsVal 0 rest : Int)) else none
    else if c = '+' then
      if rest ≠ [] ∧ allDigits rest ∧ inI64 (digitsVal 0 rest) then
        some (digitsVal 0 rest) else none
    else if allDigits (c :: rest) ∧ inI64 (digitsVal 0 (c :: rest)) then
      some (digitsVal 0 (c :: rest)) else none

/-- `u64::from_str` -/
def parseU64 : _root_.List Char → Option Nat
  | [] => none
  | c :: rest =>
    if c = '+' then
      if rest ≠ [] ∧ allDigits rest ∧ digitsVal 0 rest ≤ U64.max then
        some (digitsVal 0 rest) else none
    else if allDigits (c :: rest) ∧ digitsVal 0 (c :: rest) ≤ U64.max then
      some (digitsVal 0 (c :: rest)) else none

/-- `l` without its first `n` characters, if they are digits -/
def takeDigits (n : Nat) (l : _root_.List Char) : Option (_root_.List Char × _root_.List Char) :=
  if n ≤ l.length ∧ allDigits (l.take n) then some (l.take n, l.drop n) else none

def takeChar (c : Char) : _root_.List Char → Option (_root_.List Char)
  | d :: l => if d = c then some l else none
  | [] => none

/-- The model's `digits_i64` -/
def digI64 (neg : Bool) (acc : Int) : _root_.List Char → Option Int
  | [] => some acc
  | c :: l =>
    if c.isDigit ∧ inI64 (acc * 10) ∧
        inI64 (if neg then acc * 10 - (c.toNat - 48 : Nat) else acc * 10 + (c.toNat - 48 : Nat))
    then digI64 neg (if neg then acc * 10 - (c.toNat - 48 : Nat) else acc * 10 + (c.toNat - 48 : Nat)) l
    else none

/-- The model's `digits_u64` -/
def digU64 (acc : Nat) : _root_.List Char → Option Nat
  | [] => some acc
  | c :: l =>
    if c.isDigit ∧ acc * 10 ≤ U64.max ∧ acc * 10 + (c.toNat - 48) ≤ U64.max
    then digU64 (acc * 10 + (c.toNat - 48)) l
    else none

/-- The model's `parse_i64` -/
def parseI64' : _root_.List Char → Option Int
  | [] => none
  | c :: rest =>
    if c = '-' then (if rest = [] then none else digI64 true 0 rest)
    else if c = '+' then (if rest = [] then none else digI64 false 0 rest)
    else digI64 false 0 (c :: rest)

/-- The model's `parse_u64` -/
def parseU64' : _root_.List Char → Option Nat
  | [] => none
  | c :: rest =>
    if c = '+' then (if rest = [] then none else digU64 0 rest)
    else digU64 0 (c :: rest)

def isSignedDigits : _root_.List Char → Bool
  | [] => false
  | c :: rest => if c = '-' then (!rest.isEmpty && allDigits rest) else (!(c :: rest).isEmpty && allDigits (c :: rest))

def decimalSplit (l : _root_.List Char) : Option (_root_.List Char × _root_.List Char) :=
  match splitFirst '.' l with
  | some (a, b) => if isSignedDigits a && (!b.isEmpty && allDigits b) then some (a, b) else none
  | none => none

def fracScale (l : _root_.List Char) : Option Int :=
  match l.length with
  | 1 => some 1000
  | 2 => some 100
  | 3 => some 10
  | 4 => some 1
  | _ => none

/-- The model's `parse_decimal` -/
def parseDecimal (l : _root_.List Char) : Option Int :=
  match decimalSplit l with
  | none => none
  | some (a, b) =>
    match parseI64' a with
    | none => none
    | some lv =>
      if inI64 (lv * 10000) then
        match fracScale b with
        | none => none
        | some k =>
          match parseI64' b with
          | none => none
          | some rv =>
            if inI64 (rv * k) then
              let v := if a.head? = some '-' then lv * 10000 - rv * k else lv * 10000 + rv * k
              if inI64 v then some v else none
            else none
      else none

/-- `u8::from_str` -/
def parseU8 (l : _root_.List Char) : Option Nat :=
  (parseU64' l).bind fun n => if n ≤ 255 then some n else none

/-- Checked `i64` arithmetic -/
def chk (v : Int) : Option Int := if inI64 v then some v else none

end XL

end

public section

/-! ## Truncating division -/

@[step] theorem tdiv_spec (x k : I64) (hk : 0 < k.val) :
    ext.tdiv x k ⦃ r => r.val = x.val.tdiv k.val ⦄ := by
  unfold ext.tdiv
  step
  assumption

@[step] theorem tmod_spec (x k : I64) (hk : 0 < k.val) :
    ext.tmod x k ⦃ r => r.val = x.val.tmod k.val ⦄ := by
  unfold ext.tmod
  step
  assumption

/-! ## Characters -/

@[step] theorem char_code_spec (c : Char) : ext.char_code c ⦃ n => n.val = c.toNat ⦄ := by
  simp [ext.char_code, WP.spec_ok]; rfl

theorem isDigit_iff (c : Char) : c.isDigit = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [Char.isDigit, ge_iff_le, UInt32.le_iff_toNat_le, Bool.and_eq_true, decide_eq_true_eq]
  exact Iff.rfl

@[step] theorem digit_val_spec (c : Char) :
    ext.digit_val c ⦃ o => match o with
       | some d => c.isDigit = true ∧ d.val = c.toNat - 48
       | none => c.isDigit = false ⦄ := by
  unfold ext.digit_val
  step*
  all_goals (simp only [Bool.eq_false_iff, ne_eq, isDigit_iff] at *; scalar_tac)

@[step] theorem is_digit_spec (c : Char) : ext.is_digit c ⦃ b => b = c.isDigit ⦄ := by
  unfold ext.is_digit
  step*

/-- `toHexNat` of `Cedar.Spec.Ext.IPAddr` -/
@[expose] def XL.hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else c.toNat

/-- `isHexDigit` of `Cedar.Spec.Ext.IPAddr` -/
@[expose] def XL.isHex (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

theorem char_le_iff (c d : Char) : c ≤ d ↔ c.toNat ≤ d.toNat := by
  simp only [Char.le_def, UInt32.le_iff_toNat_le]; exact Iff.rfl

theorem char_lit_vals : '0'.val.toNat = 48 ∧ 'a'.val.toNat = 97 ∧ 'f'.val.toNat = 102 ∧
    'A'.val.toNat = 65 ∧ 'F'.val.toNat = 70 := by decide

@[step] theorem hex_val_spec (c : Char) :
    ext.hex_val c ⦃ o => match o with
       | some d => XL.isHex c = true ∧ d.val = XL.hexVal c
       | none => XL.isHex c = false ⦄ := by
  unfold ext.hex_val
  step*
  all_goals (simp only [XL.isHex, XL.hexVal, Bool.eq_false_iff, ne_eq, isDigit_iff, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, char_le_iff] at *)
  all_goals (try split_ifs) <;> (try simp only [Char.toNat] at *) <;>
    (have := char_lit_vals; scalar_tac)

theorem utf8Size_eq (c : Char) :
    c.utf8Size = if c.toNat < 0x80 then 1 else if c.toNat < 0x800 then 2
      else if c.toNat < 0x10000 then 3 else 4 := by
  rw [Char.utf8Size]
  simp only [Char.toNat, UInt32.le_iff_toNat_le]
  split_ifs <;> simp_all <;> omega

@[step] theorem utf8_width_spec (c : Char) : ext.utf8_width c ⦃ k => k.val = c.utf8Size ⦄ := by
  unfold ext.utf8_width
  step*
  all_goals (rw [utf8Size_eq]; split_ifs <;> scalar_tac)

/-! ## Lists -/

@[simp] theorem XL.utf8Len_nil : XL.utf8Len [] = 0 := rfl
@[simp] theorem XL.utf8Len_cons (c : Char) (l : _root_.List Char) :
    XL.utf8Len (c :: l) = c.utf8Size + XL.utf8Len l := by simp [XL.utf8Len]

@[step] theorem utf8_len_le_spec (s : value.List Char) (n : U32) :
    ext.utf8_len_le s n ⦃ b => b = decide (XL.utf8Len (List.toList s) ≤ n.val) ⦄ := by
  induction s generalizing n with
  | Nil => rw [ext.utf8_len_le.eq_def]; simp [WP.spec_ok]
  | Cons c rest ih =>
    rw [ext.utf8_len_le.eq_def]
    step*
    all_goals (simp only [List.toList_cons, XL.utf8Len_cons] at *)
    all_goals dec_tac

@[step] theorem is_empty_spec (s : value.List Char) :
    ext.is_empty s ⦃ b => b = (List.toList s).isEmpty ⦄ := by
  cases s <;> simp [ext.is_empty, WP.spec_ok]

@[step] theorem starts_with_spec (s : value.List Char) (c : Char) :
    ext.starts_with s c ⦃ b => b = decide ((List.toList s).head? = some c) ⦄ := by
  cases s <;> simp [ext.starts_with, WP.spec_ok]

@[step] theorem is_char_spec (s : value.List Char) (c : Char) :
    ext.is_char s c ⦃ b => b = decide (List.toList s = [c]) ⦄ := by
  unfold ext.is_char
  cases s with
  | Nil => simp [WP.spec_ok]
  | Cons d rest => step* <;> cases rest <;> simp_all <;> grind

@[step] theorem len_le_spec {T : Type} (s : value.List T) (n : U32) :
    ext.len_le s n ⦃ b => b = decide ((List.toList s).length ≤ n.val) ⦄ := by
  induction s generalizing n with
  | Nil => rw [ext.len_le.eq_def]; simp [WP.spec_ok]
  | Cons c rest ih =>
    rw [ext.len_le.eq_def]
    step*
    all_goals (subst_vars; simp <;> scalar_tac)

@[step] theorem has_one_spec (s : value.List Char) (c : Char) :
    ext.has_one s c ⦃ b => b = decide (c ∈ List.toList s) ⦄ := by
  induction s with
  | Nil => rw [ext.has_one.eq_def]; simp [WP.spec_ok]
  | Cons d rest ih =>
    rw [ext.has_one.eq_def]
    step*
    all_goals (simp_all [eq_comm])

@[step] theorem has_two_spec (s : value.List Char) (c : Char) :
    ext.has_two s c ⦃ b => b = decide (2 ≤ (List.toList s).count c) ⦄ := by
  induction s with
  | Nil => rw [ext.has_two.eq_def]; simp [WP.spec_ok]
  | Cons d rest ih =>
    rw [ext.has_two.eq_def]
    step*
    all_goals (simp_all [_root_.List.count_cons, _root_.List.count_pos_iff] <;> omega)

@[step] theorem all_digits_spec (s : value.List Char) :
    ext.all_digits s ⦃ b => b = XL.allDigits (List.toList s) ⦄ := by
  induction s with
  | Nil => rw [ext.all_digits.eq_def]; simp [WP.spec_ok, XL.allDigits]
  | Cons d rest ih =>
    rw [ext.all_digits.eq_def]
    step*
    all_goals (simp_all [XL.allDigits])

@[step] theorem is_digits_spec (s : value.List Char) :
    ext.is_digits s ⦃ b => b = (!(List.toList s).isEmpty && XL.allDigits (List.toList s)) ⦄ := by
  unfold ext.is_digits
  step*
  all_goals simp_all

@[simp] theorem XL.allDigits_nil : XL.allDigits [] = true := rfl
@[simp] theorem XL.allDigits_cons (c : Char) (l : _root_.List Char) :
    XL.allDigits (c :: l) = (c.isDigit && XL.allDigits l) := rfl

@[step] theorem clone_str_spec (s : value.List Char) : value.clone_str s ⦃ r => r = s ⦄ := by
  rw [clone_str_ok]; simp [WP.spec_ok]

@[step] theorem split_at_char_spec (s : value.List Char) (c : Char) :
    ext.split_at_char s c ⦃ r =>
      XL.splitFirst c (List.toList s) = r.map (fun p => (List.toList p.1, List.toList p.2)) ⦄ := by
  induction s with
  | Nil => rw [ext.split_at_char.eq_def]; simp [WP.spec_ok, XL.splitFirst]
  | Cons d rest ih =>
    rw [ext.split_at_char.eq_def]
    step*
    all_goals (try obtain ⟨_, _⟩ := p)
    all_goals (subst_vars; simp_all [XL.splitFirst])

@[step] theorem split_all_spec (s : value.List Char) (c : Char) :
    ext.split_all s c ⦃ r => XL.splitAll c (List.toList s) = (List.toList r).map List.toList ⦄ := by
  induction s with
  | Nil => rw [ext.split_all.eq_def]; simp [WP.spec_ok, XL.splitAll]
  | Cons d rest ih =>
    rw [ext.split_all.eq_def]
    step*
    all_goals (subst_vars; simp_all [XL.splitAll, XL.consFirst])

@[step] theorem span_digits_spec (s : value.List Char) :
    ext.span_digits s ⦃ r => List.toList r.1 = (List.toList s).takeWhile Char.isDigit ∧
      List.toList r.2 = (List.toList s).dropWhile Char.isDigit ⦄ := by
  induction s with
  | Nil => rw [ext.span_digits.eq_def]; simp [WP.spec_ok]
  | Cons d rest ih =>
    rw [ext.span_digits.eq_def]
    step*
    all_goals (subst_vars; simp_all [_root_.List.takeWhile_cons, _root_.List.dropWhile_cons])

theorem XL.takeDigits_zero (l : _root_.List Char) : XL.takeDigits 0 l = some ([], l) := by
  simp [XL.takeDigits]

theorem XL.takeDigits_nil (n : Nat) (h : n ≠ 0) : XL.takeDigits n [] = none := by
  simp [XL.takeDigits]; omega

theorem XL.takeDigits_cons (n : Nat) (d : Char) (l : _root_.List Char) (h : n ≠ 0) :
    XL.takeDigits n (d :: l) =
      if d.isDigit then (XL.takeDigits (n - 1) l).map (fun p => (d :: p.1, p.2)) else none := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [XL.takeDigits, _root_.List.length_cons, _root_.List.take_succ_cons,
    _root_.List.drop_succ_cons, XL.allDigits_cons, Nat.add_sub_cancel]
  by_cases hd : d.isDigit <;> by_cases hk : k ≤ l.length <;> by_cases ha : XL.allDigits (l.take k) <;>
    simp_all

@[step] theorem take_digits_spec (s : value.List Char) (n : U32) :
    ext.take_digits s n ⦃ r =>
      XL.takeDigits n.val (List.toList s) = r.map (fun p => (List.toList p.1, List.toList p.2)) ⦄ := by
  induction s generalizing n with
  | Nil =>
    rw [ext.take_digits.eq_def]
    step*
    all_goals (simp_all [XL.takeDigits, WP.spec_ok]; try scalar_tac)
  | Cons d rest ih =>
    rw [ext.take_digits.eq_def]
    step*
    · subst_vars; simp [XL.takeDigits_zero, WP.spec_ok]
    · subst_vars
      rw [List.toList_cons, XL.takeDigits_cons _ _ _ (by scalar_tac)]
      have : (↑n : Nat) - 1 = ↑i := by scalar_tac
      have hd : d.isDigit = true := by simp_all
      rw [if_pos hd, this, o_post]; simp [WP.spec_ok]
    · obtain ⟨a, b⟩ := p
      subst_vars
      rw [List.toList_cons, XL.takeDigits_cons _ _ _ (by scalar_tac)]
      have : (↑n : Nat) - 1 = ↑i := by scalar_tac
      have hd : d.isDigit = true := by simp_all
      rw [if_pos hd, this, o_post]; simp [WP.spec_ok]
    · subst_vars
      rw [List.toList_cons, XL.takeDigits_cons _ _ _ (by scalar_tac)]
      simp_all [WP.spec_ok]

@[step] theorem take_char_spec (s : value.List Char) (c : Char) :
    ext.take_char s c ⦃ r => XL.takeChar c (List.toList s) = r.map List.toList ⦄ := by
  unfold ext.take_char
  cases s with
  | Nil => simp [XL.takeChar, WP.spec_ok]
  | Cons d rest => step* <;> simp_all [XL.takeChar, WP.spec_ok]

theorem I64.checked_mul_val (x y : I64) :
    (I64.checked_mul x y).map (·.val) = if XL.inI64 (x.val * y.val) then some (x.val * y.val) else none := by
  have := I64.checked_mul_bv_spec x y
  simp only [I64.checked_mul]
  split at this <;> rename_i h <;> rw [h] <;> simp_all [XL.inI64]

theorem I64.checked_add_val (x y : I64) :
    (I64.checked_add x y).map (·.val) = if XL.inI64 (x.val + y.val) then some (x.val + y.val) else none := by
  have := I64.checked_add_bv_spec x y
  simp only [I64.checked_add]
  split at this <;> rename_i h <;> rw [h] <;> simp_all [XL.inI64]

theorem I64.checked_sub_val (x y : I64) :
    (I64.checked_sub x y).map (·.val) = if XL.inI64 (x.val - y.val) then some (x.val - y.val) else none := by
  have := I64.checked_sub_bv_spec x y
  simp only [I64.checked_sub]
  split at this <;> rename_i h <;> rw [h] <;> simp_all [XL.inI64]

theorem U64.checked_mul_val (x y : U64) :
    (U64.checked_mul x y).map (·.val) = if x.val * y.val ≤ U64.max then some (x.val * y.val) else none := by
  have := U64.checked_mul_bv_spec x y
  split at this <;> rename_i h <;> rw [h] <;> simp_all

theorem U64.checked_add_val (x y : U64) :
    (U64.checked_add x y).map (·.val) = if x.val + y.val ≤ U64.max then some (x.val + y.val) else none := by
  have := U64.checked_add_bv_spec x y
  split at this <;> rename_i h <;> rw [h] <;> simp_all

theorem Option.map_val_some {α : Type} {β : Type} (f : α → β) {o : Option α} {a : α} (h : o = some a) :
    o.map f = some (f a) := by simp [h]

theorem spec_ok_exists {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ v, m = ok v ∧ p v := by
  cases m using Result.cases with
  | ret v => exact ⟨v, rfl, by simpa [WP.spec_ok] using h⟩
  | vis e k => simp [WP.spec_vis] at h
  | div => simp [WP.spec_div] at h

@[simp] theorem lift_eq {α : Type} (x : α) : lift x = ok x := rfl

theorem hcast_u32_i64_val (d : U32) : (UScalar.hcast .I64 d).val = d.val := by
  have := UScalar.hcast_inBounds_spec (tgt_ty := .I64) d (by scalar_tac)
  simpa [WP.spec_ok] using this

theorem hcast_u32_u64_val (d : U32) : (UScalar.cast .U64 d).val = d.val := by
  simp [UScalar.cast_val_eq]; scalar_tac

theorem digits_i64_ok (s : value.List Char) (neg : Bool) (acc : I64) :
    ∃ r, ext.digits_i64 s neg acc = ok r ∧ XL.digI64 neg acc.val (List.toList s) = r.map (·.val) := by
  induction s generalizing acc with
  | Nil => rw [ext.digits_i64.eq_def]; simp [XL.digI64]
  | Cons c rest ih =>
    rw [ext.digits_i64.eq_def]
    simp only [List.toList_cons, XL.digI64]
    obtain ⟨o, ho, hpo⟩ := spec_ok_exists (digit_val_spec c)
    rw [ho]; simp only [bind_ok]
    cases o with
    | none => simp_all
    | some d =>
      simp only at hpo
      obtain ⟨hd, hdv⟩ := hpo
      simp only [lift_eq, bind_ok]
      have hm := I64.checked_mul_val acc 10#i64
      cases hmul : I64.checked_mul acc 10#i64 with
      | none =>
        simp only [hmul, Option.map_none] at hm
        split at hm
        · simp at hm
        · simp_all
      | some a =>
        simp only [hmul, Option.map_some] at hm
        split at hm <;> simp only [Option.some.injEq, reduceCtorEq] at hm
        rename_i hin
        have hdv' : (UScalar.hcast .I64 d).val = (c.toNat - 48 : Nat) := by
          rw [hcast_u32_i64_val, hdv]
        cases neg with
        | true =>
          simp only [ite_true, bind_ok]
          have hs := I64.checked_sub_val a (UScalar.hcast .I64 d)
          cases hsub : I64.checked_sub a (UScalar.hcast .I64 d) with
          | none =>
            simp only [hsub, Option.map_none] at hs
            split at hs
            · simp at hs
            · simp_all
          | some a2 =>
            simp only [hsub, Option.map_some] at hs
            split at hs <;> simp only [Option.some.injEq, reduceCtorEq] at hs
            obtain ⟨r, hr, hrv⟩ := ih a2
            refine ⟨r, hr, ?_⟩
            have h10 : (10#i64 : I64).val = 10 := by decide
            rw [← hrv, hs, hm, hdv', h10]
            simp_all
        | false =>
          simp only [Bool.false_eq_true, ite_false, bind_ok]
          have hs := I64.checked_add_val a (UScalar.hcast .I64 d)
          cases hadd : I64.checked_add a (UScalar.hcast .I64 d) with
          | none =>
            simp only [hadd, Option.map_none] at hs
            split at hs
            · simp at hs
            · simp_all
          | some a2 =>
            simp only [hadd, Option.map_some] at hs
            split at hs <;> simp only [Option.some.injEq, reduceCtorEq] at hs
            obtain ⟨r, hr, hrv⟩ := ih a2
            refine ⟨r, hr, ?_⟩
            have h10 : (10#i64 : I64).val = 10 := by decide
            rw [← hrv, hs, hm, hdv', h10]
            simp_all

theorem spec_of_ok_exists {α : Type} {m : Result α} {p : α → Prop} (h : ∃ v, m = ok v ∧ p v) :
    m ⦃ x => p x ⦄ := by
  obtain ⟨v, rfl, hv⟩ := h; simpa [WP.spec_ok] using hv

@[step] theorem digits_i64_spec (s : value.List Char) (neg : Bool) (acc : I64) :
    ext.digits_i64 s neg acc ⦃ r => XL.digI64 neg acc.val (List.toList s) = r.map (·.val) ⦄ :=
  spec_of_ok_exists (digits_i64_ok s neg acc)

theorem digits_u64_ok (s : value.List Char) (acc : U64) :
    ∃ r, ext.digits_u64 s acc = ok r ∧ XL.digU64 acc.val (List.toList s) = r.map (·.val) := by
  induction s generalizing acc with
  | Nil => rw [ext.digits_u64.eq_def]; simp [XL.digU64]
  | Cons c rest ih =>
    rw [ext.digits_u64.eq_def]
    simp only [List.toList_cons, XL.digU64]
    obtain ⟨o, ho, hpo⟩ := spec_ok_exists (digit_val_spec c)
    rw [ho]; simp only [bind_ok]
    cases o with
    | none => simp_all
    | some d =>
      simp only at hpo
      obtain ⟨hd, hdv⟩ := hpo
      simp only [lift_eq, bind_ok]
      have h10 : (10#u64 : U64).val = 10 := by decide
      have hm := U64.checked_mul_val acc 10#u64
      cases hmul : U64.checked_mul acc 10#u64 with
      | none =>
        simp only [hmul, Option.map_none] at hm
        split at hm
        · simp at hm
        · simp_all
      | some a =>
        simp only [hmul, Option.map_some] at hm
        split at hm <;> simp only [Option.some.injEq, reduceCtorEq] at hm
        have hdv' : (UScalar.cast .U64 d).val = c.toNat - 48 := by
          rw [hcast_u32_u64_val, hdv]
        have hs := U64.checked_add_val a (UScalar.cast .U64 d)
        cases hadd : U64.checked_add a (UScalar.cast .U64 d) with
        | none =>
          simp only [hadd, Option.map_none] at hs
          split at hs
          · simp at hs
          · simp_all
        | some a2 =>
          simp only [hadd, Option.map_some] at hs
          split at hs <;> simp only [Option.some.injEq, reduceCtorEq] at hs
          obtain ⟨r, hr, hrv⟩ := ih a2
          refine ⟨r, by simp [hadd, hr], ?_⟩
          rw [← hrv, hs, hm, hdv', h10]
          simp_all

@[step] theorem digits_u64_spec (s : value.List Char) (acc : U64) :
    ext.digits_u64 s acc ⦃ r => XL.digU64 acc.val (List.toList s) = r.map (·.val) ⦄ :=
  spec_of_ok_exists (digits_u64_ok s acc)

@[step] theorem parse_i64_spec (s : value.List Char) :
    ext.parse_i64 s ⦃ r => XL.parseI64' (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.parse_i64
  cases s with
  | Nil => simp [XL.parseI64', WP.spec_ok]
  | Cons c rest =>
    step*
    all_goals (subst_vars; simp_all [XL.parseI64'])
    all_goals (cases rest <;> simp_all)

@[step] theorem parse_u64_spec (s : value.List Char) :
    ext.parse_u64 s ⦃ r => XL.parseU64' (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.parse_u64
  cases s with
  | Nil => simp [XL.parseU64', WP.spec_ok]
  | Cons c rest =>
    step*
    all_goals (subst_vars; simp_all [XL.parseU64'])
    all_goals (cases rest <;> simp_all)

@[step] theorem parse_u8_spec (s : value.List Char) :
    ext.parse_u8 s ⦃ r => XL.parseU8 (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.parse_u8
  step*
  all_goals (subst_vars; rw [XL.parseU8, o_post]; simp)
  all_goals (try simp [UScalar.cast_val_eq])
  all_goals scalar_tac

@[simp] theorem XL.inI64_val (x : I64) : XL.inI64 x.val = true := by
  simp only [XL.inI64, decide_eq_true_eq]; scalar_tac

@[step] theorem lift_checked_mul_spec (x y : I64) :
    lift (I64.checked_mul x y) ⦃ o => XL.chk (x.val * y.val) = o.map (·.val) ⦄ := by
  simp only [lift_eq, WP.spec_ok, XL.chk]; rw [I64.checked_mul_val]

@[step] theorem lift_checked_add_spec (x y : I64) :
    lift (I64.checked_add x y) ⦃ o => XL.chk (x.val + y.val) = o.map (·.val) ⦄ := by
  simp only [lift_eq, WP.spec_ok, XL.chk]; rw [I64.checked_add_val]

@[step] theorem lift_checked_sub_spec (x y : I64) :
    lift (I64.checked_sub x y) ⦃ o => XL.chk (x.val - y.val) = o.map (·.val) ⦄ := by
  simp only [lift_eq, WP.spec_ok, XL.chk]; rw [I64.checked_sub_val]

theorem checked_add_eq (x y : I64) : (I64.checked_add x y).map (·.val) = XL.chk (x.val + y.val) := by
  rw [I64.checked_add_val]; rfl

theorem checked_sub_eq (x y : I64) : (I64.checked_sub x y).map (·.val) = XL.chk (x.val - y.val) := by
  rw [I64.checked_sub_val]; rfl

end -- public section

end CedarRustModel
