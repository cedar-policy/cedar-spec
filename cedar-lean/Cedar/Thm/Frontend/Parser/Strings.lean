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

import Cedar.Frontend.Parser

/-! This file contains lemmas for proving roundtrip properties of hex string conversion. -/

namespace Cedar.Spec.Cst.Parser

instance : DecidableEq (Except String Nat) := fun a b =>
  match a, b with
  | .ok n, .ok m => if h : n = m then isTrue (by rw [h]) else isFalse (by intro h'; injection h'; contradiction)
  | .error s, .error t => if h : s = t then isTrue (by rw [h]) else isFalse (by intro h'; injection h'; contradiction)
  | .ok _, .error _ => isFalse (by intro h; injection h)
  | .error _, .ok _ => isFalse (by intro h; injection h)

/-- `Nat.digitChar n` for `n < 16` roundtrips through `Char.asHexNat`. -/
theorem Char.asHexNat_digitChar (n : Nat) (h : n < 16) :
    Char.asHexNat (Nat.digitChar n) = .ok n := by
  match n, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ |
    8, _ | 9, _ | 10, _ | 11, _ | 12, _ | 13, _ | 14, _ | 15, _ =>
    simp [Char.asHexNat, Nat.digitChar]
  | n + 16, h => omega

/-- The fold that `String.asHexNat` performs, extracted for reasoning. -/
def hexFold (cs : List Char) (init : Except String Nat) : Except String Nat :=
  cs.foldl (fun acc c => do let v ← acc; let d ← c.asHexNat; .ok (v * 16 + d)) init

theorem hexFold_nil (init : Except String Nat) :
    hexFold [] init = init := rfl

theorem hexFold_cons (c : Char) (cs : List Char) (init : Except String Nat) :
    hexFold (c :: cs) init = hexFold cs (do let v ← init; let d ← c.asHexNat; .ok (v * 16 + d)) := by
  simp [hexFold, List.foldl]

theorem hexFold_ok_digit (cs : List Char) (v d : Nat) (hd : d < 16) :
    hexFold (Nat.digitChar d :: cs) (.ok v) = hexFold cs (.ok (v * 16 + d)) := by
  rw [hexFold_cons]
  simp [bind, Except.bind, Char.asHexNat_digitChar d hd]

/-- The generalized invariant: `hexFold (go n acc) (.ok 0) = hexFold acc (.ok n)` -/
theorem go_hexFold (n : Nat) (acc : List Char) :
    hexFold (Nat.toHexChars.go n acc) (.ok 0) = hexFold acc (.ok n) := by
  match n with
  | 0 => simp [Nat.toHexChars.go]
  | n + 1 =>
    unfold Nat.toHexChars.go
    simp only []
    have hmod : (n + 1) % 16 < 16 := Nat.mod_lt _ (by omega)
    rw [go_hexFold ((n + 1) / 16) (Nat.digitChar ((n + 1) % 16) :: acc)]
    rw [hexFold_ok_digit _ _ _ hmod]
    have heq : (n + 1) / 16 * 16 + (n + 1) % 16 = n + 1 := by
      have := Nat.div_add_mod (n + 1) 16; omega
    rw [heq]
termination_by n

/-- `toHexChars` for `n > 0` satisfies the roundtrip via hexFold. -/
theorem toHexChars_pos_roundtrip (n : Nat) (hn : n > 0) :
    hexFold (Nat.toHexChars n) (.ok 0) = .ok n := by
  simp only [Nat.toHexChars]
  have hne : (n == 0) = false := by simp [BEq.beq]; omega
  rw [if_neg (by simp [hne])]
  rw [go_hexFold]
  simp [hexFold]

/-- `toHexChars 0` roundtrips. -/
theorem toHexChars_zero_roundtrip :
    hexFold (Nat.toHexChars 0) (.ok 0) = .ok 0 := by
  simp [Nat.toHexChars, hexFold, List.foldl, Char.asHexNat, bind, Except.bind]

/-- Relate `String.asHexNat` to `hexFold`. -/
theorem asHexNat_eq_hexFold (cs : List Char) (hne : cs ≠ []) (hlen : cs.length ≤ 6) :
    (String.ofList cs).asHexNat = hexFold cs (.ok 0) := by
  unfold String.asHexNat hexFold
  have h1 : (String.ofList cs).isEmpty = false := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons c cs =>
      have hne' : String.ofList (c :: cs) ≠ "" := by
        intro h
        have := String.toList_ofList (l := c :: cs)
        rw [h] at this; simp at this
      exact Bool.eq_false_iff.mpr (mt String.isEmpty_iff.mp hne')
  rw [if_neg (by rw [h1]; exact Bool.false_ne_true)]
  rw [if_neg (by rw [String.length_ofList]; omega)]
  rw [String.toList_ofList]

/-- Length of `toHexChars.go` output. -/
theorem go_length (n : Nat) (acc : List Char) :
    (Nat.toHexChars.go n acc).length = (Nat.toHexChars.go n []).length + acc.length := by
  match n with
  | 0 => simp [Nat.toHexChars.go]
  | n + 1 =>
    unfold Nat.toHexChars.go
    simp only []
    rw [go_length ((n+1)/16) (Nat.digitChar ((n+1) % 16) :: acc)]
    rw [go_length ((n+1)/16) [Nat.digitChar ((n+1) % 16)]]
    simp [List.length]
    omega
termination_by n

theorem go_nonempty (n : Nat) (hn : n > 0) :
    (Nat.toHexChars.go n []).length ≥ 1 := by
  match n with
  | n + 1 =>
    unfold Nat.toHexChars.go
    simp only []
    rw [go_length]
    simp [List.length]

theorem go_length_le (n : Nat) (hn : n ≤ 0xFFFFFF) :
    (Nat.toHexChars.go n []).length ≤ 6 := by
  suffices ∀ (k : Nat) (m : Nat), m < 16^k → (Nat.toHexChars.go m []).length ≤ k from
    this 6 n (by omega)
  intro k
  induction k with
  | zero => intro m hm; simp at hm; subst hm; simp [Nat.toHexChars.go]
  | succ k ih =>
    intro m hm
    match m with
    | 0 => simp [Nat.toHexChars.go]
    | m + 1 =>
      unfold Nat.toHexChars.go
      simp only []
      rw [go_length]
      simp [List.length]
      have hdiv : (m + 1) / 16 < 16 ^ k := by
        have : (m + 1) / 16 < (16 ^ (k + 1)) / 16 := Nat.div_lt_div_of_lt_of_dvd (by omega) hm
        simp [Nat.pow_succ] at this
        exact this
      exact ih _ hdiv

end Cedar.Spec.Cst.Parser
