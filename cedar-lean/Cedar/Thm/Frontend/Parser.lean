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

import Cedar.Thm.Frontend.Parser.Strings

/-! This file states and proves the main theorems about the Cedar parser. -/

namespace Cedar.Spec.Cst.Parser

/-- `Nat.toHexChars` is equivalent to `Nat.toDigits 16` for values up to 4095.
    This gives additional assurance that our custom implementation matches the stdlib. -/
theorem toHexChars_eq_toDigits :
    ∀ n : Fin 4096, Nat.toHexChars n.val = Nat.toDigits 16 n.val := by
  native_decide

/-- `Nat.toHexString` roundtrips through `String.asHexNat` for all values ≤ 0xFFFFFF. -/
theorem String.asHexNat_toHexString (n : Nat) (h : n ≤ 0xFFFFFF) :
    (Nat.toHexString n).asHexNat = .ok n := by
  simp only [Nat.toHexString]
  have hne : Nat.toHexChars n ≠ [] := by
    unfold Nat.toHexChars
    split
    · exact List.cons_ne_nil _ _
    · next h0 =>
      intro heq
      have hpos : n > 0 := by simp [BEq.beq] at h0; omega
      have hlen := go_nonempty n hpos
      rw [heq] at hlen; simp at hlen
  have hlen : (Nat.toHexChars n).length ≤ 6 := by
    unfold Nat.toHexChars
    split
    · simp
    · exact go_length_le n h
  rw [asHexNat_eq_hexFold _ hne hlen]
  match hn : n with
  | 0 => exact toHexChars_zero_roundtrip
  | n + 1 => exact toHexChars_pos_roundtrip (n + 1) (by omega)

end Cedar.Spec.Cst.Parser
