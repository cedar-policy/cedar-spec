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

/-! This file states and proves the main theorems about the Cedar parser's pure functions. -/

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

/-- `classifyIdent` is a left inverse of `Ident.toString`. -/
theorem classifyIdent_roundtrip (i : Ident) :
    classifyIdent i.toString = i := by
  cases i with
  | idIdent s h => simp only [Ident.toString, classifyIdent, dif_neg h]
  | _ => rfl

/-- `Char.asHexNat` is injective on lowercase hex chars:
    if two chars in '0'..'9' or 'a'..'f' map to the same value, they are equal. -/
theorem Char.asHexNat_injective_lower (c₁ c₂ : Char) (n : Nat)
    (h₁ : Char.asHexNat c₁ = .ok n)
    (h₂ : Char.asHexNat c₂ = .ok n)
    (hlc₁ : isLowerHex c₁) (hlc₂ : isLowerHex c₂) :
    c₁ = c₂ := by
  unfold Char.asHexNat at h₁ h₂
  simp only [Bool.and_eq_true, decide_eq_true_eq, Char.le_def, UInt32.le_iff_toNat_le] at h₁ h₂
  unfold isLowerHex at hlc₁ hlc₂
  have heq : c₁.toNat = c₂.toNat := by
    rcases hlc₁ with ⟨lo₁, hi₁⟩ | ⟨lo₁, hi₁⟩ <;> rcases hlc₂ with ⟨lo₂, hi₂⟩ | ⟨lo₂, hi₂⟩ <;>
      (split at h₁ <;> split at h₂ <;> simp_all <;> omega)
  exact Char.eq_of_toNat_eq heq

end Cedar.Spec.Cst.Parser
