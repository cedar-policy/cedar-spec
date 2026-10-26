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

public import CedarRustModel.Ext.Bridge
public import Cedar.Thm.Ext.IPAddr
import all Cedar.Spec.Ext.IPAddr

/-! The IP-address parser of the model computes `XL.parseIP`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model
open Cedar.Spec.Ext

@[expose] public section

namespace XL

def v4Octet (l : _root_.List Char) : Option Nat :=
  if l ≠ [] ∧ allDigits l ∧ l.length ≤ 3 ∧ ¬(l.head? = some '0' ∧ l ≠ ['0'])
  then (digU64 0 l).bind (fun n => if n ≤ 255 then some n else none) else none

def v4Octets (g0 g1 g2 g3 : _root_.List Char) : Option (BitVec 32) :=
  match v4Octet g0, v4Octet g1, v4Octet g2, v4Octet g3 with
  | some a0, some a1, some a2, some a3 =>
    some (IPAddr.IPv4Addr.mk (BitVec.ofNat 8 a0) (BitVec.ofNat 8 a1) (BitVec.ofNat 8 a2) (BitVec.ofNat 8 a3))
  | _, _, _, _ => none

def parseV4 (l : _root_.List Char) : Option (BitVec 32) :=
  match splitAll '.' l with
  | [g0, g1, g2, g3] => v4Octets g0 g1 g2 g3
  | _ => none

theorem v4Octet_le {l : _root_.List Char} {n : Nat} (h : v4Octet l = some n) : n ≤ 255 := by
  unfold v4Octet at h
  split at h
  · cases hd : digU64 0 l with
    | none => simp [hd] at h
    | some m => simp only [hd, Option.bind_some] at h; split at h <;> simp_all
  · simp at h

def hexDig (acc : Nat) : _root_.List Char → Option Nat
  | [] => some acc
  | c :: l => if isHex c ∧ acc < 4096 then hexDig (acc * 16 + hexVal c) l else none

def v6Group (l : _root_.List Char) : Option Nat :=
  if l = [] then none else if l.length ≤ 4 then hexDig 0 l else none

def v6GroupsList : _root_.List (_root_.List Char) → Option (_root_.List Nat)
  | [] => some []
  | g :: gs => match v6Group g with
    | none => none
    | some n => (v6GroupsList gs).map (n :: ·)

def v6Groups (l : _root_.List Char) : Option (_root_.List Nat) :=
  if l = [] then some [] else v6GroupsList (splitAll ':' l)

def splitDC : _root_.List Char → Option (_root_.List Char × _root_.List Char)
  | [] => none
  | c :: rest =>
    if c = ':' ∧ rest.head? = some ':' then some ([], rest.tail)
    else (splitDC rest).map fun (a, b) => (c :: a, b)

def subLen (l : _root_.List Nat) (n : Nat) : Option Nat :=
  if l.length ≤ n then some (n - l.length) else none

def v6Hextets (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) : BitVec 128 :=
  IPAddr.IPv6Addr.mk (BitVec.ofNat 16 a0) (BitVec.ofNat 16 a1) (BitVec.ofNat 16 a2)
    (BitVec.ofNat 16 a3) (BitVec.ofNat 16 a4) (BitVec.ofNat 16 a5) (BitVec.ofNat 16 a6)
    (BitVec.ofNat 16 a7)

def v6OfGroups : _root_.List Nat → Option (BitVec 128)
  | [a0, a1, a2, a3, a4, a5, a6, a7] => some (v6Hextets a0 a1 a2 a3 a4 a5 a6 a7)
  | _ => none

def parseV6 (l : _root_.List Char) : Option (BitVec 128) :=
  match splitDC l with
  | none => (v6Groups l).bind v6OfGroups
  | some (a, b) =>
    match v6Groups a, v6Groups b with
    | some gl, some gr =>
      match subLen gl 8 with
      | none => none
      | some k => match subLen gr k with
        | none => none
        | some z => if z = 0 then none else v6OfGroups (gl ++ (_root_.List.replicate z 0 ++ gr))
    | _, _ => none

def parseAddr (l : _root_.List Char) : Option (BitVec 32 ⊕ BitVec 128) :=
  match parseV4 l with
  | some a => some (.inl a)
  | none => (parseV6 l).map .inr

def parsePrefix (l : _root_.List Char) (max maxLen : Nat) : Option Nat :=
  if utf8Len l ≤ maxLen then
    if allDigits l then
      if l.head? = some '0' then
        if l = ['0'] then
          match parseU8 l with
          | none => none
          | some n => if n > max then none else some n
        else none
      else
        match parseU8 l with
        | none => none
        | some n => if n > max then none else some n
    else none
  else none

def netOf (a : BitVec 32 ⊕ BitVec 128) (n : Nat) : IPAddr.IPNet :=
  match a with
  | .inl x => .V4 ⟨x, prefixOfNat IPAddr.V4_WIDTH n⟩
  | .inr x => .V6 ⟨x, prefixOfNat IPAddr.V6_WIDTH n⟩

def parseIP (l : _root_.List Char) : Option IPAddr.IPNet :=
  if ¬ utf8Len l ≤ 43 then none
  else if 2 ≤ l.count ':' ∧ 2 ≤ l.count '.' then none
  else match splitFirst '/' l with
    | some (a, p) => match parseAddr a with
      | some (.inl x) => (parsePrefix p 32 2).map (netOf (.inl x))
      | some (.inr x) => (parsePrefix p 128 3).map (netOf (.inr x))
      | none => none
    | none => match parseAddr l with
      | some (.inl x) => some (netOf (.inl x) 32)
      | some (.inr x) => some (netOf (.inr x) 128)
      | none => none

theorem hexVal_le (c : Char) (h : isHex c = true) : hexVal c ≤ 15 := by
  have e : '0'.toNat = 48 ∧ 'a'.toNat = 97 ∧ 'f'.toNat = 102 ∧ 'A'.toNat = 65 ∧ 'F'.toNat = 70 := by
    decide
  simp only [isHex, hexVal, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    isDigit_iff, char_le_iff, e.1, e.2.1, e.2.2.1, e.2.2.2.1, e.2.2.2.2] at h ⊢
  split_ifs <;> omega

theorem hexDig_cons (acc : Nat) (c : Char) (l : _root_.List Char) :
    hexDig acc (c :: l) = if isHex c ∧ acc < 4096 then hexDig (acc * 16 + hexVal c) l else none := by
  simp only [hexDig]

theorem hexDig_le {acc : Nat} {l : _root_.List Char} {n : Nat} (h : hexDig acc l = some n)
    (ha : acc ≤ 65535) : n ≤ 65535 := by
  induction l generalizing acc with
  | nil => simp [hexDig] at h; omega
  | cons c l ih =>
    simp only [hexDig] at h
    split at h
    · rename_i hc
      have : hexVal c ≤ 15 := hexVal_le c hc.1
      exact ih h (by omega)
    · simp at h

theorem v6Group_le {l : _root_.List Char} {n : Nat} (h : v6Group l = some n) : n ≤ 65535 := by
  unfold v6Group at h
  by_cases h1 : l = []
  · simp [h1] at h
  by_cases h2 : l.length ≤ 4
  · simp only [h1, h2, if_false, if_true] at h; exact hexDig_le h (by omega)
  · simp [h1, h2] at h

theorem v6GroupsList_le {gs : _root_.List (_root_.List Char)} {ns : _root_.List Nat}
    (h : v6GroupsList gs = some ns) : ∀ n ∈ ns, n ≤ 65535 := by
  induction gs generalizing ns with
  | nil =>
    simp only [v6GroupsList, Option.some.injEq] at h
    subst h; simp
  | cons g gs ih =>
    simp only [v6GroupsList] at h
    split at h
    · simp at h
    · rename_i n hn
      cases hr : v6GroupsList gs with
      | none => simp [hr] at h
      | some ms =>
        simp only [hr, Option.map_some, Option.some.injEq] at h
        subst h
        intro m hm
        simp only [_root_.List.mem_cons] at hm
        rcases hm with rfl | hm
        · exact v6Group_le hn
        · exact ih hr m hm

theorem v6Groups_le {l : _root_.List Char} {ns : _root_.List Nat} (h : v6Groups l = some ns) :
    ∀ n ∈ ns, n ≤ 65535 := by
  unfold v6Groups at h
  by_cases h1 : l = []
  · simp only [h1, if_true, Option.some.injEq] at h; simp [← h]
  · simp only [h1, if_false] at h; exact v6GroupsList_le h

end XL

end

public section

@[step] theorem parse_v4_octet_spec (s : value.List Char) :
    ext.parse_v4_octet s ⦃ r => XL.v4Octet (List.toList s) = r.map (·.val) ⦄ := by
  have h0 : (0 : Nat) ≤ U64.max := by scalar_tac
  unfold ext.parse_v4_octet
  step*
  all_goals (subst_vars; simp_all [XL.v4Octet, UScalar.cast_val_eq])
  all_goals scalar_tac

theorem ofNat_val_u32 (x : U32) : BitVec.ofNat 32 x.val = x.bv := by
  apply BitVec.eq_of_toNat_eq; simp

theorem hzl {w : Nat} {b : BitVec w} {k : Nat} (hb : b.toNat < 2 ^ k) {j : Nat} (hk : k ≤ j) :
    b.getLsbD j = false := by
  rw [BitVec.getLsbD, Nat.testBit_lt_two_pow]
  exact lt_of_lt_of_le hb (Nat.pow_le_pow_right (by omega) hk)

theorem v4_combine (b0 b1 b2 b3 : BitVec 32) (g0 : b0.toNat < 2 ^ 8) (g1 : b1.toNat < 2 ^ 8)
    (g2 : b2.toNat < 2 ^ 8) (g3 : b3.toNat < 2 ^ 8) :
    (b0 <<< 24 ||| b1 <<< 16 ||| b2 <<< 8 ||| b3) =
      b0.setWidth 8 ++ b1.setWidth 8 ++ b2.setWidth 8 ++ b3.setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    Nat.sub_sub]
  have z0 := fun j (h : 8 ≤ j) => hzl g0 (j := j) h
  have z1 := fun j (h : 8 ≤ j) => hzl g1 (j := j) h
  have z2 := fun j (h : 8 ≤ j) => hzl g2 (j := j) h
  have z3 := fun j (h : 8 ≤ j) => hzl g3 (j := j) h
  rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32)) with h | h | h | h
  · simp [hi, h, show i < 16 by omega, show i < 24 by omega]
  · simp [hi, show ¬ i < 8 by omega, show i - 8 < 8 by omega, show i < 16 by omega, show i < 24 by omega,
      (show b3[i] = false by rw [← BitVec.getLsbD_eq_getElem]; exact z3 i (by omega))]
  · simp [hi, show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show i - 16 < 8 by omega,
      show ¬ i < 16 by omega, show i < 24 by omega, (show b3[i] = false by rw [← BitVec.getLsbD_eq_getElem]; exact z3 i (by omega)), z2 (i - 8) (by omega)]
  · simp [hi, show ¬ i < 8 by omega, show ¬ i - 8 < 8 by omega, show ¬ i - 16 < 8 by omega,
      show i - 24 < 8 by omega, show ¬ i < 16 by omega, show ¬ i < 24 by omega, (show b3[i] = false by rw [← BitVec.getLsbD_eq_getElem]; exact z3 i (by omega)),
      z2 (i - 8) (by omega), z1 (i - 16) (by omega)]

theorem v4_combine_bv (b0 b1 b2 b3 : BitVec 32) (g0 : b0 ≤ 255#32) (g1 : b1 ≤ 255#32)
    (g2 : b2 ≤ 255#32) (g3 : b3 ≤ 255#32) :
    (b0 <<< 24 ||| b1 <<< 16 ||| b2 <<< 8 ||| b3) =
      b0.setWidth 8 ++ b1.setWidth 8 ++ b2.setWidth 8 ++ b3.setWidth 8 := by
  simp only [BitVec.le_def] at g0 g1 g2 g3
  exact v4_combine b0 b1 b2 b3 (by simp at g0; omega) (by simp at g1; omega) (by simp at g2; omega)
    (by simp at g3; omega)

theorem le255_bv (a : U32) (h : a.val ≤ 255) : a.bv ≤ 255#32 := by
  rw [BitVec.le_def, UScalar.bv_toNat]; simpa using h

theorem ofNat8_val (a : U32) : BitVec.ofNat 8 a.val = a.bv.setWidth 8 := by
  rw [← UScalar.bv_toNat, BitVec.ofNat_toNat]

@[step] theorem v4_of_octets_spec (a0 a1 a2 a3 : U32) (h0 : a0.val ≤ 255) (h1 : a1.val ≤ 255)
    (h2 : a2.val ≤ 255) (h3 : a3.val ≤ 255) :
    ext.v4_of_octets a0 a1 a2 a3 ⦃ x => BitVec.ofNat 32 x.val =
      IPAddr.IPv4Addr.mk (BitVec.ofNat 8 a0.val) (BitVec.ofNat 8 a1.val) (BitVec.ofNat 8 a2.val)
        (BitVec.ofNat 8 a3.val) ⦄ := by
  unfold ext.v4_of_octets
  step*
  rw [ofNat_val_u32, IPAddr.IPv4Addr.mk, ofNat8_val, ofNat8_val, ofNat8_val, ofNat8_val]
  simp only [UScalar.bv_or, i4_post1, i2_post1, i_post1, i1_post1, i3_post1]
  exact v4_combine_bv _ _ _ _ (le255_bv a0 h0) (le255_bv a1 h1) (le255_bv a2 h2) (le255_bv a3 h3)

@[step] theorem parse_v4_octets_spec (g0 g1 g2 g3 : value.List Char) :
    ext.parse_v4_octets g0 g1 g2 g3 ⦃ r => XL.v4Octets (List.toList g0) (List.toList g1)
      (List.toList g2) (List.toList g3) = r.map (fun x => BitVec.ofNat 32 x.val) ⦄ := by
  unfold ext.parse_v4_octets
  step*
  all_goals (subst_vars; first
    | exact XL.v4Octet_le (o_post.trans rfl) | exact XL.v4Octet_le (o1_post.trans rfl)
    | exact XL.v4Octet_le (o2_post.trans rfl) | exact XL.v4Octet_le (o3_post.trans rfl)
    | simp_all [XL.v4Octets])

@[step] theorem parse_v4_spec (s : value.List Char) :
    ext.parse_v4 s ⦃ r => XL.parseV4 (List.toList s) = r.map (fun x => BitVec.ofNat 32 x.val) ⦄ := by
  unfold ext.parse_v4
  step*
  all_goals (subst_vars; rw [XL.parseV4, parts_post]
             simp only [List.toList_cons, List.toList_nil, _root_.List.map_cons, _root_.List.map_nil])
  all_goals (try exact r_post)
  all_goals rfl

@[step] theorem hex_digits_spec (s : value.List Char) (acc : U32) :
    ext.hex_digits s acc ⦃ r => XL.hexDig acc.val (List.toList s) = r.map (·.val) ⦄ := by
  induction s generalizing acc with
  | Nil => rw [ext.hex_digits.eq_def]; simp [XL.hexDig, WP.spec_ok]
  | Cons c rest ih =>
    rw [ext.hex_digits.eq_def]
    step*
    all_goals (subst_vars; simp only [List.toList_cons, XL.hexDig_cons] at *)
    · simp [o_post]
    · have := XL.hexVal_le c o_post.1; scalar_tac
    · have h1 : (↑acc : Nat) * 16 + XL.hexVal c = ↑i1 := by scalar_tac
      rw [if_pos ⟨o_post.1, by scalar_tac⟩, h1]; exact r_post
    · rw [if_neg]; · rfl
      intro ⟨_, h⟩; scalar_tac

@[step] theorem parse_v6_group_spec (s : value.List Char) :
    ext.parse_v6_group s ⦃ r => XL.v6Group (List.toList s) = r.map (·.val) ⦄ := by
  unfold ext.parse_v6_group
  step*
  all_goals (subst_vars; simp_all [XL.v6Group])

@[step] theorem parse_v6_groups_list_spec (gs : value.List (value.List Char)) :
    ext.parse_v6_groups_list gs ⦃ r =>
      XL.v6GroupsList ((List.toList gs).map List.toList) = r.map (fun l => (List.toList l).map (·.val)) ⦄ := by
  induction gs with
  | Nil => rw [ext.parse_v6_groups_list.eq_def]; simp [XL.v6GroupsList, WP.spec_ok]
  | Cons g rest ih =>
    rw [ext.parse_v6_groups_list.eq_def]
    step*
    all_goals (subst_vars; simp_all [XL.v6GroupsList])

@[step] theorem parse_v6_groups_spec (s : value.List Char) :
    ext.parse_v6_groups s ⦃ r => XL.v6Groups (List.toList s) = r.map (fun l => (List.toList l).map (·.val)) ⦄ := by
  unfold ext.parse_v6_groups
  step*
  all_goals (subst_vars; simp_all [XL.v6Groups])

@[step] theorem split_double_colon_spec (s : value.List Char) :
    ext.split_double_colon s ⦃ r =>
      XL.splitDC (List.toList s) = r.map (fun p => (List.toList p.1, List.toList p.2)) ⦄ := by
  induction s with
  | Nil => rw [ext.split_double_colon.eq_def]; simp [XL.splitDC, WP.spec_ok]
  | Cons c rest ih =>
    rw [ext.split_double_colon.eq_def]
    step*
    all_goals (try obtain ⟨_, _⟩ := p)
    all_goals (subst_vars; simp_all [XL.splitDC])
    all_goals (cases rest <;> simp_all)

@[step] theorem sub_len_spec (l : value.List U32) (n : U32) :
    ext.sub_len l n ⦃ r => XL.subLen ((List.toList l).map (·.val)) n.val = r.map (·.val) ⦄ := by
  induction l generalizing n with
  | Nil => rw [ext.sub_len.eq_def]; simp [XL.subLen, WP.spec_ok]
  | Cons x rest ih =>
    rw [ext.sub_len.eq_def]
    step*
    all_goals (subst_vars; simp only [XL.subLen, List.toList_cons, _root_.List.map_cons,
      _root_.List.length_cons, _root_.List.length_map] at *)
    all_goals (split_ifs at * <;> simp_all)
    all_goals (try (obtain ⟨a, rfl, ha⟩ := r_post; exact ⟨a, rfl, by omega⟩))
    all_goals scalar_tac

@[step] theorem zeros_then_spec (n : U32) (tail : value.List U32) :
    ext.zeros_then n tail ⦃ r => (List.toList r).map (·.val) =
      _root_.List.replicate n.val 0 ++ (List.toList tail).map (·.val) ⦄ := by
  obtain ⟨k, hk⟩ : ∃ k, n.val = k := ⟨_, rfl⟩
  induction k generalizing n with
  | zero =>
    rw [ext.zeros_then.eq_def]
    have : n = 0#u32 := by scalar_tac
    simp [this, WP.spec_ok]
  | succ k ih =>
    rw [ext.zeros_then.eq_def]
    have : n ≠ 0#u32 := by scalar_tac
    simp only [this, if_false]
    step* by scalar_tac
    all_goals (subst_vars; simp_all [_root_.List.replicate_succ])

@[step] theorem append_u32_spec (l tail : value.List U32) :
    ext.append_u32 l tail ⦃ r => List.toList r = List.toList l ++ List.toList tail ⦄ := by
  induction l with
  | Nil => rw [ext.append_u32.eq_def]; simp [WP.spec_ok]
  | Cons x rest ih =>
    rw [ext.append_u32.eq_def]
    step*
    all_goals (subst_vars; simp_all)

theorem ofNat_val_u128 (x : U128) : BitVec.ofNat 128 x.val = x.bv := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat16_val (a : U32) : BitVec.ofNat 16 a.val = a.bv.setWidth 16 := by
  rw [← UScalar.bv_toNat, BitVec.ofNat_toNat]

theorem le65535_bv (a : U32) (h : a.val ≤ 65535) : a.bv ≤ 65535#32 := by
  rw [BitVec.le_def, UScalar.bv_toNat]; simpa using h

theorem v6_combine (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 32) (g0 : b0.toNat < 2 ^ 16) (g1 : b1.toNat < 2 ^ 16)
    (g2 : b2.toNat < 2 ^ 16) (g3 : b3.toNat < 2 ^ 16) (g4 : b4.toNat < 2 ^ 16) (g5 : b5.toNat < 2 ^ 16)
    (g6 : b6.toNat < 2 ^ 16) (g7 : b7.toNat < 2 ^ 16) :
    (b0.setWidth 128 <<< 112 ||| b1.setWidth 128 <<< 96 ||| b2.setWidth 128 <<< 80 |||
      b3.setWidth 128 <<< 64 ||| b4.setWidth 128 <<< 48 ||| b5.setWidth 128 <<< 32 |||
      b6.setWidth 128 <<< 16 ||| b7.setWidth 128) =
      b0.setWidth 16 ++ b1.setWidth 16 ++ b2.setWidth 16 ++ b3.setWidth 16 ++ b4.setWidth 16 ++
        b5.setWidth 16 ++ b6.setWidth 16 ++ b7.setWidth 16 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
    Nat.sub_sub]
  have z0 := fun j (h : 16 ≤ j) => hzl g0 (j := j) h
  have z1 := fun j (h : 16 ≤ j) => hzl g1 (j := j) h
  have z2 := fun j (h : 16 ≤ j) => hzl g2 (j := j) h
  have z3 := fun j (h : 16 ≤ j) => hzl g3 (j := j) h
  have z4 := fun j (h : 16 ≤ j) => hzl g4 (j := j) h
  have z5 := fun j (h : 16 ≤ j) => hzl g5 (j := j) h
  have z6 := fun j (h : 16 ≤ j) => hzl g6 (j := j) h
  have z7 := fun j (h : 16 ≤ j) => hzl g7 (j := j) h
  rcases (by omega : (0 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 80) ∨ (80 ≤ i ∧ i < 96) ∨ (96 ≤ i ∧ i < 112) ∨ (112 ≤ i ∧ i < 128)) with h | h | h | h | h | h | h | h
  · simp [hi, show i < 16 by omega, show i < 32 by omega, show i < 48 by omega, show i < 64 by omega, show i < 80 by omega, show i < 96 by omega, show i < 112 by omega]
  · simp [hi, show ¬ i < 16 by omega, show i < 32 by omega, show i < 48 by omega, show i < 64 by omega, show i < 80 by omega, show i < 96 by omega, show i < 112 by omega, show i - 16 < 16 by omega, show ¬ i < 16 by omega, show i - 16 < 128 by omega, z7 i (by omega), (show b7[i]'(by omega) = false by rw [← BitVec.getLsbD_eq_getElem]; exact z7 i (by omega))]
  · simp [hi, show ¬ i < 16 by omega, show ¬ i < 32 by omega, show i < 48 by omega, show i < 64 by omega, show i < 80 by omega, show i < 96 by omega, show i < 112 by omega, show ¬ i - 16 < 16 by omega, show i - 32 < 16 by omega, show ¬ i < 16 by omega, show i - 32 < 128 by omega, z6 (i - 16) (by omega), z7 i (by omega)]
  · simp [hi, show ¬ i < 16 by omega, show ¬ i < 32 by omega, show ¬ i < 48 by omega, show i < 64 by omega, show i < 80 by omega, show i < 96 by omega, show i < 112 by omega, show ¬ i - 16 < 16 by omega, show ¬ i - 32 < 16 by omega, show i - 48 < 16 by omega, show ¬ i < 16 by omega, show i - 48 < 128 by omega, z5 (i - 32) (by omega), z6 (i - 16) (by omega), z7 i (by omega)]
  · simp [hi, show ¬ i < 16 by omega, show ¬ i < 32 by omega, show ¬ i < 48 by omega, show ¬ i < 64 by omega, show i < 80 by omega, show i < 96 by omega, show i < 112 by omega, show ¬ i - 16 < 16 by omega, show ¬ i - 32 < 16 by omega, show ¬ i - 48 < 16 by omega, show i - 64 < 16 by omega, show ¬ i < 16 by omega, show i - 64 < 128 by omega, z4 (i - 48) (by omega), z5 (i - 32) (by omega), z6 (i - 16) (by omega), z7 i (by omega)]
  · simp [hi, show ¬ i < 16 by omega, show ¬ i < 32 by omega, show ¬ i < 48 by omega, show ¬ i < 64 by omega, show ¬ i < 80 by omega, show i < 96 by omega, show i < 112 by omega, show ¬ i - 16 < 16 by omega, show ¬ i - 32 < 16 by omega, show ¬ i - 48 < 16 by omega, show ¬ i - 64 < 16 by omega, show i - 80 < 16 by omega, show ¬ i < 16 by omega, show i - 80 < 128 by omega, z3 (i - 64) (by omega), z4 (i - 48) (by omega), z5 (i - 32) (by omega), z6 (i - 16) (by omega), z7 i (by omega)]
  · simp [hi, show ¬ i < 16 by omega, show ¬ i < 32 by omega, show ¬ i < 48 by omega, show ¬ i < 64 by omega, show ¬ i < 80 by omega, show ¬ i < 96 by omega, show i < 112 by omega, show ¬ i - 16 < 16 by omega, show ¬ i - 32 < 16 by omega, show ¬ i - 48 < 16 by omega, show ¬ i - 64 < 16 by omega, show ¬ i - 80 < 16 by omega, show i - 96 < 16 by omega, show ¬ i < 16 by omega, show i - 96 < 128 by omega, z2 (i - 80) (by omega), z3 (i - 64) (by omega), z4 (i - 48) (by omega), z5 (i - 32) (by omega), z6 (i - 16) (by omega), z7 i (by omega)]
  · simp [hi, show ¬ i < 16 by omega, show ¬ i < 32 by omega, show ¬ i < 48 by omega, show ¬ i < 64 by omega, show ¬ i < 80 by omega, show ¬ i < 96 by omega, show ¬ i < 112 by omega, show ¬ i - 16 < 16 by omega, show ¬ i - 32 < 16 by omega, show ¬ i - 48 < 16 by omega, show ¬ i - 64 < 16 by omega, show ¬ i - 80 < 16 by omega, show ¬ i - 96 < 16 by omega, show i - 112 < 16 by omega, show ¬ i < 16 by omega, show i - 112 < 128 by omega, z1 (i - 96) (by omega), z2 (i - 80) (by omega), z3 (i - 64) (by omega), z4 (i - 48) (by omega), z5 (i - 32) (by omega), z6 (i - 16) (by omega), z7 i (by omega)]

theorem v6_combine_bv (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 32) (g0 : b0 ≤ 65535#32) (g1 : b1 ≤ 65535#32)
    (g2 : b2 ≤ 65535#32) (g3 : b3 ≤ 65535#32) (g4 : b4 ≤ 65535#32) (g5 : b5 ≤ 65535#32)
    (g6 : b6 ≤ 65535#32) (g7 : b7 ≤ 65535#32) :
    (b0.setWidth 128 <<< 112 ||| b1.setWidth 128 <<< 96 ||| b2.setWidth 128 <<< 80 |||
      b3.setWidth 128 <<< 64 ||| b4.setWidth 128 <<< 48 ||| b5.setWidth 128 <<< 32 |||
      b6.setWidth 128 <<< 16 ||| b7.setWidth 128) =
      b0.setWidth 16 ++ b1.setWidth 16 ++ b2.setWidth 16 ++ b3.setWidth 16 ++ b4.setWidth 16 ++
        b5.setWidth 16 ++ b6.setWidth 16 ++ b7.setWidth 16 := by
  simp only [BitVec.le_def] at g0 g1 g2 g3 g4 g5 g6 g7
  exact v6_combine b0 b1 b2 b3 b4 b5 b6 b7 (by simp at g0; omega) (by simp at g1; omega)
    (by simp at g2; omega) (by simp at g3; omega) (by simp at g4; omega) (by simp at g5; omega)
    (by simp at g6; omega) (by simp at g7; omega)

@[step] theorem v6_of_hextets_spec (a0 a1 a2 a3 a4 a5 a6 a7 : U32) (h0 : a0.val ≤ 65535)
    (h1 : a1.val ≤ 65535) (h2 : a2.val ≤ 65535) (h3 : a3.val ≤ 65535) (h4 : a4.val ≤ 65535)
    (h5 : a5.val ≤ 65535) (h6 : a6.val ≤ 65535) (h7 : a7.val ≤ 65535) :
    ext.v6_of_hextets a0 a1 a2 a3 a4 a5 a6 a7 ⦃ x => BitVec.ofNat 128 x.val =
      XL.v6Hextets a0.val a1.val a2.val a3.val a4.val a5.val a6.val a7.val ⦄ := by
  unfold ext.v6_of_hextets
  step*
  rw [ofNat_val_u128, XL.v6Hextets, IPAddr.IPv6Addr.mk]
  simp only [ofNat16_val, UScalar.bv_or, UScalar.cast_bv_eq, *]
  exact v6_combine_bv _ _ _ _ _ _ _ _ (le65535_bv a0 h0) (le65535_bv a1 h1) (le65535_bv a2 h2)
    (le65535_bv a3 h3) (le65535_bv a4 h4) (le65535_bv a5 h5) (le65535_bv a6 h6) (le65535_bv a7 h7)

@[step] theorem v6_of_groups_spec (gs : value.List U32) (h : ∀ x ∈ List.toList gs, x.val ≤ 65535) :
    ext.v6_of_groups gs ⦃ r =>
      XL.v6OfGroups ((List.toList gs).map (·.val)) = r.map (fun x => BitVec.ofNat 128 x.val) ⦄ := by
  unfold ext.v6_of_groups
  rcases gs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, r⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.toList_cons, List.toList_nil, _root_.List.mem_cons, forall_eq_or_imp] at h <;>
    try (simp [XL.v6OfGroups, WP.spec_ok]; done)
  step* by simp_all
  simp_all [XL.v6OfGroups]

theorem map_val_le {l : value.List U32} {ns : _root_.List Nat} (h : ns = (List.toList l).map (·.val))
    (hb : ∀ n ∈ ns, n ≤ 65535) : ∀ x ∈ List.toList l, x.val ≤ 65535 := by
  intro x hx; exact hb _ (h ▸ _root_.List.mem_map_of_mem hx)

@[step] theorem parse_v6_spec (s : value.List Char) :
    ext.parse_v6 s ⦃ r => XL.parseV6 (List.toList s) = r.map (fun x => BitVec.ofNat 128 x.val) ⦄ := by
  unfold ext.parse_v6
  step*
  · subst_vars; simp_all [XL.parseV6]
  · subst_vars; exact map_val_le rfl (XL.v6Groups_le (o1_post.trans rfl))
  · subst_vars; simp_all [XL.parseV6]
  · obtain ⟨l, r⟩ := p
    step*
    all_goals subst_vars
    case h =>
      intro x hx
      rw [l2_post, _root_.List.mem_append] at hx
      rcases hx with hx | hx
      · exact map_val_le rfl (XL.v6Groups_le o1_post) x hx
      · have hm : x.val ∈ (List.toList l1).map (·.val) := _root_.List.mem_map_of_mem hx
        rw [l1_post, _root_.List.mem_append, _root_.List.mem_replicate] at hm
        rcases hm with ⟨_, hm⟩ | hm
        · omega
        · obtain ⟨y, hy, hyx⟩ := _root_.List.mem_map.1 hm
          rw [← hyx]; exact map_val_le rfl (XL.v6Groups_le o2_post) y hy
    all_goals (first
      | (intro x hx
         rw [l2_post, _root_.List.mem_append] at hx
         rcases hx with hx | hx
         · exact map_val_le rfl (XL.v6Groups_le (o1_post.trans rfl)) x hx
         · have hm : x.val ∈ (List.toList l1).map (·.val) := _root_.List.mem_map_of_mem hx
           rw [l1_post, _root_.List.mem_append, _root_.List.mem_replicate] at hm
           rcases hm with ⟨_, hm⟩ | hm
           · omega
           · obtain ⟨y, hy, rfl⟩ := _root_.List.mem_map.1 hm
             exact map_val_le rfl (XL.v6Groups_le (o2_post.trans rfl)) y hy)
      | (rw [← r_post, l2_post, _root_.List.map_append, l1_post]
         simp only [XL.parseV6, o_post, o1_post, o2_post, Option.map_some]
         simp_all)
      | (simp only [XL.parseV6, o_post, o1_post, o2_post, Option.map_some, Option.map_none]
         try simp_all)
      | simp_all [XL.parseV6])

def addrToSpec : ext.IPAddr → BitVec 32 ⊕ BitVec 128
  | .V4 x => .inl (BitVec.ofNat 32 x.val)
  | .V6 x => .inr (BitVec.ofNat 128 x.val)

@[step] theorem parse_ip_addr_spec (s : value.List Char) :
    ext.parse_ip_addr s ⦃ r => XL.parseAddr (List.toList s) = r.map addrToSpec ⦄ := by
  unfold ext.parse_ip_addr
  step*
  all_goals (subst_vars; simp_all [XL.parseAddr, addrToSpec])

@[step] theorem parse_prefix_spec (s : value.List Char) (max : U8) (maxLen : U32) :
    ext.parse_prefix s max maxLen ⦃ r => XL.parsePrefix (List.toList s) max.val maxLen.val = r.map (·.val) ⦄ := by
  unfold ext.parse_prefix
  step*
  all_goals (subst_vars; simp only [XL.parsePrefix])
  all_goals (split_ifs <;> simp_all)
  all_goals scalar_tac

@[step] theorem parse_ip_spec (s : value.List Char) :
    ext.parse_ip s ⦃ r => XL.parseIP (List.toList s) = r.map IPNet.toSpec ⦄ := by
  unfold ext.parse_ip
  step*
  all_goals (try obtain ⟨_, _⟩ := p)
  all_goals (try step*)
  all_goals (subst_vars; simp only [XL.parseIP])
  all_goals (simp_all [XL.netOf, IPNet.toSpec, addrToSpec])

end

end CedarRustModel