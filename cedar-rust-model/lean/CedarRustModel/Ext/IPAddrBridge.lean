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

public import CedarRustModel.Ext.IPAddr
public import Cedar.Thm.Ext.IPAddr
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Spec.Ext.Util
import all Cedar.Thm.Data.String
import all Cedar.Thm.Ext.IPAddr.Grammar
import all CedarRustModel.Ext.Convert
import all Cedar.Thm.Ext.IPAddr.Lemmas

/-! `XL.parseIP` (the shadow of the model's IP parser) is Lean's `IPAddr.ip`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.deprecated false

namespace CedarRustModel.XL

open Cedar.Spec.Ext Cedar.Spec.Ext.IPAddr Cedar.Thm Cedar.Thm.IPAddr String

open Classical

section

/-! ## Lists -/

theorem splitAll_cons (c d : Char) (l : List Char) :
    splitAll c (d :: l) = if d = c then [] :: splitAll c l else consFirst d (splitAll c l) := by
  rw [splitAll]

theorem splitAll_ne_nil (c : Char) (l : List Char) : splitAll c l ≠ [] := by
  cases l with
  | nil => simp [splitAll]
  | cons d l =>
    rw [splitAll_cons]; split
    · simp
    · unfold consFirst; split <;> simp

theorem splitAll_join (c : Char) (l : List Char) : [c].intercalate (splitAll c l) = l := by
  induction l with
  | nil => simp [splitAll]
  | cons d l ih =>
    rw [splitAll_cons]
    obtain ⟨p, ps, hp⟩ := List.exists_cons_of_ne_nil (splitAll_ne_nil c l)
    rw [hp] at ih ⊢
    split
    · rename_i h; subst h; simp [ih]
    · simp only [consFirst, List.intercalate_cons_cons_left, ih]

theorem splitAll_no (c : Char) (l : List Char) : ∀ p ∈ splitAll c l, c ∉ p := by
  induction l with
  | nil => simp [splitAll]
  | cons d l ih =>
    rw [splitAll_cons]
    obtain ⟨q, qs, hq⟩ := List.exists_cons_of_ne_nil (splitAll_ne_nil c l)
    rw [hq] at ih ⊢
    split
    · rename_i h; intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp
      · exact ih p (by simp [hp])
    · rename_i h; intro p hp
      simp only [consFirst, List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp only [List.mem_cons, not_or]; exact ⟨Ne.symm h, ih q (by simp)⟩
      · exact ih p (by simp [hp])

theorem splitAll_of_no (c : Char) (l : List Char) (h : c ∉ l) : splitAll c l = [l] := by
  induction l with
  | nil => simp [splitAll]
  | cons d l ih =>
    simp only [List.mem_cons, not_or] at h
    rw [splitAll_cons, if_neg (Ne.symm h.1), ih h.2]; rfl

theorem splitAll_append (c : Char) (a b : List Char) (h : c ∉ a) :
    splitAll c (a ++ c :: b) = a :: splitAll c b := by
  induction a with
  | nil => simp [splitAll]
  | cons d a ih =>
    simp only [List.mem_cons, not_or] at h
    rw [List.cons_append, splitAll_cons, if_neg (Ne.symm h.1), ih h.2]; rfl

theorem splitAll_intercalate (c : Char) (gs : List (List Char)) (hne : gs ≠ [])
    (h : ∀ g ∈ gs, c ∉ g) : splitAll c ([c].intercalate gs) = gs := by
  induction gs with
  | nil => contradiction
  | cons g gs ih =>
    cases gs with
    | nil => simp [splitAll_of_no c g (h g (by simp))]
    | cons g' gs' =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
        splitAll_append c g _ (h g (by simp)), ih (by simp) (fun x hx => h x (by simp [hx]))]

def noDC : List Char → Prop
  | c :: d :: l => ¬(c = ':' ∧ d = ':') ∧ noDC (d :: l)
  | _ => True

theorem noDC_tail {c : Char} {l : List Char} (h : noDC (c :: l)) : noDC l := by
  cases l with
  | nil => trivial
  | cons d l => exact h.2

theorem noDC_cons {c : Char} {l : List Char} (h : noDC l) (hc : ¬(c = ':' ∧ l.head? = some ':')) :
    noDC (c :: l) := by
  cases l with
  | nil => trivial
  | cons d l => exact ⟨by simpa using hc, h⟩

theorem noDC_of_no (l : List Char) (h : ':' ∉ l) : noDC l := by
  induction l with
  | nil => trivial
  | cons c l ih =>
    simp only [List.mem_cons, not_or] at h
    exact noDC_cons (ih h.2) (fun hc => h.1 hc.1.symm)

theorem noDC_append (a b : List Char) (ha : ':' ∉ a) (hb : noDC b) (hbh : b.head? ≠ some ':') :
    noDC (a ++ ':' :: b) := by
  induction a with
  | nil => exact noDC_cons hb (fun h => hbh h.2)
  | cons c a ih =>
    simp only [List.mem_cons, not_or] at ha
    exact noDC_cons (ih ha.2) (fun h => ha.1 h.1.symm)

theorem splitDC_cons (c : Char) (rest : List Char) :
    splitDC (c :: rest) = if c = ':' ∧ rest.head? = some ':' then some ([], rest.tail)
      else (splitDC rest).map fun p => (c :: p.1, p.2) := by
  rw [splitDC]

theorem splitDC_append (a b : List Char) (h : noDC (a ++ [':'])) :
    splitDC (a ++ ':' :: ':' :: b) = some (a, b) := by
  induction a with
  | nil => simp [splitDC_cons]
  | cons d a ih =>
    rw [List.cons_append, splitDC_cons]
    have hd : ¬(d = ':' ∧ (a ++ ':' :: ':' :: b).head? = some ':') := by
      cases a with
      | nil => simpa [noDC] using h
      | cons e a => simpa [noDC] using h.1
    rw [if_neg hd, ih (noDC_tail h)]
    rfl

theorem splitDC_none (l : List Char) (h : noDC l) : splitDC l = none := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [splitDC_cons, ih (noDC_tail h)]
    cases l with
    | nil => simp
    | cons d l => simp only [List.head?_cons, Option.some.injEq]; rw [if_neg h.1]; rfl

theorem splitDC_some {l a b : List Char} (h : splitDC l = some (a, b)) : l = a ++ ':' :: ':' :: b := by
  induction l generalizing a b with
  | nil => simp [splitDC] at h
  | cons c l ih =>
    rw [splitDC_cons] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hh⟩ := hc
      cases l with
      | nil => simp at hh
      | cons e l => simp at hh; subst hh; rfl
    · cases hs : splitDC l with
      | none => simp [hs] at h
      | some p =>
        obtain ⟨a', b'⟩ := p
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rw [ih hs]; rfl

theorem mem_intercalate {c x : Char} {gs : List (List Char)} (h : x ∈ [c].intercalate gs) :
    x = c ∨ ∃ g ∈ gs, x ∈ g := by
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    cases gs with
    | nil => simp at h; exact Or.inr ⟨g, by simp, h⟩
    | cons g' gs' =>
      rw [List.intercalate_cons_cons] at h
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with (h | h) | h
      · exact Or.inr ⟨g, by simp, h⟩
      · exact Or.inl h
      · rcases ih h with h | ⟨g'', hg, hx⟩
        · exact Or.inl h
        · exact Or.inr ⟨g'', by simp [hg], hx⟩

theorem noDC_intercalate (gs : List (List Char)) (hne : gs ≠ [])
    (hg : ∀ g ∈ gs, g ≠ [] ∧ ':' ∉ g) : noDC ([':'].intercalate gs ++ [':']) := by
  induction gs with
  | nil => contradiction
  | cons g gs ih =>
    cases gs with
    | nil => simpa using noDC_append g [] (hg g (by simp)).2 trivial (by simp)
    | cons g' gs' =>
      rw [List.intercalate_cons_cons, List.append_assoc, List.append_assoc, List.singleton_append]
      apply noDC_append g _ (hg g (by simp)).2
      · exact ih (by simp) (fun x hx => hg x (by simp [hx]))
      · obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (hg g' (by simp)).1
        have : e ≠ ':' := by intro h; apply (hg g' (by simp)).2; rw [he, h]; simp
        subst he; simp [this]

theorem length_intercalate (c : Char) (gs : List (List Char)) (hne : gs ≠ []) :
    ([c].intercalate gs).length + 1 = (gs.map List.length).sum + gs.length := by
  induction gs with
  | nil => contradiction
  | cons g gs ih =>
    cases gs with
    | nil => simp
    | cons g' gs' =>
      rw [List.intercalate_cons_cons]
      have := ih (by simp)
      simp only [List.length_append, List.length_singleton, List.map_cons, List.sum_cons,
        List.length_cons, List.length_nil] at this ⊢
      omega

theorem utf8Len_ascii (l : List Char) (h : ∀ c ∈ l, c.toNat < 128) : utf8Len l = l.length := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    simp only [utf8Len_cons, List.length_cons]
    rw [ih (fun x hx => h x (by simp [hx]))]
    have := h c (by simp)
    rw [utf8Size_eq, if_pos (by omega)]; omega


/-! ## Groups -/

theorem startsWith0 (l : List Char) : (String.ofList l).startsWith "0" = true ↔ l.head? = some '0' := by
  cases l with
  | nil => simp
  | cons c l => simp; exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem ofList_eq0 (l : List Char) : String.ofList l = "0" ↔ l = ['0'] := by
  constructor
  · intro h; have := congrArg String.toList h; simpa using this
  · intro h; subst h; rfl

theorem isCanonicalNat_ofList (l : List Char) :
    IsCanonicalNat (String.ofList l) ↔
      (l ≠ [] ∧ allDigits l = true) ∧ ¬(l.head? = some '0' ∧ l ≠ ['0']) := by
  simp only [IsCanonicalNat, isDigits_ofList, startsWith0, ofList_eq0]
  tauto

theorem digits_lt_of_len (l : List Char) (h : allDigits l = true) (n : Nat) (hl : l.length ≤ n) :
    digitsVal 0 l < 10 ^ n :=
  Nat.lt_of_lt_of_le (digitsVal_lt l h) (Nat.pow_le_pow_right (by omega) hl)

theorem v4Octet_eq (l : List Char) :
    v4Octet l = if IsCanonicalNat (String.ofList l) ∧ l.length ≤ 3 ∧ natOf (String.ofList l) ≤ 255
      then some (natOf (String.ofList l)) else none := by
  unfold v4Octet
  rw [isCanonicalNat_ofList]
  by_cases h : (l ≠ [] ∧ allDigits l = true) ∧ ¬(l.head? = some '0' ∧ l ≠ ['0']) ∧ l.length ≤ 3
  · have hlt := digits_lt_of_len l h.1.2 3 h.2.2
    norm_num at hlt
    rw [if_pos ⟨h.1.1, h.1.2, h.2.2, h.2.1⟩, digU64_eq 0 l (by scalar_tac), natOf_ofList l h.1]
    rw [if_pos ⟨h.1.2, by rw [U64_max_eq]; omega⟩]
    simp only [Nat.zero_mul, Nat.zero_add, Option.bind_some]
    by_cases h2 : digitsVal 0 l ≤ 255
    · rw [if_pos h2, if_pos ⟨⟨h.1, h.2.1⟩, h.2.2, h2⟩]
    · rw [if_neg h2, if_neg (by tauto)]
  · rw [if_neg (by tauto), if_neg (by tauto)]

theorem isHex_eq (c : Char) : isHex c = isHexDigit c := rfl
theorem hexVal_eq (c : Char) : hexVal c = toHexNat c := rfl

theorem hexDig_eq (acc : Nat) (l : List Char) (h : (acc + 1) * 16 ^ l.length ≤ 65536) :
    hexDig acc l = if l.all isHex then some (l.foldl (fun n c => n * 16 + hexVal c) acc) else none := by
  induction l generalizing acc with
  | nil => simp [hexDig]
  | cons c l ih =>
    simp only [hexDig, List.all_cons, List.foldl_cons, Bool.and_eq_true]
    simp only [List.length_cons, Nat.pow_succ] at h
    have hP : 1 ≤ 16 ^ l.length := Nat.one_le_pow _ _ (by omega)
    by_cases hc : isHex c = true
    · have hv := hexVal_le c hc
      have ha : acc < 4096 := by nlinarith
      rw [if_pos ⟨hc, ha⟩, ih _ (by nlinarith)]
      simp [hc]
    · simp [hc]

theorem v6Group_eq (l : List Char) :
    v6Group l = if IsHexGroup (String.ofList l) then some (hexValue (String.ofList l)) else none := by
  unfold v6Group
  simp only [IsHexGroup, String.length_ofList, String.toList_ofList, hexValue, String.foldl_eq_foldl_toList, String.toList_ofList]
  by_cases h1 : l = []
  · simp [h1]
  by_cases h2 : l.length ≤ 4
  · have hlen : 0 < l.length := List.length_pos_iff.2 h1
    rw [if_neg h1, if_pos h2, hexDig_eq 0 l (by
      calc (0 + 1) * 16 ^ l.length ≤ 16 ^ 4 := by simpa using Nat.pow_le_pow_right (by omega) h2
        _ = 65536 := by norm_num)]
    simp only [List.all_eq_true, isHex_eq, hexVal_eq]
    by_cases h3 : ∀ x ∈ l, isHexDigit x = true
    · simp [h3, hlen, h2]
    · simp [h3]
  · simp [h1, h2]

theorem v6GroupsList_eq (gs : List (List Char)) :
    v6GroupsList gs = if ∀ g ∈ gs, IsHexGroup (String.ofList g)
      then some (gs.map fun g => hexValue (String.ofList g)) else none := by
  induction gs with
  | nil => simp [v6GroupsList]
  | cons g gs ih =>
    simp only [v6GroupsList, v6Group_eq, ih]
    by_cases h1 : IsHexGroup (String.ofList g)
    · by_cases h2 : ∀ g ∈ gs, IsHexGroup (String.ofList g)
      · simp [h1, h2]
      · simp [h1, h2]
    · simp [h1]

theorem parsePrefix_eq (l : List Char) (max maxLen : Nat) (hmax : max ≤ 255) (hlen : maxLen ≤ 3) :
    parsePrefix l max maxLen = if IsCanonicalNat (String.ofList l) ∧ (String.ofList l).length ≤ maxLen ∧
        natOf (String.ofList l) ≤ max then some (natOf (String.ofList l)) else none := by
  rw [isCanonicalNat_ofList, String.length_ofList]
  unfold parsePrefix
  by_cases hd : allDigits l = true
  · have hasc : ∀ c ∈ l, c.toNat < 128 := by
      intro c hc
      simp only [allDigits, List.all_eq_true] at hd
      have := (isDigit_iff c).1 (hd c hc); omega
    rw [utf8Len_ascii l hasc]
    by_cases hl : l = []
    · subst hl; simp [parseU8, parseU64']
    by_cases hlen : l.length ≤ maxLen
    · have hlt := digits_lt_of_len l hd 3 (by omega)
      norm_num at hlt
      have hu8 : parseU8 l = if digitsVal 0 l ≤ 255 then some (digitsVal 0 l) else none := by
        rw [parseU8, parseU64'_digits l hl hd, if_pos (by rw [U64_max_eq]; omega)]; rfl
      rw [natOf_ofList l ⟨hl, hd⟩, if_pos hlen, if_pos hd, hu8]
      by_cases h0 : l.head? = some '0'
      · by_cases h1 : l = ['0']
        · subst h1; simp [digitsVal]; simp at hlen; omega
        · simp [h0, h1]
      · by_cases h2 : digitsVal 0 l ≤ 255
        · by_cases h3 : digitsVal 0 l ≤ max
          · simp [h0, h2, h3, hl, hd, hlen]
          · simp [h0, h2, h3]
        · simp [h0, h2]; intros; omega
    · rw [if_neg hlen, if_neg (by tauto)]
  · simp [hd]

/-! ## Addresses -/

theorem utf8Len_append (a b : List Char) : utf8Len (a ++ b) = utf8Len a + utf8Len b := by
  simp [utf8Len]

theorem splitFirst_of_no (c : Char) (l : List Char) (h : c ∉ l) : splitFirst c l = none := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp only [List.mem_cons, not_or] at h
    simp [splitFirst, Ne.symm h.1, ih h.2]

theorem noDC_of_append {a b : List Char} (h : noDC (a ++ b)) : noDC a := by
  induction a with
  | nil => trivial
  | cons c a ih =>
    cases a with
    | nil => trivial
    | cons d a => exact ⟨h.1, ih h.2⟩

theorem v6OfGroups_map (gs : List String) :
    v6OfGroups (gs.map hexValue) = finishV6 (groupValues gs) := by
  rcases gs with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, _ | ⟨g5, _ | ⟨g6, _ | ⟨g7, _ | ⟨g8, gs⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    rfl

theorem toList_v4 (v : V4Components) :
    v.asString.toList =
      v.g₀.toList ++ ('.' :: (v.g₁.toList ++ ('.' :: (v.g₂.toList ++ ('.' :: v.g₃.toList))))) := by
  simp [V4Components.asString]

theorem canonical_no {s : String} (h : IsCanonicalNat s) {c : Char} (hc : c.isDigit = false) :
    c ∉ s.toList := by
  intro hm; have := h.1.2 c hm; simp_all

theorem parseV4_v4 (v : V4Components) (hsyn : v.syntaxWf) (hcon : v.constraintsWf) :
    parseV4 v.asString.toList = some v.toAddr := by
  obtain ⟨⟨h0, l0⟩, ⟨h1, l1⟩, ⟨h2, l2⟩, ⟨h3, l3⟩⟩ := hsyn
  obtain ⟨c0, c1, c2, c3⟩ := hcon
  rw [toList_v4, parseV4, splitAll_append _ _ _ (canonical_no h0 (by decide)),
    splitAll_append _ _ _ (canonical_no h1 (by decide)),
    splitAll_append _ _ _ (canonical_no h2 (by decide)),
    splitAll_of_no _ _ (canonical_no h3 (by decide))]
  simp only [v4Octets, v4Octet_eq, String.ofList_toList, String.length_toList]
  rw [if_pos ⟨h0, l0, c0⟩, if_pos ⟨h1, l1, c1⟩, if_pos ⟨h2, l2, c2⟩, if_pos ⟨h3, l3, c3⟩]
  rfl

theorem hexGroup_facts {s : String} (h : IsHexGroup s) :
    s.toList ≠ [] ∧ ':' ∉ s.toList ∧ '.' ∉ s.toList ∧ '/' ∉ s.toList := by
  obtain ⟨hl, _, hh⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro he; rw [← String.length_toList, he] at hl; simp at hl
  all_goals (intro hm; have := hh _ hm; revert this; decide)

theorem toList_v6_full (gs : List String) :
    (V6Components.full gs).asString.toList = [':'].intercalate (gs.map String.toList) := by
  simp [V6Components.asString]

theorem toList_v6_gap (L R : List String) :
    (V6Components.gap L R).asString.toList =
      [':'].intercalate (L.map String.toList) ++ (':' :: ':' :: [':'].intercalate (R.map String.toList)) := by
  simp [V6Components.asString]

theorem v6Groups_intercalate (gs : List String) (h : ∀ g ∈ gs, IsHexGroup g) :
    v6Groups ([':'].intercalate (gs.map String.toList)) = some (gs.map hexValue) := by
  cases gs with
  | nil => rfl
  | cons g gs =>
    have hg := hexGroup_facts (h g (by simp))
    have hne : [':'].intercalate ((g :: gs).map String.toList) ≠ [] := by
      obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil hg.1
      simp [he]
    rw [v6Groups, if_neg hne, splitAll_intercalate _ _ (by simp)
      (fun x hx => by
        simp only [List.map_cons, List.mem_cons, List.mem_map] at hx
        rcases hx with rfl | ⟨y, hy, rfl⟩
        · exact hg.2.1
        · exact (hexGroup_facts (h y (by simp [hy]))).2.1),
      v6GroupsList_eq, if_pos]
    · simp
    · intro x hx
      simp only [List.map_cons, List.mem_cons, List.mem_map] at hx
      rcases hx with rfl | ⟨y, hy, rfl⟩
      · simpa using h g (by simp)
      · simpa using h y (by simp [hy])

theorem intercalate_facts (gs : List String) (h : ∀ g ∈ gs, IsHexGroup g) :
    ∀ c ∈ [':'].intercalate (gs.map String.toList), c ≠ '.' ∧ c ≠ '/' ∧ c.toNat < 128 := by
  intro c hc
  rcases mem_intercalate hc with rfl | ⟨g, hg, hcg⟩
  · decide
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
    obtain ⟨_, _, hh⟩ := h y hy
    have := hh c hcg
    refine ⟨?_, ?_, ?_⟩
    · intro e; subst e; revert this; decide
    · intro e; subst e; revert this; decide
    · simp only [isHexDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at this
      rcases this with (h1 | ⟨_, h2⟩) | ⟨_, h2⟩
      · have := (isDigit_iff c).1 h1; omega
      · rw [char_le_iff] at h2; have : 'f'.toNat = 102 := by decide
        omega
      · rw [char_le_iff] at h2; have : 'F'.toNat = 70 := by decide
        omega

theorem parseV4_none_of_no_dot (l : List Char) (h : '.' ∉ l) : parseV4 l = none := by
  rw [parseV4, splitAll_of_no _ _ h]

theorem parseV6_v6 (v : V6Components) (hsyn : v.syntaxWf) :
    parseV6 v.asString.toList = some v.toAddr := by
  cases v with
  | full gs =>
    obtain ⟨hlen, hh⟩ := hsyn
    have hne : gs ≠ [] := by intro h; subst h; simp at hlen
    rw [toList_v6_full, parseV6, splitDC_none _ (noDC_of_append (noDC_intercalate _ (by simpa using hne)
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact ⟨(hexGroup_facts (hh y hy)).1, (hexGroup_facts (hh y hy)).2.1⟩)))]
    simp only [v6Groups_intercalate gs hh, Option.bind_some, v6OfGroups_map]
    exact finishV6_groupValues_eq_toAddr (v := .full gs) (by simpa [V6Components.expand] using hlen)
  | gap L R =>
    obtain ⟨hlen, hL, hR⟩ := hsyn
    have hdc : noDC ([':'].intercalate (L.map String.toList) ++ [':']) := by
      cases L with
      | nil => trivial
      | cons g L =>
        exact noDC_intercalate _ (by simp) (fun x hx => by
          obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
          exact ⟨(hexGroup_facts (hL y hy)).1, (hexGroup_facts (hL y hy)).2.1⟩)
    rw [toList_v6_gap, parseV6, splitDC_append _ _ hdc]
    simp only [v6Groups_intercalate L hL, v6Groups_intercalate R hR, subLen, List.length_map]
    rw [if_pos (show L.length ≤ 8 by omega)]
    dsimp only
    rw [if_pos (show R.length ≤ 8 - L.length by omega)]
    dsimp only
    rw [if_neg (show ¬(8 - L.length - R.length = 0) by omega)]
    have e : L.map hexValue ++ (List.replicate (8 - L.length - R.length) 0 ++ R.map hexValue) =
        (V6Components.gap L R).expand.map hexValue := by
      simp [V6Components.expand, hexValue_zero]; omega
    rw [e, v6OfGroups_map]
    exact finishV6_groupValues_eq_toAddr (by simp [V6Components.expand]; omega)

/-! ## Networks: completeness -/

theorem v4_chars (v : V4Components) (hsyn : v.syntaxWf) :
    ∀ c ∈ v.asString.toList, c ≠ ':' ∧ c ≠ '/' ∧ c.toNat < 128 := by
  obtain ⟨⟨h0, _⟩, ⟨h1, _⟩, ⟨h2, _⟩, ⟨h3, _⟩⟩ := hsyn
  have dig : ∀ {s : String}, IsCanonicalNat s → ∀ c ∈ s.toList, c ≠ ':' ∧ c ≠ '/' ∧ c.toNat < 128 := by
    intro s hs c hc
    have := (isDigit_iff c).1 (hs.1.2 c hc)
    refine ⟨?_, ?_, by omega⟩ <;> (intro e; subst e; revert this; decide)
  intro c hc
  rw [toList_v4] at hc
  simp only [List.mem_append, List.mem_cons] at hc
  rcases hc with h | rfl | h | rfl | h | rfl | h
  · exact dig h0 c h
  · decide
  · exact dig h1 c h
  · decide
  · exact dig h2 c h
  · decide
  · exact dig h3 c h

theorem v4_len (v : V4Components) (hsyn : v.syntaxWf) : v.asString.toList.length ≤ 15 := by
  obtain ⟨⟨_, l0⟩, ⟨_, l1⟩, ⟨_, l2⟩, ⟨_, l3⟩⟩ := hsyn
  rw [toList_v4]; simp only [List.length_append, List.length_cons, String.length_toList]; omega

theorem v6_chars (v : V6Components) (hsyn : v.syntaxWf) :
    ∀ c ∈ v.asString.toList, c ≠ '.' ∧ c ≠ '/' ∧ c.toNat < 128 := by
  cases v with
  | full gs => rw [toList_v6_full]; exact intercalate_facts gs hsyn.2
  | gap L R =>
    rw [toList_v6_gap]; intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with h | rfl | rfl | h
    · exact intercalate_facts L hsyn.2.1 c h
    · decide
    · decide
    · exact intercalate_facts R hsyn.2.2 c h

theorem len_intercalate_le (gs : List String) (h : ∀ g ∈ gs, IsHexGroup g) :
    ([':'].intercalate (gs.map String.toList)).length + 1 ≤ 5 * gs.length + (if gs = [] then 1 else 0) := by
  cases gs with
  | nil => simp
  | cons g gs =>
    have := length_intercalate ':' ((g :: gs).map String.toList) (by simp)
    have hs : ((g :: gs).map String.toList |>.map List.length).sum ≤ 4 * (g :: gs).length := by
      have : ∀ x ∈ ((g :: gs).map String.toList).map List.length, x ≤ 4 := by
        intro x hx
        simp only [List.map_map, List.mem_map, Function.comp] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        rw [String.length_toList]; exact (h y hy).2.1
      have := List.sum_le_card_nsmul _ 4 this
      simpa [mul_comm] using this
    simp only [List.length_map] at this hs ⊢
    omega

theorem v6_len (v : V6Components) (hsyn : v.syntaxWf) : v.asString.toList.length ≤ 39 := by
  cases v with
  | full gs =>
    rw [toList_v6_full]
    have h1 := len_intercalate_le gs hsyn.2
    have h2 : gs.length = 8 := hsyn.1
    have h3 : gs ≠ [] := by intro h; subst h; simp at h2
    rw [if_neg h3] at h1
    omega
  | gap L R =>
    rw [toList_v6_gap]
    have h1 := len_intercalate_le L hsyn.2.1
    have h2 := len_intercalate_le R hsyn.2.2
    have h3 : L.length + R.length < 8 := hsyn.1
    simp only [List.length_append, List.length_cons]
    split_ifs at h1 h2 <;> omega

theorem count_zero {c : Char} {l : List Char} (h : c ∉ l) : l.count c = 0 :=
  List.count_eq_zero.2 h

def fullWidth : BitVec 32 ⊕ BitVec 128 → Nat
  | .inl _ => 32
  | .inr _ => 128

theorem parseIP_none_pre (A : List Char) (x : BitVec 32 ⊕ BitVec 128) (hA : parseAddr A = some x)
    (hch : ∀ c ∈ A, c ≠ '/' ∧ c.toNat < 128) (hcnt : A.count ':' = 0 ∨ A.count '.' = 0)
    (hlen : A.length ≤ 43) :
    parseIP A = some (netOf x (fullWidth x)) := by
  rw [parseIP, utf8Len_ascii A (fun c hc => (hch c hc).2), if_neg (by omega), if_neg (by omega),
    splitFirst_of_no _ _ (fun hm => (hch _ hm).1 rfl)]
  dsimp only
  rw [hA]
  cases x <;> rfl

theorem digits_chars {p : String} (h : IsCanonicalNat p) :
    ∀ c ∈ p.toList, c ≠ ':' ∧ c ≠ '.' ∧ c ≠ '/' ∧ c.toNat < 128 := by
  intro c hc
  have := (isDigit_iff c).1 (h.1.2 c hc)
  refine ⟨?_, ?_, ?_, by omega⟩ <;> (intro e; subst e; revert this; decide)

theorem parseIP_some_pre (A : List Char) (x : BitVec 32 ⊕ BitVec 128) (hA : parseAddr A = some x)
    (hch : ∀ c ∈ A, c ≠ '/' ∧ c.toNat < 128) (hcnt : A.count ':' = 0 ∨ A.count '.' = 0)
    (p : String) (hp : IsCanonicalNat p) (hpl : p.length ≤ 3) (hlen : A.length ≤ 39) :
    parseIP (A ++ '/' :: p.toList) =
      (match x with
       | .inl _ => parsePrefix p.toList 32 2
       | .inr _ => parsePrefix p.toList 128 3).map (netOf x) := by
  have hpc := digits_chars hp
  have hall : ∀ c ∈ A ++ '/' :: p.toList, c.toNat < 128 := by
    intro c hc
    simp only [List.mem_append, List.mem_cons] at hc
    rcases hc with h | rfl | h
    · exact (hch c h).2
    · decide
    · exact (hpc c h).2.2.2
  have hcp1 : p.toList.count ':' = 0 := count_zero (fun hm => (hpc _ hm).1 rfl)
  have hcp2 : p.toList.count '.' = 0 := count_zero (fun hm => (hpc _ hm).2.1 rfl)
  rw [parseIP, utf8Len_ascii _ hall, if_neg (by simp [String.length_toList]; omega)]
  rw [if_neg (by simp [List.count_append, List.count_cons, hcp1, hcp2]; omega)]
  rw [splitFirst_append _ _ _ (fun hm => (hch _ hm).1 rfl)]
  dsimp only
  rw [hA]
  cases x <;> rfl

theorem netOf_v4 (v : V4Components) (pre : Option String) :
    v4Value v pre = netOf (.inl v.toAddr) (match pre with | none => 32 | some p => natOf p) := by
  cases pre <;> rfl

theorem netOf_v6 (v : V6Components) (pre : Option String) :
    v6Value v pre = netOf (.inr v.toAddr) (match pre with | none => 128 | some p => natOf p) := by
  cases pre <;> rfl

theorem parseIP_complete {str : String} {net : IPNet} (h : IsIPNetValue str net) :
    parseIP str.toList = some net := by
  rcases h with ⟨v, pre, ⟨hsyn, hcon, hpre, rfl⟩, rfl⟩ | ⟨v, pre, ⟨hsyn, hpre, rfl⟩, rfl⟩
  · have hA : parseAddr v.asString.toList = some (.inl v.toAddr) := by
      simp [parseAddr, parseV4_v4 v hsyn hcon]
    have hch := v4_chars v hsyn
    have hcnt : v.asString.toList.count ':' = 0 := count_zero (fun hm => (hch _ hm).1 rfl)
    have hlen := v4_len v hsyn
    rw [netOf_v4]
    cases pre with
    | none =>
      simpa [fullWidth] using parseIP_none_pre _ _ hA (fun c hc => ⟨(hch c hc).2.1, (hch c hc).2.2⟩) (Or.inl hcnt)
        (by omega)
    | some p =>
      obtain ⟨hp, hpl, hpv⟩ := hpre
      have := parseIP_some_pre _ _ hA (fun c hc => ⟨(hch c hc).2.1, (hch c hc).2.2⟩) (Or.inl hcnt) p hp
        (by omega) (by omega)
      show parseIP (v.asString ++ ("/" ++ p)).toList = _
      rw [String.toList_append, String.toList_append,
        show "/".toList ++ p.toList = '/' :: p.toList by rfl, this]
      dsimp only
      rw [parsePrefix_eq _ _ _ (by decide) (by decide), String.ofList_toList,
        if_pos ⟨hp, hpl, by rw [show ADDR_SIZE V4_WIDTH = 32 from rfl] at hpv; exact hpv⟩]
      rfl
  · have hA : parseAddr v.asString.toList = some (.inr v.toAddr) := by
      simp [parseAddr, parseV6_v6 v hsyn,
        parseV4_none_of_no_dot _ (fun hm => (v6_chars v hsyn _ hm).1 rfl)]
    have hch := v6_chars v hsyn
    have hcnt : v.asString.toList.count '.' = 0 := count_zero (fun hm => (hch _ hm).1 rfl)
    have hlen := v6_len v hsyn
    rw [netOf_v6]
    cases pre with
    | none =>
      simpa [fullWidth] using parseIP_none_pre _ _ hA (fun c hc => ⟨(hch c hc).2.1, (hch c hc).2.2⟩) (Or.inr hcnt)
        (by omega)
    | some p =>
      obtain ⟨hp, hpl, hpv⟩ := hpre
      have := parseIP_some_pre _ _ hA (fun c hc => ⟨(hch c hc).2.1, (hch c hc).2.2⟩) (Or.inr hcnt) p hp
        (by omega) hlen
      show parseIP (v.asString ++ ("/" ++ p)).toList = _
      rw [String.toList_append, String.toList_append,
        show "/".toList ++ p.toList = '/' :: p.toList by rfl, this]
      dsimp only
      rw [parsePrefix_eq _ _ _ (by decide) (by decide), String.ofList_toList,
        if_pos ⟨hp, hpl, by rw [show ADDR_SIZE V6_WIDTH = 128 from rfl] at hpv; exact hpv⟩]
      rfl

/-! ## Networks: soundness -/

theorem v4Octet_some {g : List Char} {n : Nat} (h : v4Octet g = some n) :
    (IsCanonicalNat (String.ofList g) ∧ (String.ofList g).length ≤ 3) ∧
      natOf (String.ofList g) ≤ 255 ∧ n = natOf (String.ofList g) := by
  rw [v4Octet_eq] at h
  split at h
  · rename_i hc; simp only [Option.some.injEq] at h
    exact ⟨⟨hc.1, by simpa using hc.2.1⟩, hc.2.2, h.symm⟩
  · simp at h

theorem parseV4_some {a : List Char} {x : BitVec 32} (h : parseV4 a = some x) :
    ∃ v : V4Components, v.syntaxWf ∧ v.constraintsWf ∧ a = v.asString.toList ∧ x = v.toAddr := by
  unfold parseV4 at h
  have hj := splitAll_join '.' a
  generalize hs : splitAll '.' a = parts at h hj
  rcases parts with _ | ⟨g0, _ | ⟨g1, _ | ⟨g2, _ | ⟨g3, _ | ⟨g4, parts⟩⟩⟩⟩⟩ <;> try simp at h
  unfold v4Octets at h
  cases h0 : v4Octet g0 <;> cases h1 : v4Octet g1 <;> cases h2 : v4Octet g2 <;>
    cases h3 : v4Octet g3 <;> simp only [h0, h1, h2, h3, reduceCtorEq, Option.some.injEq] at h
  obtain ⟨s0, c0, rfl⟩ := v4Octet_some h0
  obtain ⟨s1, c1, rfl⟩ := v4Octet_some h1
  obtain ⟨s2, c2, rfl⟩ := v4Octet_some h2
  obtain ⟨s3, c3, rfl⟩ := v4Octet_some h3
  refine ⟨⟨String.ofList g0, String.ofList g1, String.ofList g2, String.ofList g3⟩,
    ⟨s0, s1, s2, s3⟩, ⟨c0, c1, c2, c3⟩, ?_, h.symm⟩
  rw [toList_v4]; simp only [String.toList_ofList]
  rw [← hj]; simp

theorem v6Groups_some {a : List Char} {ns : List Nat} (h : v6Groups a = some ns) :
    ∃ gs : List String, (∀ g ∈ gs, IsHexGroup g) ∧ a = [':'].intercalate (gs.map String.toList) ∧
      ns = gs.map hexValue := by
  unfold v6Groups at h
  split at h
  · rename_i ha; subst ha; simp only [Option.some.injEq] at h; subst h
    exact ⟨[], by simp, rfl, rfl⟩
  · rw [v6GroupsList_eq] at h
    split at h
    · rename_i hh; simp only [Option.some.injEq] at h; subst h
      refine ⟨(splitAll ':' a).map String.ofList, by simpa using hh, ?_, by simp⟩
      simp [splitAll_join]
    · simp at h

theorem v6OfGroups_length {ns : List Nat} {x : BitVec 128} (h : v6OfGroups ns = some x) : ns.length = 8 := by
  rcases ns with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, _ | ⟨a8, ns⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
    first | rfl | simp [v6OfGroups] at h

theorem parseV6_some {a : List Char} {x : BitVec 128} (h : parseV6 a = some x) :
    ∃ v : V6Components, v.syntaxWf ∧ a = v.asString.toList ∧ x = v.toAddr := by
  unfold parseV6 at h
  cases hdc : splitDC a with
  | none =>
    rw [hdc] at h; try dsimp only at h
    cases hg : v6Groups a with
    | none => simp [hg] at h
    | some ns =>
      rw [hg, Option.bind_some] at h
      obtain ⟨gs, hh, rfl, rfl⟩ := v6Groups_some hg
      have hlen := v6OfGroups_length h
      have hfin := finishV6_groupValues_eq_toAddr (v := .full gs) (by simpa [V6Components.expand] using hlen)
      simp only [V6Components.expand] at hfin
      rw [v6OfGroups_map, hfin] at h
      exact ⟨.full gs, ⟨by simpa using hlen, hh⟩, by rw [toList_v6_full], (Option.some.inj h).symm⟩
  | some q =>
    obtain ⟨A, B⟩ := q
    rw [hdc] at h; try dsimp only at h
    have ha := splitDC_some hdc
    cases hgA : v6Groups A with
    | none => simp [hgA] at h
    | some gl =>
      cases hgB : v6Groups B with
      | none => simp [hgA, hgB] at h
      | some gr =>
        rw [hgA, hgB] at h; try dsimp only at h
        obtain ⟨L, hL, rfl, rfl⟩ := v6Groups_some hgA
        obtain ⟨R, hR, rfl, rfl⟩ := v6Groups_some hgB
        by_cases c1 : L.length ≤ 8
        swap; · simp [subLen, c1] at h
        by_cases c2 : R.length ≤ 8 - L.length
        swap; · simp [subLen, c1, c2] at h
        by_cases c3 : 8 - L.length - R.length = 0
        · simp [subLen, c1, c2, c3] at h
        simp only [subLen, List.length_map, if_pos c1, if_pos c2, if_neg c3] at h
        have e : L.map hexValue ++ (List.replicate (8 - L.length - R.length) 0 ++ R.map hexValue) =
            (V6Components.gap L R).expand.map hexValue := by
          simp [V6Components.expand, hexValue_zero]; omega
        rw [e, v6OfGroups_map, finishV6_groupValues_eq_toAddr (by simp [V6Components.expand]; omega)] at h
        exact ⟨.gap L R, ⟨by omega, hL, hR⟩, by rw [ha, toList_v6_gap], (Option.some.inj h).symm⟩

theorem parsePrefix_some {p : List Char} {max maxLen n : Nat} (hmax : max ≤ 255) (hlen : maxLen ≤ 3)
    (h : parsePrefix p max maxLen = some n) :
    (IsCanonicalNat (String.ofList p) ∧ (String.ofList p).length ≤ maxLen ∧ natOf (String.ofList p) ≤ max) ∧
      n = natOf (String.ofList p) := by
  rw [parsePrefix_eq p max maxLen hmax hlen] at h
  split at h
  · rename_i hc; exact ⟨hc, (Option.some.inj h).symm⟩
  · simp at h

theorem ofList_append_slash (a p : List Char) :
    String.ofList (a ++ '/' :: p) = String.ofList a ++ ("/" ++ String.ofList p) := by
  apply String.toList_inj.1; simp

theorem parseIP_sound {l : List Char} {net : IPNet} (h : parseIP l = some net) :
    IsIPNetValue (String.ofList l) net := by
  unfold parseIP at h
  split at h; · simp at h
  split at h; · simp at h
  cases hs : splitFirst '/' l with
  | some q =>
    obtain ⟨a, p⟩ := q
    obtain ⟨rfl, _⟩ := splitFirst_some hs
    rw [hs] at h; try dsimp only at h
    cases ha : parseAddr a with
    | none => simp [ha] at h
    | some x =>
      rw [ha] at h; try dsimp only at h
      cases x with
      | inl x =>
        have h4 : parseV4 a = some x := by
          unfold parseAddr at ha; cases h4 : parseV4 a <;> simp_all
        obtain ⟨v, hsyn, hcon, rfl, rfl⟩ := parseV4_some h4
        cases hp : parsePrefix p 32 2 with
        | none => simp [hp] at h
        | some n =>
          rw [hp] at h; simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨hpre, rfl⟩ := parsePrefix_some (by decide) (by decide) hp
          refine Or.inl ⟨v, some (String.ofList p), ⟨hsyn, hcon, hpre, ?_⟩, ?_⟩
          · rw [ofList_append_slash, String.ofList_toList]
          · rw [← h, netOf_v4]
      | inr x =>
        have h6 : parseV6 a = some x := by
          unfold parseAddr at ha; cases h4 : parseV4 a <;> simp_all
        obtain ⟨v, hsyn, rfl, rfl⟩ := parseV6_some h6
        cases hp : parsePrefix p 128 3 with
        | none => simp [hp] at h
        | some n =>
          rw [hp] at h; simp only [Option.map_some, Option.some.injEq] at h
          obtain ⟨hpre, rfl⟩ := parsePrefix_some (by decide) (by decide) hp
          refine Or.inr ⟨v, some (String.ofList p), ⟨hsyn, hpre, ?_⟩, ?_⟩
          · rw [ofList_append_slash, String.ofList_toList]
          · rw [← h, netOf_v6]
  | none =>
    rw [hs] at h; try dsimp only at h
    cases ha : parseAddr l with
    | none => simp [ha] at h
    | some x =>
      rw [ha] at h; try dsimp only at h
      cases x with
      | inl x =>
        have h4 : parseV4 l = some x := by
          unfold parseAddr at ha; cases h4 : parseV4 l <;> simp_all
        obtain ⟨v, hsyn, hcon, rfl, rfl⟩ := parseV4_some h4
        refine Or.inl ⟨v, none, ⟨hsyn, hcon, trivial, by simp⟩, ?_⟩
        rw [← Option.some.inj h, netOf_v4]
      | inr x =>
        have h6 : parseV6 l = some x := by
          unfold parseAddr at ha; cases h4 : parseV4 l <;> simp_all
        obtain ⟨v, hsyn, rfl, rfl⟩ := parseV6_some h6
        refine Or.inr ⟨v, none, ⟨hsyn, trivial, by simp⟩, ?_⟩
        rw [← Option.some.inj h, netOf_v6]

end

/-- The model's IP parser is Lean's `IPAddr.ip` -/
public theorem parseIP_eq (l : List Char) : parseIP l = IPAddr.ip (String.ofList l) := by
  cases hp : IPAddr.ip (String.ofList l) with
  | some net =>
    have := parseIP_complete (parse_sound _ net hp)
    simpa using this
  | none =>
    cases hm : parseIP l with
    | none => rfl
    | some net =>
      have := parse_complete _ net (parseIP_sound hm)
      rw [hp] at this; simp at this

end CedarRustModel.XL
