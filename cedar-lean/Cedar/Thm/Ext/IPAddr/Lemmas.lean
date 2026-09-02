module

public import Cedar.Thm.Ext.IPAddr.Grammar

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Thm.Data.String
import all Cedar.Thm.Ext.IPAddr.Grammar
import all Init.Data.String.Legacy
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred
import Init.Data.List.SplitOn.Lemmas

namespace Cedar.Thm.IPAddr
open Cedar.Spec.Ext
open IPAddr

/-! # IPAddr grammar bridge lemmas

These lemmas connect the parser-independent grammar definitions in
`Cedar.Thm.Ext.IPAddr.Grammar` (`IsWfIPNet`, `computeValue`-style `v4Value`/`v6Value`) to the actual
`Cedar.Spec.Ext.IPAddr.parse`. They culminate in the per-form parse characterizations the aggregator
`parse_sound`/`parse_complete` build on.

The parser structure (from `Cedar.Spec.Ext.IPAddr`) is:
- `parse str = if (parseIPv4Net str).isSome then parseIPv4Net str else parseIPv6Net str`;
- `parseIPv4Net` splits on `'/'`, parses four `parseNumV4` groups (split on `'.'`) and an optional
  `parsePrefixNat` prefix;
- `parseIPv6Net` splits on `'/'`, parses the address via `parseSegsV6` (which handles `::` via
  `splitOn "::"` and pads to eight hextets) and an optional `parsePrefixNat` prefix.

Each numeric primitive (`parseNumV4`, `parseNumV6`, `parsePrefixNat`) enforces the length /
leading-zero / range side conditions that the grammar predicates transcribe. -/

/-! ## Numeric-token bridges -/

/-- `parseNumV4` accepts exactly the canonical ≤ 3-digit groups with value ≤ 255, returning
    `numValue`. -/
theorem parseNumV4_eq_some {s : String} (hwf : IsCanonicalNat s ∧ s.length ≤ 3)
    (hcon : numValue s ≤ 255) :
    parseNumV4 s = some (BitVec.ofNat 8 (numValue s)) :=
  by
  unfold parseNumV4
  dsimp only
  rw [if_pos]
  · cases hnat : toNat?' s with
    | none =>
      have hs := hwf.1.1.toNat?'_isSome
      simp [hnat] at hs
    | some n =>
      simp [hnat, numValue] at hcon ⊢
      omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hwf.1.1.1, hwf.2⟩, hwf.1.2⟩

/-- Conversely, if `parseNumV4` accepts `s`, it is a canonical ≤ 3-digit group whose value is at
    most 255. -/
theorem parseNumV4_isSome_wf {s : String} (h : (parseNumV4 s).isSome) :
    (IsCanonicalNat s ∧ s.length ≤ 3) ∧ numValue s ≤ 255 :=
  by
  simp only [parseNumV4] at h
  split at h <;> rename_i hg
  · cases hnat : toNat?' s with
    | none => simp [hnat, bind, Option.bind] at h
    | some n =>
      simp only [hnat, bind, Option.bind] at h
      have hnle : n ≤ 255 := by
        by_contra hnle
        simp [hnle] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
      have hdig : IsDigits s := isDigits_of_toNat?'_isSome (by simp [hnat])
      exact ⟨⟨⟨hdig, hg.2⟩, hg.1.2⟩, by simpa [numValue, hnat] using hnle⟩
  · simp at h

/-- `parseNumV6` accepts exactly the 1–4 digit hex groups, returning `hexValue`. -/
private theorem toHexNat_le_of_isHexDigit {c : Char} (h : isHexDigit c = true) :
    toHexNat c ≤ 15 := by
  simp only [isHexDigit, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold toHexNat
  split <;> rename_i hd
  · have hb := Char.isDigit_iff_toNat.mp hd
    have hs := Nat.sub_le_sub_right hb.2 '0'.toNat
    have hc : '9'.toNat - '0'.toNat = 9 := by decide
    omega
  split <;> rename_i hl
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hl
    have hs := Nat.sub_le_sub_right
      (show c.toNat ≤ 'f'.toNat by
        simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using hl.2)
      'a'.toNat
    have hc : 'f'.toNat - 'a'.toNat = 5 := by decide
    omega
  split <;> rename_i hu
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hu
    have hs := Nat.sub_le_sub_right
      (show c.toNat ≤ 'F'.toNat by
        simpa only [Char.le_def, UInt32.le_iff_toNat_le, Char.toNat] using hu.2)
      'A'.toNat
    have hc : 'F'.toNat - 'A'.toNat = 5 := by decide
    omega
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hd hl hu
    have hfalse :
        ¬((c.isDigit = true ∨ ('a' ≤ c ∧ c ≤ 'f')) ∨ ('A' ≤ c ∧ c ≤ 'F')) :=
      not_or_intro (not_or_intro hd hl) hu
    exact (hfalse h).elim

private theorem foldHex_lt (l : List Char) (acc : Nat)
    (h : ∀ c ∈ l, isHexDigit c = true) :
    l.foldl (fun n c => n * 16 + toHexNat c) acc < (acc + 1) * 16 ^ l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons c cs ih =>
      simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
      have hdigit : toHexNat c ≤ 15 := toHexNat_le_of_isHexDigit (h c (by simp))
      have hacc : acc * 16 + toHexNat c + 1 ≤ (acc + 1) * 16 := by omega
      have htail := ih (acc * 16 + toHexNat c) (by
        intro x hx
        exact h x (by simp [hx]))
      apply Nat.lt_of_lt_of_le htail
      apply Nat.le_trans (Nat.mul_le_mul_right _ hacc)
      simp only [Nat.mul_assoc, Nat.mul_comm]
      exact Nat.le_refl _

theorem parseNumV6_eq_some {s : String} (hwf : IsHexGroup s) :
    parseNumV6 s = some (BitVec.ofNat 16 (hexValue s)) :=
  by
  have hbound :
      s.foldl (fun n c => n * 16 + toHexNat c) 0 ≤ 0xffff := by
    rw [String.foldl_eq_foldl_toList]
    have hlt := foldHex_lt s.toList 0 hwf.2.2
    simp only [Nat.zero_add, Nat.one_mul, String.length_toList] at hlt
    have hpow : 16 ^ s.length ≤ 16 ^ 4 :=
      Nat.pow_le_pow_right (by omega) hwf.2.1
    omega
  unfold parseNumV6
  rw [if_pos, if_pos hbound]
  · simp [hexValue, String.foldl_eq_foldl_toList]
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hwf.1, hwf.2.1⟩, by
      rw [String.all_bool_eq]
      simpa only [List.all_eq_true] using hwf.2.2⟩

/-- Conversely, if `parseNumV6` accepts `s` it is a well-formed hex group. -/
theorem parseNumV6_isSome_wf {s : String} (h : (parseNumV6 s).isSome) : IsHexGroup s :=
  by
  by_cases hsyn :
      (0 < s.length && s.length ≤ 4 && s.all isHexDigit) = true
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at hsyn
    rw [String.all_bool_eq] at hsyn
    exact ⟨hsyn.1.1, hsyn.1.2, by
      simpa only [List.all_eq_true] using hsyn.2⟩
  ·
    simp only [parseNumV6] at h
    rw [if_neg hsyn] at h
    simp at h

/-- `parsePrefixNat` accepts exactly the canonical numbers with at most `digits` digits and value
    at most `size`. -/
theorem parsePrefixNat_eq_some {s : String} {digits size : Nat}
    (hwf : IsCanonicalNat s ∧ s.length ≤ digits ∧ numValue s ≤ size) :
    (parsePrefixNat s digits size).isSome :=
  by
  unfold parsePrefixNat
  rw [if_pos]
  · cases hnat : toNat?' s with
    | none =>
      have hs := hwf.1.1.toNat?'_isSome
      simp [hnat] at hs
    | some n =>
      have hnle : n ≤ size := by
        simpa [numValue, hnat] using hwf.2.2
      simp [hnle]
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hwf.1.1.1, hwf.2.1⟩, hwf.1.2⟩

private theorem parsePrefixNat_eq_value {s : String} {digits size : Nat}
    (hwf : IsCanonicalNat s ∧ s.length ≤ digits ∧ numValue s ≤ size) :
    parsePrefixNat s digits size = some (Fin.ofNat (size + 1) (numValue s)) := by
  unfold parsePrefixNat
  rw [if_pos]
  · cases hnat : toNat?' s with
    | none =>
      have hs := hwf.1.1.toNat?'_isSome
      simp [hnat] at hs
    | some n =>
      have hnle : n ≤ size := by
        simpa [numValue, hnat] using hwf.2.2
      simp [hnat, hnle, numValue]
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hwf.1.1.1, hwf.2.1⟩, hwf.1.2⟩

private theorem parsePrefixNat_isSome_wf {s : String} {digits size : Nat}
    (h : (parsePrefixNat s digits size).isSome) :
    IsCanonicalNat s ∧ s.length ≤ digits ∧ numValue s ≤ size := by
  simp only [parsePrefixNat] at h
  split at h <;> rename_i hguard
  · cases hnat : toNat?' s with
    | none => simp [hnat, bind, Option.bind] at h
    | some n =>
      simp only [hnat, bind, Option.bind] at h
      have hnle : n ≤ size := by
        by_contra hnle
        simp [hnle] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hguard
      have hdig : IsDigits s := isDigits_of_toNat?'_isSome (by simp [hnat])
      exact ⟨⟨hdig, hguard.2⟩, hguard.1.2, by simpa [numValue, hnat] using hnle⟩
  · simp at h

private theorem parsePrefixNat_some_wf {s : String} {digits size : Nat}
    {pre : Fin (size + 1)} (h : parsePrefixNat s digits size = some pre) :
    (IsCanonicalNat s ∧ s.length ≤ digits ∧ numValue s ≤ size) ∧
      pre.val = numValue s := by
  have hisSome : (parsePrefixNat s digits size).isSome := by
    rw [h]
    simp
  have hwf := parsePrefixNat_isSome_wf hisSome
  have heq := parsePrefixNat_eq_value hwf
  rw [h] at heq
  injection heq with heq
  subst pre
  refine ⟨hwf, ?_⟩
  simp only [Fin.val_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]

/-! ## IPv4 form -/

private theorem noDotOfCanonical {s : String} (h : IsCanonicalNat s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hd := h.1.2 '.' hc
  simp at hd

private theorem noSlashOfCanonical {s : String} (h : IsCanonicalNat s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hd := h.1.2 '/' hc
  simp at hd

private theorem noSepAppend {s₁ s₂ : String} {p : Char → Bool}
    (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) :
    ∀ c ∈ (s₁ ++ s₂).toList, p c = false := by
  intro c hc
  rw [String.toList_append] at hc
  rcases List.mem_append.mp hc with h | h
  · exact h₁ c h
  · exact h₂ c h

private theorem noSlashDot :
    ∀ c ∈ ".".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem splitToList_eq4 (s₁ s₂ s₃ s₄ : String) (p : Char → Bool) (sep : Char)
    (hsep : p sep = true) (h₁ : ∀ c ∈ s₁.toList, p c = false)
    (h₂ : ∀ c ∈ s₂.toList, p c = false) (h₃ : ∀ c ∈ s₃.toList, p c = false)
    (h₄ : ∀ c ∈ s₄.toList, p c = false) :
    (s₁ ++ String.singleton sep ++ s₂ ++ String.singleton sep ++ s₃ ++
      String.singleton sep ++ s₄).splitToList p = [s₁, s₂, s₃, s₄] := by
  rw [String.splitToList_of_valid]
  simp only [String.toList_append, String.toList_singleton, List.append_assoc,
    List.nil_append, List.cons_append]
  rw [List.splitOnP_append_cons_of_forall_mem h₁ sep hsep]
  rw [List.splitOnP_append_cons_of_forall_mem h₂ sep hsep]
  rw [List.splitOnP_append_cons_of_forall_mem h₃ sep hsep]
  rw [List.splitOnP_eq_singleton h₄]
  simp

private theorem eq_intercalate_of_splitToList_eq {s : String} {parts : List String}
    (sep : Char) (h : s.splitToList (fun c => decide (c = sep)) = parts) :
    s = String.intercalate (String.singleton sep) parts := by
  rw [String.splitToList_of_valid] at h
  have hp : (fun c : Char => decide (c = sep)) = (fun c => c == sep) := by
    funext c
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, beq_iff_eq]
  have hsplits : List.splitOn sep s.toList = parts.map String.toList := by
    rw [List.splitOn_eq_splitOnP]
    have h' := congrArg (List.map String.toList) h
    simpa [Function.comp_def, hp] using h'
  have hi := congrArg (List.intercalate [sep]) hsplits
  rw [List.intercalate_splitOn] at hi
  rw [← String.toList_inj]
  simpa [String.toList_intercalate] using hi

private theorem noSlashV4 (v : V4Components) (hsyn : v.syntaxWf) :
    ∀ c ∈ v.asString.toList, (fun x : Char => decide (x = '/')) c = false := by
  simpa [V4Components.asString, String.append_assoc] using
    noSepAppend (noSlashOfCanonical hsyn.1.1)
      (noSepAppend noSlashDot
        (noSepAppend (noSlashOfCanonical hsyn.2.1.1)
          (noSepAppend noSlashDot
            (noSepAppend (noSlashOfCanonical hsyn.2.2.1.1)
              (noSepAppend noSlashDot (noSlashOfCanonical hsyn.2.2.2.1))))))

/-- `parseSegsV4` inverts `V4Components.asString` on well-formed, in-range V4 groups. -/
theorem parseSegsV4_asString {v : V4Components} (hsyn : v.syntaxWf) (hcon : v.constraintsWf) :
    parseSegsV4 v.asString = some v.toAddr :=
  by
  have hsplit :
      v.asString.splitToList (· = '.') = [v.g₀, v.g₁, v.g₂, v.g₃] := by
    simpa [V4Components.asString, String.append_assoc] using
      splitToList_eq4 v.g₀ v.g₁ v.g₂ v.g₃ (fun x : Char => decide (x = '.')) '.'
        (by simp) (noDotOfCanonical hsyn.1.1) (noDotOfCanonical hsyn.2.1.1)
        (noDotOfCanonical hsyn.2.2.1.1) (noDotOfCanonical hsyn.2.2.2.1)
  unfold parseSegsV4
  rw [hsplit]
  simp only
  rw [parseNumV4_eq_some hsyn.1 hcon.1]
  rw [parseNumV4_eq_some hsyn.2.1 hcon.2.1]
  rw [parseNumV4_eq_some hsyn.2.2.1 hcon.2.2.1]
  rw [parseNumV4_eq_some hsyn.2.2.2 hcon.2.2.2]
  simp [V4Components.toAddr]

private theorem parseSegsV4_some_wf {str : String} {addr : IPv4Addr}
    (h : parseSegsV4 str = some addr) :
    ∃ v : V4Components,
      str = v.asString ∧ v.syntaxWf ∧ v.constraintsWf ∧ addr = v.toAddr := by
  unfold parseSegsV4 at h
  generalize hsplits : str.splitToList (· = '.') = parts at h
  rcases parts with _ | ⟨g₀, parts⟩
  · simp at h
  rcases parts with _ | ⟨g₁, parts⟩
  · simp at h
  rcases parts with _ | ⟨g₂, parts⟩
  · simp at h
  rcases parts with _ | ⟨g₃, parts⟩
  · simp at h
  rcases parts with _ | ⟨extra, parts⟩
  ·
    cases h₀ : parseNumV4 g₀ with
    | none => simp [h₀] at h
    | some a₀ =>
      cases h₁ : parseNumV4 g₁ with
      | none => simp [h₀, h₁] at h
      | some a₁ =>
        cases h₂ : parseNumV4 g₂ with
        | none => simp [h₀, h₁, h₂] at h
        | some a₂ =>
          cases h₃ : parseNumV4 g₃ with
          | none => simp [h₀, h₁, h₂, h₃] at h
          | some a₃ =>
            simp [h₀, h₁, h₂, h₃] at h
            have hisSome₀ : (parseNumV4 g₀).isSome := by rw [h₀]; simp
            have hisSome₁ : (parseNumV4 g₁).isSome := by rw [h₁]; simp
            have hisSome₂ : (parseNumV4 g₂).isSome := by rw [h₂]; simp
            have hisSome₃ : (parseNumV4 g₃).isSome := by rw [h₃]; simp
            have hwf₀ := parseNumV4_isSome_wf hisSome₀
            have hwf₁ := parseNumV4_isSome_wf hisSome₁
            have hwf₂ := parseNumV4_isSome_wf hisSome₂
            have hwf₃ := parseNumV4_isSome_wf hisSome₃
            have ha₀ := parseNumV4_eq_some hwf₀.1 hwf₀.2
            have ha₁ := parseNumV4_eq_some hwf₁.1 hwf₁.2
            have ha₂ := parseNumV4_eq_some hwf₂.1 hwf₂.2
            have ha₃ := parseNumV4_eq_some hwf₃.1 hwf₃.2
            rw [h₀] at ha₀
            rw [h₁] at ha₁
            rw [h₂] at ha₂
            rw [h₃] at ha₃
            injection ha₀ with ha₀
            injection ha₁ with ha₁
            injection ha₂ with ha₂
            injection ha₃ with ha₃
            subst a₀
            subst a₁
            subst a₂
            subst a₃
            refine ⟨⟨g₀, g₁, g₂, g₃⟩, ?_, ?_, ?_, ?_⟩
            · have hs := eq_intercalate_of_splitToList_eq '.' hsplits
              simpa [V4Components.asString, String.append_assoc] using hs
            · exact ⟨hwf₀.1, hwf₁.1, hwf₂.1, hwf₃.1⟩
            · exact ⟨hwf₀.2, hwf₁.2, hwf₂.2, hwf₃.2⟩
            · simpa [V4Components.toAddr] using h.symm
  · simp at h

/-- `parseIPv4Net` succeeds on a well-formed V4 string, yielding `v4Value`. -/
theorem parseIPv4Net_eq_some {v : V4Components} {pre : Option String}
    (hsyn : v.syntaxWf) (hcon : v.constraintsWf)
    (hpre : IsWfOptionalPrefix 2 (ADDR_SIZE V4_WIDTH) pre) :
    parseIPv4Net (v.asString ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v4Value v pre) :=
  by
  unfold parseIPv4Net
  cases pre with
  | none =>
      have hsplit : v.asString.splitToList (· = '/') = [v.asString] :=
        splitToList_no_sep v.asString (fun x : Char => decide (x = '/')) (noSlashV4 v hsyn)
      simp only [String.append_empty]
      rw [hsplit]
      simp only
      rw [parseSegsV4_asString hsyn hcon]
      simp [v4Value, prefixValue, IPNetPrefix.ofNat]
  | some p =>
      have hsplit :
          (v.asString ++ ("/" ++ p)).splitToList (· = '/') = [v.asString, p] := by
        simpa [String.append_assoc] using
          splitToList_eq v.asString p (fun x : Char => decide (x = '/')) '/'
            (by simp) (noSlashV4 v hsyn) (noSlashOfCanonical hpre.1)
      simp only
      rw [hsplit]
      simp only
      rw [parsePrefixNat_eq_value hpre, parseSegsV4_asString hsyn hcon]
      change IsCanonicalNat p ∧ p.length ≤ 2 ∧ numValue p ≤ ADDR_SIZE V4_WIDTH at hpre
      have hlt : numValue p < ADDR_SIZE V4_WIDTH + 1 := by omega
      simp [v4Value, prefixValue, IPNetPrefix.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hlt]

/-- Soundness for V4: a successful `parseIPv4Net` means the string is a well-formed V4 rendering
    whose value is the returned net. -/
theorem parseIPv4Net_isSome_wf {str : String} {net : IPNet} (h : parseIPv4Net str = some net) :
    IsWfV4 str ∧ ∃ v pre, net = v4Value v pre :=
  by
  unfold parseIPv4Net at h
  generalize hsplits : str.splitToList (· = '/') = parts at h
  rcases parts with _ | ⟨addrStr, rest⟩
  · simp at h
  rcases rest with _ | ⟨preStr, rest⟩
  ·
    cases ha : parseSegsV4 addrStr with
    | none => simp [ha] at h
    | some addr =>
      simp [ha] at h
      obtain ⟨v, haddrStr, hsyn, hcon, haddr⟩ := parseSegsV4_some_wf ha
      have hstr := eq_intercalate_of_splitToList_eq '/' hsplits
      rw [String.intercalate_singleton] at hstr
      rw [haddrStr] at hstr
      refine ⟨?_, v, none, ?_⟩
      · exact ⟨v, none, hsyn, hcon, trivial, by simpa using hstr⟩
      · subst addr
        simpa [v4Value, prefixValue, IPNetPrefix.ofNat] using h.symm
  rcases rest with _ | ⟨extra, rest⟩
  ·
    cases hp : parsePrefixNat preStr 2 (ADDR_SIZE V4_WIDTH) with
    | none => simp [hp] at h
    | some pre =>
      cases ha : parseSegsV4 addrStr with
      | none => simp [hp, ha] at h
      | some addr =>
        simp [hp, ha] at h
        obtain ⟨v, haddrStr, hsyn, hcon, haddr⟩ := parseSegsV4_some_wf ha
        obtain ⟨hpre, hpreValue⟩ := parsePrefixNat_some_wf hp
        have hstr := eq_intercalate_of_splitToList_eq '/' hsplits
        rw [String.intercalate_cons_cons, String.intercalate_singleton] at hstr
        rw [haddrStr] at hstr
        refine ⟨?_, v, some preStr, ?_⟩
        · exact ⟨v, some preStr, hsyn, hcon, hpre, by
            simpa [String.append_assoc] using hstr⟩
        · subst addr
          simpa [v4Value, prefixValue, hpreValue] using h.symm
  · simp at h

/-! ## IPv6 form -/

private def groupValues (parts : List String) : List (BitVec 16) :=
  parts.map (fun part => BitVec.ofNat 16 (hexValue part))

private theorem hexValue_zero : hexValue "0" = 0 := by
  unfold hexValue
  simp [String.foldl_eq_foldl_toList, toHexNat]

private def finishV6 (groups : List (BitVec 16)) : Option IPv6Addr :=
  match groups with
  | [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇] =>
      some (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇)
  | _ => none

private theorem finishV6_length_of_some {groups : List (BitVec 16)} {addr : IPv6Addr}
    (h : finishV6 groups = some addr) :
    groups.length = 8 := by
  unfold finishV6 at h
  rcases groups with _ | ⟨a₀, groups⟩
  · simp at h
  rcases groups with _ | ⟨a₁, groups⟩
  · simp at h
  rcases groups with _ | ⟨a₂, groups⟩
  · simp at h
  rcases groups with _ | ⟨a₃, groups⟩
  · simp at h
  rcases groups with _ | ⟨a₄, groups⟩
  · simp at h
  rcases groups with _ | ⟨a₅, groups⟩
  · simp at h
  rcases groups with _ | ⟨a₆, groups⟩
  · simp at h
  rcases groups with _ | ⟨a₇, groups⟩
  · simp at h
  rcases groups with _ | ⟨extra, groups⟩
  · rfl
  · simp at h

private theorem finishV6_groupValues_eq_toAddr {v : V6Components}
    (hlen : v.expand.length = 8) :
    finishV6 (groupValues v.expand) = some v.toAddr := by
  unfold V6Components.toAddr
  generalize hexpand : v.expand = groups at hlen ⊢
  rcases groups with _ | ⟨g₀, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨g₁, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨g₂, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨g₃, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨g₄, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨g₅, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨g₆, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨g₇, groups⟩
  · simp at hlen
  rcases groups with _ | ⟨extra, groups⟩
  · simp [finishV6, groupValues]
  · simp at hlen

private theorem noColonOfHex {s : String} (h : IsHexGroup s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = ':')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hm := h.2.2 ':' hc
  simp [isHexDigit] at hm

private theorem neColonOfHex {s : String} (h : IsHexGroup s) :
    ∀ c ∈ s.toList, c ≠ ':' := by
  intro c hc heq
  subst c
  have hm := h.2.2 ':' hc
  simp [isHexDigit] at hm

private theorem noSlashOfHex {s : String} (h : IsHexGroup s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '/')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hm := h.2.2 '/' hc
  simp [isHexDigit] at hm

private theorem noDotOfHex {s : String} (h : IsHexGroup s) :
    ∀ c ∈ s.toList, (fun x : Char => decide (x = '.')) c = false := by
  intro c hc
  simp only [decide_eq_false_iff_not]
  intro heq
  subst c
  have hm := h.2.2 '.' hc
  simp [isHexDigit] at hm

private theorem List.splitOnP_intercalate (parts : List (List α)) (hne : parts ≠ [])
    (p : α → Bool) (sep : α) (hsep : p sep = true)
    (hparts : ∀ part ∈ parts, ∀ x ∈ part, p x = false) :
    List.splitOnP p ([sep].intercalate parts) = parts := by
  induction parts with
  | nil => exact (hne rfl).elim
  | cons part rest ih =>
      cases rest with
      | nil =>
          rw [List.intercalate_singleton]
          exact List.splitOnP_eq_singleton (hparts part (by simp))
      | cons next tail =>
          rw [List.intercalate_cons_cons, List.append_assoc, List.singleton_append,
            List.splitOnP_append_cons_of_forall_mem (hparts part (by simp)) sep hsep]
          congr 1
          apply ih
          · simp
          · intro item hitem x hx
            exact hparts item (by simp [hitem]) x hx

private theorem splitToList_intercalate (parts : List String) (hne : parts ≠ [])
    (p : Char → Bool) (sep : Char) (hsep : p sep = true)
    (hparts : ∀ part ∈ parts, ∀ c ∈ part.toList, p c = false) :
    (String.intercalate (String.singleton sep) parts).splitToList p = parts := by
  rw [String.splitToList_of_valid, String.toList_intercalate, String.toList_singleton]
  rw [List.splitOnP_intercalate (parts.map String.toList) (by simpa using hne)
    p sep hsep]
  · simp
  · intro chars hchars c hc
    rw [List.mem_map] at hchars
    obtain ⟨part, hpart, rfl⟩ := hchars
    exact hparts part hpart c hc

private theorem mapM_parseNumV6_eq_some {parts : List String}
    (hall : ∀ part ∈ parts, IsHexGroup part) :
    parts.mapM parseNumV6 = some (groupValues parts) := by
  induction parts with
  | nil => simp [groupValues]
  | cons part parts ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hall
      simp [groupValues, parseNumV6_eq_some hall.1, ih hall.2]

private theorem mapM_parseNumV6_some_wf {parts : List String} {values : List (BitVec 16)}
    (h : parts.mapM parseNumV6 = some values) :
    (∀ part ∈ parts, IsHexGroup part) ∧ values = groupValues parts := by
  induction parts generalizing values with
  | nil =>
      simp at h
      subst values
      simp [groupValues]
  | cons part parts ih =>
      cases hp : parseNumV6 part with
      | none => simp [hp] at h
      | some value =>
        cases ht : parts.mapM parseNumV6 with
        | none => simp [hp, ht] at h
        | some values' =>
          simp [hp, ht] at h
          subst values
          have hpart : IsHexGroup part := parseNumV6_isSome_wf (by rw [hp]; simp)
          obtain ⟨hparts, hvalues⟩ := ih ht
          have hvalue := parseNumV6_eq_some hpart
          rw [hp] at hvalue
          injection hvalue with hvalue
          subst value
          refine ⟨?_, by simp [groupValues, hvalues]⟩
          intro item hitem
          simp only [List.mem_cons] at hitem
          rcases hitem with rfl | hitem
          · exact hpart
          · exact hparts item hitem

private theorem parseNumSegsV6_eq_some {parts : List String}
    (hall : ∀ part ∈ parts, IsHexGroup part) :
    parseNumSegsV6 (String.intercalate ":" parts) = some (groupValues parts) := by
  cases parts with
  | nil => simp [parseNumSegsV6, groupValues]
  | cons part parts =>
      have hsplit :
          (String.intercalate ":" (part :: parts)).splitToList (· = ':') =
            part :: parts := by
        exact splitToList_intercalate (part :: parts) (by simp)
          (fun x : Char => decide (x = ':')) ':' (by simp)
          (fun item hitem => noColonOfHex (hall item hitem))
      have hpartNonempty : part ≠ "" := by
        intro heq
        have hlen := (hall part (by simp)).1
        simp [heq] at hlen
      have hnonempty : String.intercalate ":" (part :: parts) ≠ "" := by
        cases parts <;> simp [hpartNonempty]
      unfold parseNumSegsV6
      rw [if_neg (by simpa [String.isEmpty_iff] using hnonempty), hsplit]
      exact mapM_parseNumV6_eq_some hall

private theorem parseNumSegsV6_some_wf {str : String} {values : List (BitVec 16)}
    (h : parseNumSegsV6 str = some values) :
    ∃ parts,
      str = String.intercalate ":" parts ∧
      (∀ part ∈ parts, IsHexGroup part) ∧
      values = groupValues parts := by
  unfold parseNumSegsV6 at h
  split at h <;> rename_i hempty
  · have hstr : str = "" := String.isEmpty_iff.mp hempty
    simp only [Option.some.injEq] at h
    subst str
    subst values
    exact ⟨[], by simp, by simp, rfl⟩
  · generalize hsplits : str.splitToList (· = ':') = parts at h
    obtain ⟨hall, hvalues⟩ := mapM_parseNumV6_some_wf h
    refine ⟨parts, ?_, hall, hvalues⟩
    exact eq_intercalate_of_splitToList_eq ':' hsplits

/-! ## Specialized model of `String.splitOn "::"` -/

/-- A character-list model of splitting on `"::"`, used only in the proof layer. -/
private def splitDoubleColonModelAux : List Char → List Char → List String
  | current, ':' :: ':' :: rest =>
      String.ofList current :: splitDoubleColonModelAux [] rest
  | current, c :: rest =>
      splitDoubleColonModelAux (current ++ [c]) rest
  | current, [] =>
      [String.ofList current]

/-- The proof-layer model of `String.splitOn "::"`. -/
public def splitDoubleColonModel (str : String) : List String :=
  splitDoubleColonModelAux [] str.toList

/--
The two reachable separator-cursor states of `String.splitOnAux` for the fixed separator `"::"`.
When `pending` is true, the scanner has matched the first colon and is waiting for the second.
-/
private def splitDoubleColonScan : Bool → List Char → List Char → List String
  | false, current, [] => [String.ofList current]
  | false, current, c :: rest =>
      if c = ':' then
        splitDoubleColonScan true current rest
      else
        splitDoubleColonScan false (current ++ [c]) rest
  | true, current, [] => [String.ofList (current ++ [':'])]
  | true, current, c :: rest =>
      if c = ':' then
        String.ofList current :: splitDoubleColonScan false [] rest
      else
        splitDoubleColonScan false (current ++ [':']) (c :: rest)
termination_by pending _ remaining =>
  remaining.length * 2 + if pending then 1 else 0

private def splitDoubleColonModelState
    (pending : Bool) (current remaining : List Char) : List String :=
  if pending then
    splitDoubleColonModelAux current (':' :: remaining)
  else
    splitDoubleColonModelAux current remaining

private theorem splitDoubleColonScan_eq_model (pending current remaining) :
    splitDoubleColonScan pending current remaining =
      splitDoubleColonModelState pending current remaining := by
  induction pending, current, remaining using splitDoubleColonScan.induct <;>
    simp [splitDoubleColonScan, splitDoubleColonModelState, splitDoubleColonModelAux, *,
      List.append_assoc]

private def splitDoubleColonScannedChars
    (pending : Bool) (pre current : List Char) : List Char :=
  pre ++ current ++ if pending then [':'] else []

private def splitDoubleColonSepPos (pending : Bool) : String.Pos.Raw :=
  if pending then ⟨1⟩ else 0

private theorem splitOnAux_doubleColon_eq_scan :
    ∀ pending current remaining pre acc,
      String.splitOnAux
          (String.ofList
            (splitDoubleColonScannedChars pending pre current ++ remaining))
          "::"
          ⟨String.utf8Len pre⟩
          ⟨String.utf8Len (splitDoubleColonScannedChars pending pre current)⟩
          (splitDoubleColonSepPos pending)
          acc =
        acc.reverse ++ splitDoubleColonScan pending current remaining := by
  intro pending current remaining
  induction pending, current, remaining using splitDoubleColonScan.induct <;>
    intro pre acc
  case case1 current =>
    simp only [splitDoubleColonScannedChars, splitDoubleColonSepPos, Bool.false_eq_true,
      ↓reduceIte, List.append_nil, splitDoubleColonScan]
    rw [String.splitOnAux]
    rw [if_pos]
    · rw [String.utf8Len_append]
      have hextract :
          String.Pos.Raw.extract (String.ofList (pre ++ current))
            ⟨String.utf8Len pre⟩
            ⟨String.utf8Len pre + String.utf8Len current⟩ =
              String.ofList current := by
        simpa using String.extract_of_valid pre current []
      rw [hextract]
      simp
    · simpa using (String.atEnd_of_valid (pre ++ current) []).2 rfl
  case case2 current rest ih =>
    simp only [splitDoubleColonScannedChars, splitDoubleColonSepPos, Bool.false_eq_true,
      ↓reduceIte, List.append_nil, splitDoubleColonScan]
    have hnot :
        ¬String.Pos.Raw.atEnd (String.ofList ((pre ++ current) ++ ':' :: rest))
          ⟨String.utf8Len (pre ++ current)⟩ := by
      simpa using
        (not_congr (String.atEnd_of_valid (pre ++ current) (':' :: rest))).2 (by simp)
    rw [String.splitOnAux, if_neg hnot]
    rw [show
      String.Pos.Raw.get (String.ofList ((pre ++ current) ++ ':' :: rest))
          ⟨String.utf8Len (pre ++ current)⟩ = ':' by
        simpa using String.get_of_valid (pre ++ current) (':' :: rest)]
    rw [show String.Pos.Raw.get "::" 0 = ':' by rfl]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [show
      String.Pos.Raw.next (String.ofList ((pre ++ current) ++ ':' :: rest))
          ⟨String.utf8Len (pre ++ current)⟩ =
            ⟨String.utf8Len (pre ++ current) + ':'.utf8Size⟩ by
        simpa using String.next_of_valid (pre ++ current) ':' rest]
    rw [show String.Pos.Raw.next "::" 0 = ⟨1⟩ by rfl]
    rw [if_neg (show ¬String.Pos.Raw.atEnd "::" ⟨1⟩ by decide)]
    simpa [splitDoubleColonScannedChars, splitDoubleColonSepPos, String.utf8Len_append,
      List.append_assoc, Nat.add_assoc] using ih pre acc
  case case3 current c rest hc ih =>
    simp only [splitDoubleColonScannedChars, splitDoubleColonSepPos, Bool.false_eq_true,
      ↓reduceIte, List.append_nil, splitDoubleColonScan, if_neg hc]
    have hnot :
        ¬String.Pos.Raw.atEnd (String.ofList ((pre ++ current) ++ c :: rest))
          ⟨String.utf8Len (pre ++ current)⟩ := by
      simpa using
        (not_congr (String.atEnd_of_valid (pre ++ current) (c :: rest))).2 (by simp)
    rw [String.splitOnAux, if_neg hnot]
    rw [show
      String.Pos.Raw.get (String.ofList ((pre ++ current) ++ c :: rest))
          ⟨String.utf8Len (pre ++ current)⟩ = c by
        simpa using String.get_of_valid (pre ++ current) (c :: rest)]
    rw [show String.Pos.Raw.get "::" 0 = ':' by rfl]
    rw [if_neg (by simpa using hc)]
    simp only [String.Pos.Raw.unoffsetBy_zero]
    rw [show
      String.Pos.Raw.next (String.ofList ((pre ++ current) ++ c :: rest))
          ⟨String.utf8Len (pre ++ current)⟩ =
            ⟨String.utf8Len (pre ++ current) + c.utf8Size⟩ by
        simpa using String.next_of_valid (pre ++ current) c rest]
    simpa [splitDoubleColonScannedChars, splitDoubleColonSepPos, String.utf8Len_append,
      List.append_assoc, Nat.add_assoc] using ih pre acc
  case case4 current =>
    simp only [splitDoubleColonScannedChars, splitDoubleColonSepPos, ↓reduceIte,
      List.append_nil, splitDoubleColonScan]
    rw [String.splitOnAux]
    rw [if_pos]
    · simp only [String.utf8Len_append]
      have hextract :
          String.Pos.Raw.extract (String.ofList (pre ++ current ++ [':']))
            ⟨String.utf8Len pre⟩
            ⟨String.utf8Len pre + String.utf8Len current + String.utf8Len [':']⟩ =
              String.ofList (current ++ [':']) := by
        simpa [List.append_assoc, String.utf8Len_append, Nat.add_assoc] using
          String.extract_of_valid pre (current ++ [':']) []
      rw [hextract]
      simp
    · simpa [List.append_assoc] using
        (String.atEnd_of_valid (pre ++ current ++ [':']) []).2 rfl
  case case5 current rest ih =>
    simp only [splitDoubleColonScannedChars, splitDoubleColonSepPos, ↓reduceIte,
      splitDoubleColonScan]
    have hnot :
        ¬String.Pos.Raw.atEnd
          (String.ofList ((pre ++ current ++ [':']) ++ ':' :: rest))
          ⟨String.utf8Len (pre ++ current ++ [':'])⟩ := by
      simpa using
        (not_congr
          (String.atEnd_of_valid (pre ++ current ++ [':']) (':' :: rest))).2
          (by simp)
    rw [String.splitOnAux, if_neg hnot]
    rw [show
      String.Pos.Raw.get
          (String.ofList ((pre ++ current ++ [':']) ++ ':' :: rest))
          ⟨String.utf8Len (pre ++ current ++ [':'])⟩ = ':' by
        simpa using String.get_of_valid (pre ++ current ++ [':']) (':' :: rest)]
    rw [show String.Pos.Raw.get "::" ⟨1⟩ = ':' by rfl]
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [show
      String.Pos.Raw.next
          (String.ofList ((pre ++ current ++ [':']) ++ ':' :: rest))
          ⟨String.utf8Len (pre ++ current ++ [':'])⟩ =
            ⟨String.utf8Len (pre ++ current ++ [':']) + ':'.utf8Size⟩ by
        simpa using String.next_of_valid (pre ++ current ++ [':']) ':' rest]
    rw [show String.Pos.Raw.next "::" ⟨1⟩ = ⟨2⟩ by rfl]
    rw [if_pos (show String.Pos.Raw.atEnd "::" ⟨2⟩ by decide)]
    have hunoffset :
        (⟨String.utf8Len (pre ++ current ++ [':']) + ':'.utf8Size⟩ :
          String.Pos.Raw).unoffsetBy ⟨2⟩ =
            ⟨String.utf8Len (pre ++ current)⟩ := by
      ext
      simp [String.utf8Len_append, String.utf8Len_cons, Char.utf8Size]
    rw [hunoffset]
    have hextract :
        String.Pos.Raw.extract
          (String.ofList ((pre ++ current ++ [':']) ++ ':' :: rest))
          ⟨String.utf8Len pre⟩
          ⟨String.utf8Len (pre ++ current)⟩ =
            String.ofList current := by
      simpa [List.append_assoc] using
        String.extract_of_valid pre current ([':', ':'] ++ rest)
    rw [hextract]
    simpa [splitDoubleColonScannedChars, splitDoubleColonSepPos, String.utf8Len_append,
      List.append_assoc, Nat.add_assoc] using
        ih (pre ++ current ++ [':', ':']) (String.ofList current :: acc)
  case case6 current c rest hc ih =>
    simp only [splitDoubleColonScannedChars, splitDoubleColonSepPos, ↓reduceIte,
      splitDoubleColonScan, if_neg hc]
    have hnot :
        ¬String.Pos.Raw.atEnd
          (String.ofList ((pre ++ current ++ [':']) ++ c :: rest))
          ⟨String.utf8Len (pre ++ current ++ [':'])⟩ := by
      simpa using
        (not_congr
          (String.atEnd_of_valid (pre ++ current ++ [':']) (c :: rest))).2
          (by simp)
    rw [String.splitOnAux, if_neg hnot]
    rw [show
      String.Pos.Raw.get
          (String.ofList ((pre ++ current ++ [':']) ++ c :: rest))
          ⟨String.utf8Len (pre ++ current ++ [':'])⟩ = c by
        simpa using String.get_of_valid (pre ++ current ++ [':']) (c :: rest)]
    rw [show String.Pos.Raw.get "::" ⟨1⟩ = ':' by rfl]
    rw [if_neg (by simpa using hc)]
    have hunoffset :
        (⟨String.utf8Len (pre ++ current ++ [':'])⟩ :
          String.Pos.Raw).unoffsetBy ⟨1⟩ =
            ⟨String.utf8Len (pre ++ current)⟩ := by
      ext
      simp [String.utf8Len_append, String.utf8Len_cons, Char.utf8Size]
    rw [hunoffset]
    rw [show
      String.Pos.Raw.next
          (String.ofList ((pre ++ current ++ [':']) ++ c :: rest))
          ⟨String.utf8Len (pre ++ current)⟩ =
            ⟨String.utf8Len (pre ++ current) + ':'.utf8Size⟩ by
        have h := String.next_of_valid (pre ++ current) ':' (c :: rest)
        simpa [List.append_assoc] using h]
    simpa [splitDoubleColonScan, if_neg hc, splitDoubleColonScannedChars,
      splitDoubleColonSepPos, String.utf8Len_append, List.append_assoc, Nat.add_assoc] using
        ih pre acc

/-- `String.splitOn "::"` agrees with the proof-layer character-list model on every string. -/
public theorem splitOn_doubleColon_eq (s : String) :
    s.splitOn "::" = splitDoubleColonModel s := by
  unfold String.splitOn
  rw [if_neg (by decide)]
  have h := splitOnAux_doubleColon_eq_scan false [] s.toList [] []
  simpa [splitDoubleColonScannedChars, splitDoubleColonSepPos,
    splitDoubleColonScan_eq_model, splitDoubleColonModelState, splitDoubleColonModel] using h

private theorem renderGroups_cons_toList (part : String) (parts : List String) :
    (String.intercalate ":" (part :: parts)).toList =
      part.toList ++
        match parts with
        | [] => []
        | _ => ':' :: (String.intercalate ":" parts).toList := by
  cases parts <;> simp [String.toList_append]

private theorem splitDoubleColonModelAux_consume_noColon
    (current chars rest : List Char)
    (h : ∀ c ∈ chars, c ≠ ':') :
    splitDoubleColonModelAux current (chars ++ rest) =
      splitDoubleColonModelAux (current ++ chars) rest := by
  induction chars generalizing current with
  | nil => simp
  | cons c cs ih =>
      have hc : c ≠ ':' := h c (by simp)
      have hnonmatch :
          ∀ suffix, c = ':' → cs ++ rest = ':' :: suffix → False := by
        intro suffix heq _
        exact hc heq
      rw [List.cons_append, splitDoubleColonModelAux.eq_2 current c (cs ++ rest) hnonmatch]
      simpa only [List.append_assoc, List.singleton_append] using
        ih (current ++ [c]) (fun d hd => h d (by simp [hd]))

private theorem splitDoubleColonModelAux_consume_renderGroups
    (current suffix : List Char) (parts : List String)
    (hall : ∀ part ∈ parts, IsHexGroup part) :
    splitDoubleColonModelAux current ((String.intercalate ":" parts).toList ++ suffix) =
      splitDoubleColonModelAux (current ++ (String.intercalate ":" parts).toList) suffix := by
  induction parts generalizing current with
  | nil => simp
  | cons part parts ih =>
      cases parts with
      | nil =>
          simpa using splitDoubleColonModelAux_consume_noColon current part.toList suffix
            (neColonOfHex (hall part (by simp)))
      | cons next tail =>
          have hpart := hall part (by simp)
          have hnext := hall next (by simp)
          have htail : ∀ item ∈ next :: tail, IsHexGroup item := by
            intro item hitem
            exact hall item (by simp [hitem])
          have hnextList : next.toList ≠ [] := by
            intro heq
            have hlen := hnext.1
            rw [← String.length_toList, heq] at hlen
            simp at hlen
          obtain ⟨c, cs, hcList⟩ := List.exists_cons_of_ne_nil hnextList
          have hc : c ≠ ':' := neColonOfHex hnext c (by simp [hcList])
          obtain ⟨tailChars, hrenderTail⟩ :
              ∃ tailChars, (String.intercalate ":" (next :: tail)).toList =
                c :: tailChars := by
            rw [renderGroups_cons_toList, hcList]
            exact ⟨_, rfl⟩
          have hnonmatch :
              ∀ rest, ':' = ':' →
                (String.intercalate ":" (next :: tail)).toList ++ suffix =
                  ':' :: rest → False := by
            intro rest _ heq
            rw [hrenderTail] at heq
            injection heq with heq
            exact hc heq
          rw [renderGroups_cons_toList]
          simp only [List.cons_append, List.append_assoc]
          rw [splitDoubleColonModelAux_consume_noColon current part.toList
            (':' :: ((String.intercalate ":" (next :: tail)).toList ++ suffix))
            (neColonOfHex hpart)]
          rw [splitDoubleColonModelAux.eq_2 (current ++ part.toList) ':'
            ((String.intercalate ":" (next :: tail)).toList ++ suffix) hnonmatch]
          have hrec := ih ((current ++ part.toList) ++ [':']) htail
          rw [hrec]
          congr 1
          simp only [List.append_assoc, List.singleton_append]

private theorem ofList_intercalate_toList (sep : String) (parts : List String) :
    String.ofList (sep.toList.intercalate (parts.map String.toList)) =
      String.intercalate sep parts := by
  apply String.toList_inj.mp
  simp

private theorem splitDoubleColonModel_renderGroups (parts : List String)
    (hall : ∀ part ∈ parts, IsHexGroup part) :
    splitDoubleColonModel (String.intercalate ":" parts) =
      [String.intercalate ":" parts] := by
  unfold splitDoubleColonModel
  have h := splitDoubleColonModelAux_consume_renderGroups [] [] parts hall
  simp [splitDoubleColonModelAux] at h
  rw [String.toList_intercalate]
  rw [← ofList_intercalate_toList ":" parts]
  exact h

private theorem splitDoubleColonModel_renderGroups_gap (left right : List String)
    (hleft : ∀ part ∈ left, IsHexGroup part)
    (hright : ∀ part ∈ right, IsHexGroup part) :
    splitDoubleColonModel (String.intercalate ":" left ++ "::" ++
      String.intercalate ":" right) =
      [String.intercalate ":" left, String.intercalate ":" right] := by
  unfold splitDoubleColonModel
  simp only [String.toList_append]
  rw [show "::".toList = [':', ':'] by rfl]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rw [splitDoubleColonModelAux_consume_renderGroups []
    (':' :: ':' :: (String.intercalate ":" right).toList) left hleft]
  rw [splitDoubleColonModelAux.eq_1]
  have hrightAux := splitDoubleColonModelAux_consume_renderGroups [] [] right hright
  simp [splitDoubleColonModelAux] at hrightAux
  have hrightChars :
      [':'].intercalate (right.map String.toList) =
        (String.intercalate ":" right).toList := by simp
  rw [hrightChars] at hrightAux
  simp only [String.ofList_toList] at hrightAux
  simp only [List.nil_append, String.ofList_toList]
  rw [hrightAux]

private theorem splitDoubleColonModelAux_ne_nil (current remaining : List Char) :
    splitDoubleColonModelAux current remaining ≠ [] := by
  induction current, remaining using splitDoubleColonModelAux.induct with
  | case1 current rest ih => simp [splitDoubleColonModelAux]
  | case2 current c rest hnomatch ih =>
      rw [splitDoubleColonModelAux.eq_2 current c rest hnomatch]
      exact ih
  | case3 current => simp [splitDoubleColonModelAux]

private theorem intercalate_splitDoubleColonModelAux (current remaining : List Char) :
    String.intercalate "::" (splitDoubleColonModelAux current remaining) =
      String.ofList current ++ String.ofList remaining := by
  induction current, remaining using splitDoubleColonModelAux.induct with
  | case1 current rest ih =>
      rw [splitDoubleColonModelAux.eq_1]
      have hne : splitDoubleColonModelAux [] rest ≠ [] :=
        splitDoubleColonModelAux_ne_nil [] rest
      obtain ⟨part, parts, hparts⟩ := List.exists_cons_of_ne_nil hne
      rw [hparts, String.intercalate_cons_cons]
      rw [hparts] at ih
      rw [ih]
      change
        String.ofList current ++ "::" ++ String.ofList rest =
          String.ofList current ++ String.ofList (':' :: ':' :: rest)
      have hcolon :
          String.ofList (':' :: ':' :: rest) = "::" ++ String.ofList rest := by
        apply String.toList_inj.mp
        simp
      rw [hcolon]
      simp only [String.append_assoc]
  | case2 current c rest hnomatch ih =>
      rw [splitDoubleColonModelAux.eq_2 current c rest hnomatch]
      simpa only [← String.ofList_append, List.append_assoc, List.singleton_append] using ih
  | case3 current =>
      simp [splitDoubleColonModelAux]

private theorem eq_intercalate_of_splitDoubleColonModel_eq {str : String} {parts : List String}
    (h : splitDoubleColonModel str = parts) :
    str = String.intercalate "::" parts := by
  unfold splitDoubleColonModel at h
  rw [← h, intercalate_splitDoubleColonModelAux]
  simp

/-- `parseSegsV6` inverts `V6Components.asString` on a syntactically well-formed V6 address:
    `full gs` (no `::`) splits to exactly 8 hextets; `gap l r` splits on `::` into two sides that
    `parseSegsV6` pads to 8. -/
theorem parseSegsV6_asString {v : V6Components} (hsyn : v.syntaxWf) :
    parseSegsV6 v.asString = some v.toAddr :=
  by
  cases v with
  | full parts =>
      obtain ⟨hlen, hall⟩ := hsyn
      have hsplit :
          splitDoubleColonModel (V6Components.asString (.full parts)) =
            [String.intercalate ":" parts] := by
        simpa [V6Components.asString] using splitDoubleColonModel_renderGroups parts hall
      have hparse :
          parseNumSegsV6 (String.intercalate ":" parts) =
            some (groupValues parts) :=
        parseNumSegsV6_eq_some hall
      unfold parseSegsV6
      rw [splitOn_doubleColon_eq, hsplit]
      simp only
      rw [hparse]
      change finishV6 (groupValues parts) =
        some (V6Components.toAddr (.full parts))
      apply finishV6_groupValues_eq_toAddr (v := .full parts)
      simpa [V6Components.expand] using hlen
  | gap left right =>
      obtain ⟨hcount, hleft, hright⟩ := hsyn
      have hsplit :
          splitDoubleColonModel (V6Components.asString (.gap left right)) =
            [String.intercalate ":" left, String.intercalate ":" right] := by
        simpa [V6Components.asString] using
          splitDoubleColonModel_renderGroups_gap left right hleft hright
      have hleftParse :
          parseNumSegsV6 (String.intercalate ":" left) =
            some (groupValues left) :=
        parseNumSegsV6_eq_some hleft
      have hrightParse :
          parseNumSegsV6 (String.intercalate ":" right) =
            some (groupValues right) :=
        parseNumSegsV6_eq_some hright
      have hvalueCount : (groupValues left).length + (groupValues right).length < 8 := by
        simpa [groupValues] using hcount
      unfold parseSegsV6
      rw [splitOn_doubleColon_eq, hsplit]
      simp only
      rw [hleftParse, hrightParse]
      simp only [bind, Option.bind]
      rw [if_pos hvalueCount]
      change
        finishV6
            (groupValues left ++
              List.replicate
                (8 - ((groupValues left).length + (groupValues right).length)) 0 ++
              groupValues right) =
          some (V6Components.toAddr (.gap left right))
      have hfinish :
          finishV6 (groupValues (V6Components.expand (.gap left right))) =
            some (V6Components.toAddr (.gap left right)) := by
        apply finishV6_groupValues_eq_toAddr
        simp only [V6Components.expand, List.length_append, List.length_replicate]
        omega
      simpa [V6Components.expand, groupValues, hexValue_zero] using hfinish

private theorem parseSegsV6_some_wf {str : String} {addr : IPv6Addr}
    (h : parseSegsV6 str = some addr) :
    ∃ v : V6Components,
      str = v.asString ∧ v.syntaxWf ∧ addr = v.toAddr := by
  unfold parseSegsV6 at h
  rw [splitOn_doubleColon_eq] at h
  generalize hsplits : splitDoubleColonModel str = splits at h
  rcases splits with _ | ⟨leftStr, rest⟩
  · simp at h
  rcases rest with _ | ⟨rightStr, rest⟩
  ·
    cases hp : parseNumSegsV6 leftStr with
    | none => simp [hp] at h
    | some values =>
      simp only [hp, bind, Option.bind] at h
      change finishV6 values = some addr at h
      obtain ⟨parts, hleftStr, hall, hvalues⟩ := parseNumSegsV6_some_wf hp
      have hlenValues := finishV6_length_of_some h
      have hlen : parts.length = 8 := by
        rw [hvalues] at hlenValues
        simpa [groupValues] using hlenValues
      refine ⟨.full parts, ?_, ⟨hlen, hall⟩, ?_⟩
      · have hstr := eq_intercalate_of_splitDoubleColonModel_eq hsplits
        rw [String.intercalate_singleton, hleftStr] at hstr
        simpa [V6Components.asString] using hstr
      · rw [hvalues] at h
        have hfinish :
            finishV6 (groupValues parts) =
              some (V6Components.toAddr (.full parts)) := by
          apply finishV6_groupValues_eq_toAddr (v := .full parts)
          simpa [V6Components.expand] using hlen
        rw [hfinish] at h
        injection h with haddr
        exact haddr.symm
  rcases rest with _ | ⟨extra, rest⟩
  ·
    cases hleftParse : parseNumSegsV6 leftStr with
    | none => simp [hleftParse] at h
    | some leftValues =>
      cases hrightParse : parseNumSegsV6 rightStr with
      | none => simp [hleftParse, hrightParse] at h
      | some rightValues =>
        simp only [hleftParse, hrightParse, bind, Option.bind] at h
        split at h <;> rename_i hcount
        ·
          change
            finishV6
                (leftValues ++
                  List.replicate (8 - (leftValues.length + rightValues.length)) 0 ++
                  rightValues) =
              some addr at h
          obtain ⟨left, hleftStr, hleft, hleftValues⟩ :=
            parseNumSegsV6_some_wf hleftParse
          obtain ⟨right, hrightStr, hright, hrightValues⟩ :=
            parseNumSegsV6_some_wf hrightParse
          rw [hleftValues, hrightValues] at h hcount
          have hsyntaxCount : left.length + right.length < 8 := by
            simpa [groupValues] using hcount
          refine ⟨.gap left right, ?_, ⟨hsyntaxCount, hleft, hright⟩, ?_⟩
          · have hstr := eq_intercalate_of_splitDoubleColonModel_eq hsplits
            rw [String.intercalate_cons_cons, String.intercalate_singleton,
              hleftStr, hrightStr] at hstr
            simpa [V6Components.asString, String.append_assoc] using hstr
          · have hfinish :
                finishV6 (groupValues (V6Components.expand (.gap left right))) =
                  some (V6Components.toAddr (.gap left right)) := by
              apply finishV6_groupValues_eq_toAddr
              simp only [V6Components.expand, List.length_append, List.length_replicate]
              omega
            have hfinish' :
                finishV6
                    (groupValues left ++
                      List.replicate
                        (8 - ((groupValues left).length + (groupValues right).length)) 0 ++
                      groupValues right) =
                  some (V6Components.toAddr (.gap left right)) := by
              simpa [V6Components.expand, groupValues, hexValue_zero] using hfinish
            rw [hfinish'] at h
            injection h with haddr
            exact haddr.symm
        · simp at h
  · simp at h

private theorem noSlashColon :
    ∀ c ∈ ":".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem noSlashDoubleColon :
    ∀ c ∈ "::".toList, (fun x : Char => decide (x = '/')) c = false := by
  simp

private theorem noSlashRenderGroups {parts : List String}
    (hall : ∀ part ∈ parts, IsHexGroup part) :
    ∀ c ∈ (String.intercalate ":" parts).toList,
      (fun x : Char => decide (x = '/')) c = false := by
  induction parts with
  | nil => simp
  | cons part parts ih =>
      cases parts with
      | nil =>
          simpa using noSlashOfHex (hall part (by simp))
      | cons next tail =>
          have hpart := noSlashOfHex (hall part (by simp))
          have htail := ih (fun item hitem => hall item (by simp [hitem]))
          simpa [String.append_assoc] using
            noSepAppend hpart (noSepAppend noSlashColon htail)

private theorem noSlashV6 (v : V6Components) (hsyn : v.syntaxWf) :
    ∀ c ∈ v.asString.toList, (fun x : Char => decide (x = '/')) c = false := by
  cases v with
  | full parts =>
      exact noSlashRenderGroups hsyn.2
  | gap left right =>
      simpa [V6Components.asString, String.append_assoc] using
        noSepAppend (noSlashRenderGroups hsyn.2.1)
          (noSepAppend noSlashDoubleColon (noSlashRenderGroups hsyn.2.2))

private theorem noDotColon :
    ∀ c ∈ ":".toList, (fun x : Char => decide (x = '.')) c = false := by
  simp

private theorem noDotDoubleColon :
    ∀ c ∈ "::".toList, (fun x : Char => decide (x = '.')) c = false := by
  simp

private theorem noDotRenderGroups {parts : List String}
    (hall : ∀ part ∈ parts, IsHexGroup part) :
    ∀ c ∈ (String.intercalate ":" parts).toList,
      (fun x : Char => decide (x = '.')) c = false := by
  induction parts with
  | nil => simp
  | cons part parts ih =>
      cases parts with
      | nil =>
          simpa using noDotOfHex (hall part (by simp))
      | cons next tail =>
          have hpart := noDotOfHex (hall part (by simp))
          have htail := ih (fun item hitem => hall item (by simp [hitem]))
          simpa [String.append_assoc] using
            noSepAppend hpart (noSepAppend noDotColon htail)

private theorem noDotV6 (v : V6Components) (hsyn : v.syntaxWf) :
    ∀ c ∈ v.asString.toList, (fun x : Char => decide (x = '.')) c = false := by
  cases v with
  | full parts =>
      exact noDotRenderGroups hsyn.2
  | gap left right =>
      simpa [V6Components.asString, String.append_assoc] using
        noSepAppend (noDotRenderGroups hsyn.2.1)
          (noSepAppend noDotDoubleColon (noDotRenderGroups hsyn.2.2))

/-- `parseIPv6Net` succeeds on a well-formed V6 string, yielding `v6Value`. -/
theorem parseIPv6Net_eq_some {v : V6Components} {pre : Option String}
    (hsyn : v.syntaxWf)
    (hpre : IsWfOptionalPrefix 3 (ADDR_SIZE V6_WIDTH) pre) :
    parseIPv6Net (v.asString ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v6Value v pre) :=
  by
  unfold parseIPv6Net
  cases pre with
  | none =>
      have hsplit : v.asString.splitToList (· = '/') = [v.asString] :=
        splitToList_no_sep v.asString (fun x : Char => decide (x = '/')) (noSlashV6 v hsyn)
      simp only [String.append_empty]
      rw [hsplit]
      simp only
      rw [parseSegsV6_asString hsyn]
      simp [v6Value, prefixValue, IPNetPrefix.ofNat]
  | some p =>
      have hsplit :
          (v.asString ++ ("/" ++ p)).splitToList (· = '/') = [v.asString, p] := by
        simpa [String.append_assoc] using
          splitToList_eq v.asString p (fun x : Char => decide (x = '/')) '/'
            (by simp) (noSlashV6 v hsyn) (noSlashOfCanonical hpre.1)
      simp only
      rw [hsplit]
      simp only
      rw [parsePrefixNat_eq_value hpre, parseSegsV6_asString hsyn]
      change IsCanonicalNat p ∧ p.length ≤ 3 ∧ numValue p ≤ ADDR_SIZE V6_WIDTH at hpre
      have hlt : numValue p < ADDR_SIZE V6_WIDTH + 1 := by omega
      simp [v6Value, prefixValue, IPNetPrefix.ofNat, Fin.ofNat, Nat.mod_eq_of_lt hlt]

/-- Soundness for V6: a successful `parseIPv6Net` means the string is a well-formed V6 rendering. -/
theorem parseIPv6Net_isSome_wf {str : String} {net : IPNet} (h : parseIPv6Net str = some net) :
    IsWfV6 str ∧ ∃ v pre, net = v6Value v pre :=
  by
  unfold parseIPv6Net at h
  generalize hsplits : str.splitToList (· = '/') = parts at h
  rcases parts with _ | ⟨addrStr, rest⟩
  · simp at h
  rcases rest with _ | ⟨preStr, rest⟩
  ·
    cases ha : parseSegsV6 addrStr with
    | none => simp [ha] at h
    | some addr =>
      simp [ha] at h
      obtain ⟨v, haddrStr, hsyn, haddr⟩ := parseSegsV6_some_wf ha
      have hstr := eq_intercalate_of_splitToList_eq '/' hsplits
      rw [String.intercalate_singleton, haddrStr] at hstr
      refine ⟨?_, v, none, ?_⟩
      · exact ⟨v, none, hsyn, trivial, by simpa using hstr⟩
      · subst addr
        simpa [v6Value, prefixValue, IPNetPrefix.ofNat] using h.symm
  rcases rest with _ | ⟨extra, rest⟩
  ·
    cases hp : parsePrefixNat preStr 3 (ADDR_SIZE V6_WIDTH) with
    | none => simp [hp] at h
    | some pre =>
      cases ha : parseSegsV6 addrStr with
      | none => simp [hp, ha] at h
      | some addr =>
        simp [hp, ha] at h
        obtain ⟨v, haddrStr, hsyn, haddr⟩ := parseSegsV6_some_wf ha
        obtain ⟨hpre, hpreValue⟩ := parsePrefixNat_some_wf hp
        have hstr := eq_intercalate_of_splitToList_eq '/' hsplits
        rw [String.intercalate_cons_cons, String.intercalate_singleton,
          haddrStr] at hstr
        refine ⟨?_, v, some preStr, ?_⟩
        · exact ⟨v, some preStr, hsyn, hpre, by
            simpa [String.append_assoc] using hstr⟩
        · subst addr
          simpa [v6Value, prefixValue, hpreValue] using h.symm
  · simp at h

/-- The V4 and V6 accepted-string sets are disjoint: no string parses as both. In particular a
    well-formed V6 string is not accepted by `parseIPv4Net` (needed for the `parse`'s V4-first
    fall-through to reach V6). -/
theorem parseIPv4Net_none_of_isWfV6 {str : String} (h : IsWfV6 str) :
    parseIPv4Net str = none :=
  by
  obtain ⟨v, pre, hsyn, hpre, rfl⟩ := h
  have haddrNone : parseSegsV4 v.asString = none := by
    have hsplit : v.asString.splitToList (· = '.') = [v.asString] :=
      splitToList_no_sep v.asString (fun x : Char => decide (x = '.')) (noDotV6 v hsyn)
    unfold parseSegsV4
    rw [hsplit]
  unfold parseIPv4Net
  cases pre with
  | none =>
      have hsplit : v.asString.splitToList (· = '/') = [v.asString] :=
        splitToList_no_sep v.asString (fun x : Char => decide (x = '/')) (noSlashV6 v hsyn)
      simp only [String.append_empty]
      rw [hsplit]
      simp only
      rw [haddrNone]
      rfl
  | some p =>
      have hsplit :
          (v.asString ++ ("/" ++ p)).splitToList (· = '/') = [v.asString, p] := by
        simpa [String.append_assoc] using
          splitToList_eq v.asString p (fun x : Char => decide (x = '/')) '/'
            (by simp) (noSlashV6 v hsyn) (noSlashOfCanonical hpre.1)
      simp only
      rw [hsplit]
      simp only
      cases parsePrefixNat p 2 (ADDR_SIZE V4_WIDTH)
      · rfl
      · rw [haddrNone]
        rfl

end Cedar.Thm.IPAddr
