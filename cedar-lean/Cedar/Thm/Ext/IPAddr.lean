module

public import Cedar.Thm.Ext.IPAddr.Lemmas

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Thm.Ext.IPAddr.Grammar
import all Cedar.Thm.Ext.IPAddr.Lemmas
import all Init.Data.Repr

namespace Cedar.Thm.IPAddr
open Cedar.Spec.Ext
open IPAddr

/-! # IPAddr parser correctness

`parse_sound`, `parse_complete`, and `parse_eq_none_iff` characterize exactly when
`Cedar.Spec.Ext.IPAddr.ip` (a.k.a. `ip`) succeeds, in terms of the grammar-level `IsWfIPNet`
predicate and the `v4Value`/`v6Value` value functions (both in `Cedar.Thm.Ext.IPAddr.Grammar`). The
parser-independent bridge lemmas they build on live in `Cedar.Thm.Ext.IPAddr.Lemmas`.

Unlike decimal/duration, the value of an IP-net is not a single `Int` but an `IPNet`, so soundness
is phrased as "the returned net equals the components' value". Unlike datetime, the parser is
hand-written (no `Std.Time` delegation), so the bridges are direct string-manipulation reasoning.

`IsWfIPNet` is `IsWfV4 ∨ IsWfV6`. On the value side there is no separate `computeValue : Option`
(as in decimal): a well-formed string determines its `IPNet` via `v4Value`/`v6Value`, so soundness
and completeness are stated per witnessing components. -/

/-! ## Soundness -/

/-- Soundness of `IPAddr.ip`: if parsing succeeds, the input is a well-formed IP-net string, and
    the returned net is the value of its witnessing components. -/
public theorem parse_sound (str : String) (net : IPNet) (h : IPAddr.ip str = some net) :
    IsWfIPNet str ∧
    ((∃ v pre, net = v4Value v pre) ∨ (∃ v pre, net = v6Value v pre)) := by
  unfold IPAddr.ip parse at h
  simp only at h
  split at h
  · obtain ⟨hwf, hvalue⟩ := parseIPv4Net_isSome_wf h
    exact ⟨Or.inl hwf, Or.inl hvalue⟩
  · obtain ⟨hwf, hvalue⟩ := parseIPv6Net_isSome_wf h
    exact ⟨Or.inr hwf, Or.inr hvalue⟩

/-! ## Completeness -/

/-- Completeness for the V4 form: a well-formed V4 string parses to its `v4Value`. -/
public theorem parse_complete_v4 {v : V4Components} {pre : Option String}
    (hsyn : v.syntaxWf) (hcon : v.constraintsWf)
    (hpre : IsWfOptionalPrefix 2 (ADDR_SIZE V4_WIDTH) pre) :
    IPAddr.ip (v.asString ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v4Value v pre) := by
  have hparse :
      parseIPv4Net (v.asString ++ (match pre with | none => "" | some p => "/" ++ p)) =
        some (v4Value v pre) :=
    parseIPv4Net_eq_some (v := v) (pre := pre) hsyn hcon hpre
  unfold IPAddr.ip parse
  simp only
  rw [hparse]
  simp

/-- Completeness for the V6 form: a well-formed V6 string parses to its `v6Value`. -/
public theorem parse_complete_v6 {v : V6Components} {pre : Option String}
    (hsyn : v.syntaxWf)
    (hpre : IsWfOptionalPrefix 3 (ADDR_SIZE V6_WIDTH) pre) :
    IPAddr.ip (v.asString ++ (match pre with | none => "" | some p => "/" ++ p))
      = some (v6Value v pre) := by
  cases pre with
  | none =>
      have hwf : IsWfV6 v.asString := ⟨v, none, hsyn, hpre, by simp⟩
      have hv4 : parseIPv4Net v.asString = none := parseIPv4Net_none_of_isWfV6 hwf
      have hv6 : parseIPv6Net v.asString = some (v6Value v none) := by
        simpa using parseIPv6Net_eq_some (v := v) (pre := none) hsyn hpre
      simp only [String.append_empty]
      unfold IPAddr.ip parse
      simp only
      rw [hv4, hv6]
      rfl
  | some p =>
      have hwf : IsWfV6 (v.asString ++ ("/" ++ p)) :=
        ⟨v, some p, hsyn, hpre, rfl⟩
      have hv4 : parseIPv4Net (v.asString ++ ("/" ++ p)) = none :=
        parseIPv4Net_none_of_isWfV6 hwf
      have hv6 : parseIPv6Net (v.asString ++ ("/" ++ p)) =
          some (v6Value v (some p)) := by
        simpa using parseIPv6Net_eq_some (v := v) (pre := some p) hsyn hpre
      unfold IPAddr.ip parse
      simp only
      rw [hv4, hv6]
      rfl

/-- Completeness of `IPAddr.ip`: every well-formed IP-net string is accepted (with the value of
    its witnessing components). -/
public theorem parse_complete (str : String) (h : IsWfIPNet str) :
    (IPAddr.ip str).isSome := by
  rcases h with hv4 | hv6
  · obtain ⟨v, pre, hsyn, hcon, hpre, hstr⟩ := hv4
    cases pre with
    | none =>
        simp only [String.append_empty] at hstr
        subst str
        have hparse : IPAddr.ip v.asString = some (v4Value v none) := by
          simpa only [String.append_empty] using
            (parse_complete_v4 (v := v) (pre := none) hsyn hcon hpre)
        rw [hparse]
        simp
    | some p =>
        subst str
        rw [parse_complete_v4 (v := v) (pre := some p) hsyn hcon hpre]
        simp
  · obtain ⟨v, pre, hsyn, hpre, hstr⟩ := hv6
    cases pre with
    | none =>
        simp only [String.append_empty] at hstr
        subst str
        have hparse : IPAddr.ip v.asString = some (v6Value v none) := by
          simpa only [String.append_empty] using
            (parse_complete_v6 (v := v) (pre := none) hsyn hpre)
        rw [hparse]
        simp
    | some p =>
        subst str
        rw [parse_complete_v6 (v := v) (pre := some p) hsyn hpre]
        simp

/-! ## Failure characterization -/

/-- Failure characterization: `IPAddr.ip` rejects exactly the strings that are not well-formed
    IP-nets. (There is no overflow condition — the grammar's field bounds already exclude
    out-of-range values.) -/
public theorem parse_eq_none_iff (str : String) :
    IPAddr.ip str = none ↔ ¬ IsWfIPNet str := by
  constructor
  · intro hnone hwf
    have hsome := parse_complete str hwf
    rw [hnone] at hsome
    simp at hsome
  · intro hnwf
    cases hparse : IPAddr.ip str with
    | none => rfl
    | some net => exact (hnwf (parse_sound str net hparse).1).elim

/-! ## Roundtrip -/

private theorem toNat?'_toString (n : Nat) : toNat?' (toString n) = some n := by
  unfold toNat?'
  have hno_us : (toString n).contains '_' = false := by
    have h : ¬ ('_' ∈ (toString n).toList) := by
      rw [Nat.toString_eq_repr, Nat.toList_repr]
      exact Nat.underscore_not_in_toDigits
    simp [String.contains]
  rw [hno_us]
  simp [Nat.toString_eq_repr]

private theorem isDigits_toString (n : Nat) : IsDigits (toString n) :=
  isDigits_of_toNat?'_isSome (by rw [toNat?'_toString]; simp)

private theorem canonical_toString (n : Nat) :
    (toString n).startsWith "0" → toString n = "0" := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hstarts
    rw [String.startsWith_string_iff] at hstarts
    by_cases hlt : n < 10
    · rw [Nat.toString_eq_repr, Nat.repr_of_lt hlt] at hstarts ⊢
      simp at hstarts
      subst n
      apply String.toList_inj.mp
      simp
    · have hge : 10 ≤ n := by omega
      have hq : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
      have hqstarts : (toString (n / 10)).startsWith "0" := by
        have hrepr :
            (toString n).toList =
              (toString (n / 10)).toList ++
                (String.singleton (Nat.digitChar (n % 10))).toList := by
          rw [Nat.toString_eq_repr, Nat.repr_of_ge hge, String.toList_append]
          simp [Nat.toString_eq_repr]
        rw [hrepr] at hstarts
        cases hlist : (toString (n / 10)).toList with
        | nil =>
          have hne : toString (n / 10) ≠ "" := by
            rw [Nat.toString_eq_repr]
            exact Nat.repr_ne_empty
          exfalso
          apply hne
          apply String.toList_inj.mp
          rw [hlist]
          rfl
        | cons c cs =>
          rw [hlist] at hstarts
          simp only [List.cons_append] at hstarts
          rw [String.startsWith_string_iff, hlist]
          simpa using hstarts
      have hqzero : toString (n / 10) = "0" := ih (n / 10) hq hqstarts
      have heq := congrArg toNat?' hqzero
      rw [toNat?'_toString] at heq
      have htoStringZero : toString (0 : Nat) = "0" := by
        rw [Nat.toString_eq_repr, Nat.repr_of_lt (by omega)]
        apply String.toList_inj.mp
        simp
      have hzero : toNat?' "0" = some 0 := by
        rw [← htoStringZero, toNat?'_toString]
      rw [hzero] at heq
      injection heq with hqeq
      omega

private theorem isCanonicalNat_toString (n : Nat) : IsCanonicalNat (toString n) :=
  ⟨isDigits_toString n, canonical_toString n⟩

private theorem toString_length_le {n width : Nat} (hbound : n < 10 ^ width)
    (hwidth : 0 < width) :
    (toString n).length ≤ width := by
  rw [Nat.toString_eq_repr]
  exact (Nat.length_repr_le_iff hwidth).mpr hbound

private theorem v4Addr_toNat_mk (a₀ a₁ a₂ a₃ : BitVec 8) :
    (IPv4Addr.mk a₀ a₁ a₂ a₃).toNat =
      ((a₀.toNat * 256 + a₁.toNat) * 256 + a₂.toNat) * 256 + a₃.toNat := by
  unfold IPv4Addr.mk
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₃)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₂)]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt a₁)]
  simp [Nat.shiftLeft_eq]

private theorem v4Components_toAddr_of_addr (addr : IPv4Addr) :
    let v := addr.toNat
    V4Components.toAddr
        ⟨toString ((v >>> 24) &&& 0xff), toString ((v >>> 16) &&& 0xff),
          toString ((v >>> 8) &&& 0xff), toString (v &&& 0xff)⟩ =
      addr := by
  dsimp only
  unfold V4Components.toAddr numValue
  repeat rw [toNat?'_toString]
  simp only [Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  rw [v4Addr_toNat_mk]
  simp
  have hmask : (0xff : Nat) = 2 ^ 8 - 1 := by decide
  simp only [hmask, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  have hbound := BitVec.isLt addr
  change addr.toNat < 2 ^ 32 at hbound
  omega

private theorem v4Prefix_of_toNat (pre : IPv4Prefix) :
    (pre.toNat : IPv4Prefix) = pre := by
  cases pre with
  | none => rfl
  | some pre =>
      have hbound := BitVec.isLt pre
      change pre.toNat < 2 ^ 5 at hbound
      change (if pre.toNat < 32 then some (BitVec.ofNat 5 pre.toNat) else none) = some pre
      rw [if_pos (by omega)]
      congr
      apply BitVec.eq_of_toNat_eq
      simp

private theorem mask255_le (n : Nat) : n &&& 0xff ≤ 255 := by
  have h := Nat.and_lt_two_pow n (n := 8) (y := 0xff) (by decide)
  omega

private theorem v4Prefix_toNat_le (pre : IPv4Prefix) : pre.toNat ≤ 32 := by
  cases pre with
  | none =>
      change 32 ≤ 32
      omega
  | some pre =>
      have hbound := BitVec.isLt pre
      change pre.toNat < 2 ^ 5 at hbound
      change pre.toNat ≤ 32
      omega

private theorem parse_toString_v4 (addr : IPv4Addr) (pre : IPv4Prefix) :
    IPAddr.ip (toString (IPNet.V4 ⟨addr, pre⟩)) = some (IPNet.V4 ⟨addr, pre⟩) := by
  let v := addr.toNat
  let g₀ := toString ((v >>> 24) &&& 0xff)
  let g₁ := toString ((v >>> 16) &&& 0xff)
  let g₂ := toString ((v >>> 8) &&& 0xff)
  let g₃ := toString (v &&& 0xff)
  let p := toString pre.toNat
  let c : V4Components := ⟨g₀, g₁, g₂, g₃⟩
  have hsyn : c.syntaxWf := by
    refine
      ⟨⟨isCanonicalNat_toString _, toString_length_le (by
          have h := mask255_le (v >>> 24)
          omega) (by omega)⟩,
        ⟨isCanonicalNat_toString _, toString_length_le (by
          have h := mask255_le (v >>> 16)
          omega) (by omega)⟩,
        ⟨isCanonicalNat_toString _, toString_length_le (by
          have h := mask255_le (v >>> 8)
          omega) (by omega)⟩,
        ⟨isCanonicalNat_toString _, toString_length_le (by
          have h := mask255_le v
          omega) (by omega)⟩⟩
  have hcon : c.constraintsWf := by
    simp only [V4Components.constraintsWf, c, g₀, g₁, g₂, g₃, numValue]
    repeat rw [toNat?'_toString]
    simp only [Option.getD_some]
    exact ⟨mask255_le _, mask255_le _, mask255_le _, mask255_le _⟩
  have hpre : IsWfOptionalPrefix 2 (ADDR_SIZE V4_WIDTH) (some p) := by
    simp only [IsWfOptionalPrefix]
    refine
      ⟨isCanonicalNat_toString _,
        toString_length_le (by
          have h := v4Prefix_toNat_le pre
          omega) (by omega),
        ?_⟩
    simp only [p, numValue]
    rw [toNat?'_toString]
    simp only [Option.getD_some]
    change pre.toNat ≤ 32
    exact v4Prefix_toNat_le pre
  have haddr : c.toAddr = addr := by
    simpa [c, g₀, g₁, g₂, g₃, v] using v4Components_toAddr_of_addr addr
  have hpfx : prefixValue V4_WIDTH (some p) = pre := by
    simp only [prefixValue, p, numValue]
    rw [toNat?'_toString]
    simp only [Option.getD_some]
    exact v4Prefix_of_toNat pre
  have hvalue : v4Value c (some p) = IPNet.V4 ⟨addr, pre⟩ := by
    simp [v4Value, haddr, hpfx]
  have hrender :
      toString (IPNet.V4 ⟨addr, pre⟩) = c.asString ++ ("/" ++ p) := by
    calc
      toString (IPNet.V4 ⟨addr, pre⟩) =
          s!"{(addr.toNat >>> 24) &&& 0xff}.{(addr.toNat >>> 16) &&& 0xff}.\
            {(addr.toNat >>> 8) &&& 0xff}.{addr.toNat &&& 0xff}/{pre.toNat}" := rfl
      _ = c.asString ++ ("/" ++ p) := by
        have hdot : toString "." = "." := rfl
        have hslash : toString "/" = "/" := rfl
        simp [c, g₀, g₁, g₂, g₃, p, v, V4Components.asString, hdot, hslash,
          String.append_assoc]
  calc
    IPAddr.ip (toString (IPNet.V4 ⟨addr, pre⟩)) =
        IPAddr.ip (c.asString ++ ("/" ++ p)) := congrArg IPAddr.ip hrender
    _ = some (v4Value c (some p)) := parse_complete_v4 hsyn hcon hpre
    _ = some (IPNet.V4 ⟨addr, pre⟩) := congrArg some hvalue

private def hex16 (n : Nat) : String :=
  String.singleton ((n % 0x10000) / 0x1000).digitChar ++
    String.singleton ((n % 0x1000) / 0x100).digitChar ++
    String.singleton ((n % 0x100) / 0x10).digitChar ++
    String.singleton ((n % 0x10) / 0x1).digitChar

private theorem digitChar_isHexDigit {n : Nat} (h : n < 16) :
    isHexDigit n.digitChar = true := by
  by_cases hten : n < 10
  · unfold isHexDigit
    rw [Nat.isDigit_digitChar]
    simp [hten]
  · have hn : n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show Nat.digitChar 10 = 'a' by simp]
      simp [isHexDigit]
    · rw [show Nat.digitChar 11 = 'b' by simp]
      simp [isHexDigit]
    · rw [show Nat.digitChar 12 = 'c' by simp]
      simp [isHexDigit]
    · rw [show Nat.digitChar 13 = 'd' by simp]
      simp [isHexDigit]
    · rw [show Nat.digitChar 14 = 'e' by simp]
      simp [isHexDigit]
    · rw [show Nat.digitChar 15 = 'f' by simp]
      simp [isHexDigit]

private theorem hex16_isHexGroup (n : Nat) : IsHexGroup (hex16 n) := by
  have h₀ : (n % 0x10000) / 0x1000 < 16 := by omega
  have h₁ : (n % 0x1000) / 0x100 < 16 := by omega
  have h₂ : (n % 0x100) / 0x10 < 16 := by omega
  have h₃ : (n % 0x10) / 0x1 < 16 := by omega
  unfold IsHexGroup hex16
  constructor
  · simp
  constructor
  · simp
  · intro c hc
    simp only [String.toList_append, String.toList_singleton, List.mem_append,
      List.mem_singleton] at hc
    rcases hc with ((rfl | rfl) | rfl) | rfl
    · exact digitChar_isHexDigit h₀
    · exact digitChar_isHexDigit h₁
    · exact digitChar_isHexDigit h₂
    · exact digitChar_isHexDigit h₃

private theorem toHexNat_digitChar {n : Nat} (h : n < 16) :
    toHexNat n.digitChar = n := by
  by_cases hten : n < 10
  · unfold toHexNat
    have hdigit : n.digitChar.isDigit = true := by
      rw [Nat.isDigit_digitChar]
      simp [hten]
    rw [if_pos hdigit]
    exact Nat.toNat_digitChar_sub_48_of_lt_ten hten
  · have hn : n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 ∨ n = 15 := by omega
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [show Nat.digitChar 10 = 'a' by simp]
      simp [toHexNat]
    · rw [show Nat.digitChar 11 = 'b' by simp]
      simp [toHexNat]
    · rw [show Nat.digitChar 12 = 'c' by simp]
      simp [toHexNat]
    · rw [show Nat.digitChar 13 = 'd' by simp]
      simp [toHexNat]
    · rw [show Nat.digitChar 14 = 'e' by simp]
      simp [toHexNat]
    · rw [show Nat.digitChar 15 = 'f' by simp]
      simp [toHexNat]

private theorem hexValue_hex16 (n : Nat) :
    hexValue (hex16 n) = n % 0x10000 := by
  have h₀ : (n % 0x10000) / 0x1000 < 16 := by omega
  have h₁ : (n % 0x1000) / 0x100 < 16 := by omega
  have h₂ : (n % 0x100) / 0x10 < 16 := by omega
  have h₃ : (n % 0x10) / 0x1 < 16 := by omega
  unfold hexValue hex16
  simp only [String.foldl_eq_foldl_toList, String.toList_append,
    String.toList_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [toHexNat_digitChar h₀, toHexNat_digitChar h₁, toHexNat_digitChar h₂,
    toHexNat_digitChar h₃]
  omega

private theorem v6Components_toAddr_of_addr (addr : IPv6Addr) :
    let v := addr.toNat
    V6Components.toAddr
      (.full
        [hex16 ((v >>> 112) &&& 0xffff), hex16 ((v >>> 96) &&& 0xffff),
          hex16 ((v >>> 80) &&& 0xffff), hex16 ((v >>> 64) &&& 0xffff),
          hex16 ((v >>> 48) &&& 0xffff), hex16 ((v >>> 32) &&& 0xffff),
          hex16 ((v >>> 16) &&& 0xffff), hex16 (v &&& 0xffff)]) =
      addr := by
  dsimp only
  unfold V6Components.toAddr V6Components.expand
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  change IPv6Addr.mk
    (BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> 112) &&& 0xffff))))
    (BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> 96) &&& 0xffff))))
    (BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> 80) &&& 0xffff))))
    (BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> 64) &&& 0xffff))))
    (BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> 48) &&& 0xffff))))
    (BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> 32) &&& 0xffff))))
    (BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> 16) &&& 0xffff))))
    (BitVec.ofNat 16 (hexValue (hex16 (addr.toNat &&& 0xffff)))) = addr
  have hchunk (start : Nat) :
      BitVec.ofNat 16 (hexValue (hex16 ((addr.toNat >>> start) &&& 0xffff))) =
        addr.extractLsb' start 16 := by
    rw [hexValue_hex16]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.extractLsb'_toNat]
    have hmask : (0xffff : Nat) = 2 ^ 16 - 1 := by decide
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod]
    simp
  rw [hchunk 112, hchunk 96, hchunk 80, hchunk 64, hchunk 48, hchunk 32, hchunk 16]
  rw [show BitVec.ofNat 16 (hexValue (hex16 (addr.toNat &&& 0xffff))) =
      addr.extractLsb' 0 16 by simpa using hchunk 0]
  unfold IPv6Addr.mk
  repeat rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by omega)]
  exact BitVec.extractLsb'_eq_self

private theorem v6Prefix_of_toNat (pre : IPv6Prefix) :
    (pre.toNat : IPv6Prefix) = pre := by
  cases pre with
  | none => rfl
  | some pre =>
      have hbound := BitVec.isLt pre
      change pre.toNat < 2 ^ 7 at hbound
      change (if pre.toNat < 128 then some (BitVec.ofNat 7 pre.toNat) else none) = some pre
      rw [if_pos hbound]
      congr
      apply BitVec.eq_of_toNat_eq
      simp

private theorem v6Prefix_toNat_le (pre : IPv6Prefix) : pre.toNat ≤ 128 := by
  cases pre with
  | none =>
      change 128 ≤ 128
      omega
  | some pre =>
      have hbound := BitVec.isLt pre
      change pre.toNat < 2 ^ 7 at hbound
      change pre.toNat ≤ 128
      omega

private theorem parse_toString_v6 (addr : IPv6Addr) (pre : IPv6Prefix) :
    IPAddr.ip (toString (IPNet.V6 ⟨addr, pre⟩)) = some (IPNet.V6 ⟨addr, pre⟩) := by
  let v := addr.toNat
  let h₀ := hex16 ((v >>> 112) &&& 0xffff)
  let h₁ := hex16 ((v >>> 96) &&& 0xffff)
  let h₂ := hex16 ((v >>> 80) &&& 0xffff)
  let h₃ := hex16 ((v >>> 64) &&& 0xffff)
  let h₄ := hex16 ((v >>> 48) &&& 0xffff)
  let h₅ := hex16 ((v >>> 32) &&& 0xffff)
  let h₆ := hex16 ((v >>> 16) &&& 0xffff)
  let h₇ := hex16 (v &&& 0xffff)
  let p := toString pre.toNat
  let c : V6Components := .full [h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇]
  have hsyn : c.syntaxWf := by
    constructor
    · rfl
    · intro part hpart
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpart
      rcases hpart with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact hex16_isHexGroup _
  have hpre : IsWfOptionalPrefix 3 (ADDR_SIZE V6_WIDTH) (some p) := by
    simp only [IsWfOptionalPrefix]
    refine
      ⟨isCanonicalNat_toString _,
        toString_length_le (by
          have h := v6Prefix_toNat_le pre
          omega) (by omega),
        ?_⟩
    simp only [p, numValue]
    rw [toNat?'_toString]
    simp only [Option.getD_some]
    change pre.toNat ≤ 128
    exact v6Prefix_toNat_le pre
  have haddr : c.toAddr = addr := by
    simpa [c, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, v] using
      v6Components_toAddr_of_addr addr
  have hpfx : prefixValue V6_WIDTH (some p) = pre := by
    simp only [prefixValue, p, numValue]
    rw [toNat?'_toString]
    simp only [Option.getD_some]
    exact v6Prefix_of_toNat pre
  have hvalue : v6Value c (some p) = IPNet.V6 ⟨addr, pre⟩ := by
    simp [v6Value, haddr, hpfx]
  have hrender :
      toString (IPNet.V6 ⟨addr, pre⟩) = c.asString ++ ("/" ++ p) := by
    have hcanonical :
        toString (IPNet.V6 ⟨addr, pre⟩) =
          s!"{hex16 ((addr.toNat >>> 112) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 96) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 80) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 64) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 48) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 32) &&& 0xffff)}:\
            {hex16 ((addr.toNat >>> 16) &&& 0xffff)}:\
            {hex16 (addr.toNat &&& 0xffff)}/{pre.toNat}" := by
      rfl
    rw [hcanonical]
    have hstring (s : String) : toString s = s := rfl
    simp [c, h₀, h₁, h₂, h₃, h₄, h₅, h₆, h₇, p, v, V6Components.asString,
      hstring, String.append_assoc]
  calc
    IPAddr.ip (toString (IPNet.V6 ⟨addr, pre⟩)) =
        IPAddr.ip (c.asString ++ ("/" ++ p)) := congrArg IPAddr.ip hrender
    _ = some (v6Value c (some p)) := parse_complete_v6 hsyn hpre
    _ = some (IPNet.V6 ⟨addr, pre⟩) := congrArg some hvalue

/-- `parse ∘ toString` roundtrip: parsing the canonical representation recovers the original
    IP-net. -/
public theorem parse_toString_roundtrip (net : IPNet) :
    IPAddr.ip (toString net) = some net := by
  cases net with
  | V4 cidr =>
      cases cidr with
      | mk addr pre => exact parse_toString_v4 addr pre
  | V6 cidr =>
      cases cidr with
      | mk addr pre => exact parse_toString_v6 addr pre

/-- `toString` is injective: distinct IP-nets produce distinct canonical strings. -/
public theorem toString_injective (net net' : IPNet) (h : toString net = toString net') :
    net = net' := by
  have hnet := parse_toString_roundtrip net
  have hnet' := parse_toString_roundtrip net'
  rw [h] at hnet
  rw [hnet] at hnet'
  injection hnet'

/-- Equal normal form iff equal value: normalization decides IP-net equality. -/
public theorem normalize_eq_iff_parse_eq (str str' : String) :
    normalize str = normalize str' ↔ IPAddr.ip str = IPAddr.ip str' := by
  constructor
  · intro h
    unfold normalize at h
    match hparse : IPAddr.ip str, hparse' : IPAddr.ip str' with
    | .some net, .some net' =>
      simp [hparse, hparse', Option.map] at h
      exact congrArg _ (toString_injective net net' h)
    | .some net, .none => simp [hparse, hparse', Option.map] at h
    | .none, .some net' => simp [hparse, hparse', Option.map] at h
    | .none, .none => rfl
  · intro h
    simp [normalize, h]

end Cedar.Thm.IPAddr
