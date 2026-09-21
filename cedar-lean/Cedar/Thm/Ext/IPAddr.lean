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

public import Cedar.Thm.Ext.IPAddr.Lemmas

import all Cedar.Spec.Ext.Util
import all Cedar.Spec.Ext.IPAddr
import all Cedar.Thm.Ext.IPAddr.Grammar
import all Cedar.Thm.Ext.IPAddr.Lemmas

namespace Cedar.Thm.IPAddr
open Cedar.Spec.Ext
open IPAddr

/-! # IPAddr parser correctness

`parse_sound`, `parse_complete`, and `parse_eq_none_iff` characterize exactly when
`Cedar.Spec.Ext.IPAddr.ip` (a.k.a. `ip`) succeeds, in terms of the grammar-level `IsWfIPNet`
predicate and declarative `IsIPNetValue` relation. Its two branches use `v4Value` and `v6Value` to
give the denotation of the same components that witness the input rendering. The parser-independent
bridge lemmas they build on live in `Cedar.Thm.Ext.IPAddr.Lemmas`. -/

/-! ## Soundness -/

/-- Soundness of `IPAddr.ip`: if parsing succeeds, the declarative grammar relation assigns the
    input exactly the returned `IPNet`. -/
public theorem parse_sound (str : String) (net : IPNet) (h : IPAddr.ip str = some net) :
    IsIPNetValue str net := by
  unfold IPAddr.ip parse at h
  simp only at h
  split at h
  · exact Or.inl (parseIPv4Net_isSome_wf h)
  · exact Or.inr (parseIPv6Net_isSome_wf h)

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

/-- Completeness of `IPAddr.ip`: if the grammar assigns `str` the value `net`, parsing returns that
    exact `IPNet`. -/
public theorem parse_complete (str : String) (net : IPNet)
    (h : IsIPNetValue str net) :
    IPAddr.ip str = some net := by
  rcases h with hv4 | hv6
  · obtain ⟨v, pre, hsyn, hcon, hpre, hstr, hnet⟩ := hv4
    subst str
    subst net
    cases pre with
    | none => simpa using parse_complete_v4 hsyn hcon hpre
    | some p => simpa using parse_complete_v4 hsyn hcon hpre
  · obtain ⟨v, pre, hsyn, hpre, hstr, hnet⟩ := hv6
    subst str
    subst net
    cases pre with
    | none => simpa using parse_complete_v6 hsyn hpre
    | some p => simpa using parse_complete_v6 hsyn hpre

/-- Exact parser characterization: parsing succeeds with `net` precisely when the declarative
    grammar relation assigns the input that `IPNet`. -/
public theorem parse_eq_some_iff_isIPNetValue (str : String) (net : IPNet) :
    IPAddr.ip str = some net ↔ IsIPNetValue str net :=
  ⟨parse_sound str net, parse_complete str net⟩

/-- The relational value specification is single-valued: an IP-net string denotes at most one
    `IPNet`. -/
public theorem isIPNetValue_unique {str : String} {net₁ net₂ : IPNet}
    (h₁ : IsIPNetValue str net₁) (h₂ : IsIPNetValue str net₂) : net₁ = net₂ := by
  have hp₁ := parse_complete str net₁ h₁
  have hp₂ := parse_complete str net₂ h₂
  rw [hp₁] at hp₂
  exact Option.some.inj hp₂

/-! ## Failure characterization -/

/-- Failure characterization: `IPAddr.ip` rejects exactly the strings that are not well-formed
    IP-nets. (There is no overflow condition — the grammar's field bounds already exclude
    out-of-range values.) -/
public theorem parse_eq_none_iff (str : String) :
    IPAddr.ip str = none ↔ ¬ IsWfIPNet str := by
  constructor
  · intro hnone hwf
    obtain ⟨net, hvalue⟩ := isWfIPNet_iff_exists_value.mp hwf
    have hsome := parse_complete str net hvalue
    rw [hnone] at hsome
    contradiction
  · intro hnwf
    cases hparse : IPAddr.ip str with
    | none => rfl
    | some net =>
        exact (hnwf (isWfIPNet_iff_exists_value.mpr ⟨net, parse_sound str net hparse⟩)).elim

/-! ## Roundtrip -/

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
