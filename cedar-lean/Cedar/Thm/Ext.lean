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

import Cedar.Spec.Ext
import Cedar.Spec.ExtFun

namespace Cedar.Thm.Ext

open Cedar.Spec.Ext

/--
  If parsing the string representation of a `decimal` succeeds, it gives you
  exactly that `decimal` back
-/
theorem decimal_parse_roundtrip {d d' : Decimal} :
  Decimal.decimal (toString d) = some d' → d = d'
:= by
  simp [toString, Decimal.decimal, Decimal.parse]
  sorry

/--
  The string representation of a `decimal` is always parseable
-/
theorem decimal_toString_is_parseable (d : Decimal) :
  (Decimal.decimal (toString d)).isSome
:= by
  simp [toString, Decimal.decimal, Decimal.parse]
  sorry

theorem decimal_toString_inverse (d : Decimal) :
  Spec.call Spec.ExtFun.decimal [.prim (.string (toString d))] = .ok (.ext (.decimal d))
:= by
  simp [Spec.call, Spec.res, Coe.coe]
  cases h₁ : Decimal.decimal (toString d)
  <;> simp only [Except.ok.injEq, Spec.Value.ext.injEq, decimal.injEq]
  case none =>
    rw [← Option.not_isSome_iff_eq_none] at h₁
    simp [decimal_toString_is_parseable d] at h₁
  case some d' =>
    exact (decimal_parse_roundtrip h₁).symm

/--
  If parsing the string representation of an `ip` as IPv4 succeeds, it gives you
  exactly that `ip` back
-/
theorem parseIPv4net_roundtrip {ip ip' : Spec.IPAddr} :
  IPAddr.parseIPv4Net (toString ip) = some ip' → ip = ip'
:= by
  sorry

/--
  If parsing the string representation of an `ip` as IPv6 succeeds, it gives you
  exactly that `ip` back
-/
theorem parseIPv6net_roundtrip {ip ip' : Spec.IPAddr} :
  IPAddr.parseIPv6Net (toString ip) = some ip' → ip = ip'
:= by
  sorry

/--
  The string representation of an `ip` is always parseable, either as an IPv4 or
  an IPv6
-/
theorem ipaddr_toString_is_parseable (ip : Spec.IPAddr) :
  (IPAddr.parseIPv4Net (toString ip)).isSome ∨
  (IPAddr.parseIPv6Net (toString ip)).isSome
:= by
  sorry

theorem ipaddr_toString_inverse (ip : Spec.IPAddr) :
  Spec.call Spec.ExtFun.ip [.prim (.string (toString ip))] = .ok (.ext (.ipaddr ip))
:= by
  simp [Spec.call, Spec.res, Coe.coe]
  cases h₁ : IPAddr.ip (toString ip)
  <;> simp only [Except.ok.injEq, Spec.Value.ext.injEq, ipaddr.injEq]
  case none =>
    simp [IPAddr.ip, IPAddr.parse] at h₁
    split at h₁ <;> rename_i h₂
    · replace ⟨ipnet, h₂⟩ := Option.isSome_iff_exists.mp h₂
      simp [h₂] at h₁
    · simp only [Option.not_isSome, Option.isNone_iff_eq_none, Bool.not_eq_true] at h₂
      rcases ipaddr_toString_is_parseable ip with h₃ | h₃
      · simp [Option.isSome, h₂] at h₃
      · simp [Option.isSome, h₁] at h₃
  case some ipnet =>
    simp [IPAddr.ip, IPAddr.parse] at h₁
    split at h₁ <;> rename_i h₂
    · replace ⟨ipnet', h₂⟩ := Option.isSome_iff_exists.mp h₂
      simp [h₂] at h₁ ; subst ipnet'
      exact (parseIPv4net_roundtrip h₂).symm
    · simp only [Option.not_isSome, Option.isNone_iff_eq_none, Bool.not_eq_true] at h₂
      exact (parseIPv6net_roundtrip h₁).symm

end Cedar.Thm.Ext
