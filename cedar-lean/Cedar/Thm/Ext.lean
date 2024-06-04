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

theorem decimal_toString_inverse (d : Decimal) :
  Spec.call Spec.ExtFun.decimal [.prim (.string (toString d))] = .ok (.ext (.decimal d))
:= by
  simp [Spec.call, Spec.res, Coe.coe]
  cases h₁ : Decimal.decimal (toString d)
  <;> simp only [Except.ok.injEq, Spec.Value.ext.injEq, decimal.injEq]
  case none =>
    simp [toString, Decimal.instToStringDecimal] at h₁
    simp [Decimal.decimal, Decimal.parse] at h₁
    sorry
  case some d' =>
    simp [toString, Decimal.instToStringDecimal] at h₁
    simp [Decimal.decimal, Decimal.parse] at h₁
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
      sorry -- can't unfold these private definitions; can we make them not private?
  case some ipnet =>
    simp [IPAddr.ip, IPAddr.parse] at h₁
    split at h₁ <;> rename_i h₂
    · replace ⟨ipnet', h₂⟩ := Option.isSome_iff_exists.mp h₂
      simp [h₂] at h₁ ; subst ipnet'
      sorry
    · simp only [Option.not_isSome, Option.isNone_iff_eq_none, Bool.not_eq_true] at h₂
      sorry -- can't unfold these private definitions; can we make them not private?

end Cedar.Thm.Ext
