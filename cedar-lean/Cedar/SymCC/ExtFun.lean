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

import Cedar.SymCC.Env
import Cedar.SymCC.Factory

/-!

This file contains the symbolic encoding (factory functions) for extension
operators.

The extension functions are total. If given well-formed and type-correct
arguments, an extension function will return a well-formed and type-correct
output. Otherwise, the output is an arbitrary term.

This design lets us minimize the number of error paths in the overall
specification of symbolic evaluation, which makes for nicer code and proofs, and
it more closely tracks the specification of the concrete evaluator.

See `Evaluator.lean` to see how the symbolic evaluator uses this API. See also
`Factory.lean`.

-/

namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec
open Factory Batteries

namespace Decimal

def lessThan (t₁ t₂ : Term) : Term :=
  bvslt (ext.decimal.val t₁) (ext.decimal.val t₂)

def lessThanOrEqual (t₁ t₂ : Term) : Term :=
  bvsle (ext.decimal.val t₁) (ext.decimal.val t₂)

def greaterThan (t₁ t₂ : Term) : Term :=
  lessThan t₂ t₁

def greaterThanOrEqual (t₁ t₂ : Term) : Term :=
  lessThanOrEqual t₂ t₁

end Decimal

namespace IPAddr
open BitVec

def isIpv4 (t : Term) : Term :=
  ext.ipaddr.isV4 t

def isIpv6 (t : Term) : Term :=
  not (ext.ipaddr.isV4 t)

def subnetWidth (w : Nat) (ipPre : Term) : Term :=
  let n := Ext.IPAddr.ADDR_SIZE w
  (ite
    (isNone ipPre)
    (BitVec.ofNat n 0)
    (bvsub (BitVec.ofNat n n) (zero_extend (n - w) (option.get ipPre))))

def range (w : Nat) (ipAddr ipPre : Term) : Term × Term :=
  let n := Ext.IPAddr.ADDR_SIZE w
  let width := subnetWidth w ipPre
  let lo := bvshl (bvlshr ipAddr width) width
  let hi := bvsub (bvadd lo (bvshl 1#n width)) 1#n
  (lo, hi)

def rangeV4 (t : Term) : Term × Term :=
  range 5 (ext.ipaddr.addrV4 t) (ext.ipaddr.prefixV4 t)

def rangeV6 (t : Term) : Term × Term :=
  range 7 (ext.ipaddr.addrV6 t) (ext.ipaddr.prefixV6 t)

def inRange (range : Term → Term × Term) (t₁ t₂ : Term) : Term :=
  let r₁ := range t₁
  let r₂ := range t₂
  (and (bvule r₁.2 r₂.2) (bvule r₂.1 r₁.1))

def inRangeV (isIp : Term → Term) (range : Term → Term × Term) (t₁ t₂ : Term) : Term :=
  (and
    (and (isIp t₁) (isIp t₂))
    (inRange range t₁ t₂))

def isInRange (t₁ t₂ : Term) : Term :=
  (or
    (inRangeV isIpv4 rangeV4 t₁ t₂)
    (inRangeV isIpv6 rangeV6 t₁ t₂))

def ipTerm (ip : IPAddr) : Term := (.prim (.ext (.ipaddr ip)))

def inRangeLit (t : Term) (cidr₄ : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH) (cidr₆ : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH) : Term :=
  (ite
    (isIpv4 t)
    (inRange rangeV4 t (ipTerm (Ext.IPAddr.IPNet.V4 cidr₄)))
    (inRange rangeV6 t (ipTerm (Ext.IPAddr.IPNet.V6 cidr₆))))

def isLoopback (t : Term) : Term :=
  inRangeLit t Ext.IPAddr.LOOP_BACK_CIDR_V4 Ext.IPAddr.LOOP_BACK_CIDR_V6

 def isMulticast (t : Term) : Term :=
  inRangeLit t Ext.IPAddr.MULTICAST_CIDR_V4 Ext.IPAddr.MULTICAST_CIDR_V6

end IPAddr

namespace Duration

def toMilliseconds (t : Term) : Term := ext.duration.val t

def toSeconds (t : Term) : Term :=
  bvsdiv (toMilliseconds t) (.prim (.bitvec (Int64.toBitVec 1000)))

def toMinutes (t : Term) : Term :=
  bvsdiv (toSeconds t) (.prim (.bitvec (Int64.toBitVec 60)))

def toHours (t : Term) : Term :=
  bvsdiv (toMinutes t) (.prim (.bitvec (Int64.toBitVec 60)))

def toDays (t : Term) : Term :=
  bvsdiv (toHours t) (.prim (.bitvec (Int64.toBitVec 24)))

end Duration

namespace Datetime

def offset (dt dur : Term) : Term :=
  let dt_val := ext.datetime.val dt
  let dur_val := ext.duration.val dur
  ifFalse (bvsaddo dt_val dur_val) (ext.datetime.ofBitVec (bvadd dt_val dur_val))

def durationSince (dt₁ dt₂ : Term) : Term :=
  let dt₁_val := ext.datetime.val dt₁
  let dt₂_val := ext.datetime.val dt₂
  ifFalse (bvssubo dt₁_val dt₂_val) (ext.duration.ofBitVec (bvsub dt₁_val dt₂_val))

def toDate (dt : Term) : Term :=
  let zero := .prim (.bitvec (Int64.toBitVec 0))
  let one := .prim (.bitvec (Int64.toBitVec 1))
  let ms_per_day := .prim (.bitvec (Int64.toBitVec 86400000))
  let dt_val := ext.datetime.val dt
  (ite (bvsle zero dt_val)
    (someOf (ext.datetime.ofBitVec (bvmul ms_per_day (bvsdiv dt_val ms_per_day))))
    (ite (eq (bvsrem dt_val ms_per_day) zero)
      (someOf dt)
      (ifFalse (bvsmulo (bvsub (bvsdiv dt_val ms_per_day) one) ms_per_day)
        (ext.datetime.ofBitVec (bvmul (bvsub (bvsdiv dt_val ms_per_day) one) ms_per_day))
      )
    )
  )

def toTime (dt : Term) : Term :=
  let zero := .prim (.bitvec (Int64.toBitVec 0))
  let ms_per_day := .prim (.bitvec (Int64.toBitVec 86400000))
  let dt_val := ext.datetime.val dt
  ext.duration.ofBitVec
    (ite (bvsle zero dt_val)
      (bvsrem dt_val ms_per_day)
      (ite (eq (bvsrem dt_val ms_per_day) zero)
        zero
        (bvadd (bvsrem dt_val ms_per_day) ms_per_day)
      )
    )

end Datetime

end Cedar.SymCC
