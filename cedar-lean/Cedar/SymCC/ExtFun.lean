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

import Cedar.SymCC.Env
public import Cedar.SymCC.Factory -- TODO: this need not be a public import

/-!

This file contains the symbolic encoding (factory functions) for extension
operators.

The extension functions are total. If given well-formed and type-correct
arguments, an extension function will return a well-formed and type-correct
output. Otherwise, the output is an arbitrary term.

This design lets us minimize the number of error paths in the overall
specification of symbolic compilation, which makes for nicer code and proofs, and
it more closely tracks the specification of the concrete evaluator.

See `Compiler.lean` to see how the symbolic compiler uses this API. See also
`Factory.lean`.

-/

@[expose] public section -- TODO: make the public interface more granular/intentional, instead of having everything public and exposed

namespace Cedar.SymCC

open Cedar.Data
open Cedar.Spec
open Factory Batteries

namespace Decimal

public def lessThan (t₁ t₂ : Term) : Term :=
  bvslt (ext.decimal.val t₁) (ext.decimal.val t₂)

public def lessThanOrEqual (t₁ t₂ : Term) : Term :=
  bvsle (ext.decimal.val t₁) (ext.decimal.val t₂)

public def greaterThan (t₁ t₂ : Term) : Term :=
  lessThan t₂ t₁

public def greaterThanOrEqual (t₁ t₂ : Term) : Term :=
  lessThanOrEqual t₂ t₁

end Decimal

namespace IPAddr
open BitVec

public def isIpv4 (t : Term) : Term :=
  ext.ipaddr.isV4 t

public def isIpv6 (t : Term) : Term :=
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

public def isInRange (t₁ t₂ : Term) : Term :=
  (or
    (inRangeV isIpv4 rangeV4 t₁ t₂)
    (inRangeV isIpv6 rangeV6 t₁ t₂))

def ipTerm (ip : IPAddr) : Term := (.prim (.ext (.ipaddr ip)))

def inRangeLit (t : Term) (cidr₄ : Ext.IPAddr.CIDR Ext.IPAddr.V4_WIDTH) (cidr₆ : Ext.IPAddr.CIDR Ext.IPAddr.V6_WIDTH) : Term :=
  (ite
    (isIpv4 t)
    (inRange rangeV4 t (ipTerm (Ext.IPAddr.IPNet.V4 cidr₄)))
    (inRange rangeV6 t (ipTerm (Ext.IPAddr.IPNet.V6 cidr₆))))

public def isLoopback (t : Term) : Term :=
  inRangeLit t Ext.IPAddr.LOOP_BACK_CIDR_V4 Ext.IPAddr.LOOP_BACK_CIDR_V6

public def isMulticast (t : Term) : Term :=
  inRangeLit t Ext.IPAddr.MULTICAST_CIDR_V4 Ext.IPAddr.MULTICAST_CIDR_V6

end IPAddr

namespace Duration

public def toMilliseconds (t : Term) : Term := ext.duration.val t

public def toSeconds (t : Term) : Term :=
  bvsdiv (toMilliseconds t) (.prim (.bitvec (Int64.toBitVec 1000)))

public def toMinutes (t : Term) : Term :=
  bvsdiv (toSeconds t) (.prim (.bitvec (Int64.toBitVec 60)))

public def toHours (t : Term) : Term :=
  bvsdiv (toMinutes t) (.prim (.bitvec (Int64.toBitVec 60)))

public def toDays (t : Term) : Term :=
  bvsdiv (toHours t) (.prim (.bitvec (Int64.toBitVec 24)))

end Duration

namespace Datetime

public def offset (dt dur : Term) : Term :=
  let dt_val := ext.datetime.val dt
  let dur_val := ext.duration.val dur
  ifFalse (bvsaddo dt_val dur_val) (ext.datetime.ofBitVec (bvadd dt_val dur_val))

public def durationSince (dt₁ dt₂ : Term) : Term :=
  let dt₁_val := ext.datetime.val dt₁
  let dt₂_val := ext.datetime.val dt₂
  ifFalse (bvssubo dt₁_val dt₂_val) (ext.duration.ofBitVec (bvsub dt₁_val dt₂_val))

public def toDate (dt : Term) : Term :=
  let ms_per_day := .prim (.bitvec (Int64.toBitVec 86400000))
  let dt_val := ext.datetime.val dt
  -- we want dt - (dt % MS_PER_DAY), with the right version of '%'
  -- using bvsmod does the right thing: we have 0 <= (bvsmod x MS_PER_DAY) < MS_PER_DAY
  let rem := bvsmod dt_val ms_per_day
  ifFalse (bvssubo dt_val rem) (ext.datetime.ofBitVec (bvsub dt_val rem))

public def toTime (dt : Term) : Term :=
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
