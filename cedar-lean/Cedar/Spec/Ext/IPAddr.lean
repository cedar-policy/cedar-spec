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

/-! This file defines Cedar IpAddr values and functions. -/

namespace Cedar.Spec.Ext

namespace IPAddr

----- UInt128 -----

-- Type of 128-bit unsigned numbers: 0 <= n < 2^128.
abbrev UInt128 := Fin 0x100000000000000000000000000000000

def UInt128.ofNat (n : Nat) : UInt128 := Fin.ofNat n

instance : Coe UInt128 Nat where
  coe n := n.1

instance : Coe Nat UInt128 where
  coe n := Fin.ofNat n

instance : Coe UInt8 Nat where
  coe n := n.toNat

instance : Coe UInt16 Nat where
  coe n := n.toNat

instance : Coe UInt32 Nat where
  coe n := n.toNat

instance : Coe Nat UInt32 where
  coe n := UInt32.ofNat n

----- IPv4Addr and IPv6Addr -----

/--
IPv4 address: a 32 bit number partitioned into 4 groups. a0 is most signifcant
and a3 is the least significant. In other words, the number represented is
a0++a1++a2++a3
--/
abbrev IPv4Addr := UInt32

def IPv4Addr.toUInt128 (ip4 : IPv4Addr) : UInt128 := UInt128.ofNat ip4.toNat

def UInt128.toIPv4Addr (bits : UInt128) : IPv4Addr := UInt32.ofNat bits

def IPv4Addr.mk (a₀ a₁ a₂ a₃ : UInt8) : IPv4Addr :=
  (a₀ : Nat) <<< 24 |||
  (a₁ : Nat) <<< 16 |||
  (a₂ : Nat) <<<  8 |||
  (a₃ : Nat)

/--
IPv6 address: a 128 bit number partitioned into 8 groups. a0 is most signifcant
and a7 is the least significant. In other words, the number represented is
a0++a1++a2++a3++a4++a5++a6++a7
--/
abbrev IPv6Addr := UInt128

def IPv6Addr.toUInt128 (ip6 : IPv6Addr) : UInt128 := ip6

def UInt128.toIPv6Addr (bits : UInt128) : IPv6Addr := bits

def IPv6Addr.mk (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : UInt16) : IPv6Addr :=
  (a₀ : Nat) <<< 112 |||
  (a₁ : Nat) <<<  96 |||
  (a₂ : Nat) <<<  80 |||
  (a₃ : Nat) <<<  64 |||
  (a₄ : Nat) <<<  48 |||
  (a₅ : Nat) <<<  32 |||
  (a₆ : Nat) <<<  16 |||
  (a₇ : Nat)

----- IPNet -----

def V4_SIZE := 32
abbrev Prefix4 := Fin (V4_SIZE + 1)

def V6_SIZE := 128
abbrev Prefix6 := Fin (V6_SIZE + 1)

inductive IPNet where
  | V4 (v4 : IPv4Addr) (prefix4 : Prefix4)
  | V6 (v6 : IPv6Addr) (prefix6 : Prefix6)

def IPNet.isV4 : IPNet → Bool
  | .V4 _ _ => true
  | _       => false

def IPNet.isV6 : IPNet → Bool
  | .V6 _ _ => true
  | _       => false

def IPNet.toUInt128 : IPNet → UInt128
  | .V4 v4 _ => v4.toUInt128
  | .V6 v6 _ => v6.toUInt128

def IPNet.subnetWidth : IPNet → UInt128
  | .V4 _ p4 => V4_SIZE - p4
  | .V6 _ p6 => V6_SIZE - p6

def IPNet.applySubnetMask (ip : IPNet) : UInt128 :=
  let width := ip.subnetWidth
  (ip.toUInt128 >>> width) <<< width

def IPNet.range (ip : IPNet) : UInt128 × UInt128 :=
  let lo := ip.applySubnetMask
  let hi := lo + (1 <<< ip.subnetWidth) - 1
  (lo, hi)

def IPNet.inRange : IPNet → IPNet → Bool
  | .V4 _ _, .V6 _ _ => false
  | .V6 _ _, .V4 _ _ => false
  | ip₁    , ip₂     =>
    let r₁ := ip₁.range
    let r₂ := ip₂.range
    r₂.2 ≥ r₁.2 && r₁.1 ≥ r₂.1

def LOOP_BACK_ADDRESS_V4 := IPv4Addr.mk 127 0 0 0
def LOOP_BACK_ADDRESS_V6 := IPv6Addr.mk 0 0 0 0 0 0 0 1
def LOOP_BACK_NET_V4     := IPNet.V4 LOOP_BACK_ADDRESS_V4 8
def LOOP_BACK_NET_V6     := IPNet.V6 LOOP_BACK_ADDRESS_V6 128

def MULTICAST_ADDRESS_V4 := IPv4Addr.mk 224 0 0 0
def MULTICAST_ADDRESS_V6 := IPv6Addr.mk 65280 0 0 0 0 0 0 0
def MULTICAST_NET_V4     := IPNet.V4 MULTICAST_ADDRESS_V4 4
def MULTICAST_NET_V6     := IPNet.V6 MULTICAST_ADDRESS_V6 8

def IPNet.isLoopback (ip : IPNet) : Bool :=
  ip.inRange (if ip.isV4 then LOOP_BACK_NET_V4 else LOOP_BACK_NET_V6)

def IPNet.isMulticast (ip : IPNet) : Bool :=
  ip.inRange (if ip.isV4 then MULTICAST_NET_V4 else MULTICAST_NET_V6)

def parseCIDR (str : String) (digits : Nat) (size : Nat) : Option (Fin (size + 1)) :=
  let len := str.length
  if 0 < len && len ≤ digits && (str.startsWith "0" → str = "0")
  then do
    let n ← str.toNat?
    if n ≤ size then .some (Fin.ofNat n) else .none
  else .none

def parseCIDRV4 (str : String) : Option Prefix4 := parseCIDR str 2 V4_SIZE

def parseCIDRV6 (str : String) : Option Prefix6 := parseCIDR str 3 V6_SIZE

def parseNumV4 (str : String) : Option UInt8 :=
  let len := str.length
  if 0 < len && len ≤ 3 && (str.startsWith "0" → str = "0")
  then do
    let n ← str.toNat?
    if n ≤ 0xff then .some (UInt8.ofNat n) else .none
  else .none

def parseSegsV4 (str : String) : Option IPv4Addr :=
  match str.split (· = '.') with
  | [s₀, s₁, s₂, s₃] => do
    let a₀ ← parseNumV4 s₀
    let a₁ ← parseNumV4 s₁
    let a₂ ← parseNumV4 s₂
    let a₃ ← parseNumV4 s₃
    .some (IPv4Addr.mk a₀ a₁ a₂ a₃)
  | _ => .none

def parseIPv4Net (str : String) : Option IPNet :=
  match str.split (· = '/') with
  | strV4 :: rest => do
    let pre ←
      match rest with
      | []       => .some (Fin.ofNat V4_SIZE)
      | [strPre] => parseCIDRV4 strPre
      | _        => .none
    let v4 ← parseSegsV4 strV4
    .some (IPNet.V4 v4 pre)
  | _ => .none

private def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

private def toHexNat (c : Char) : Nat :=
  if c.isDigit
  then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f'
  then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F'
  then c.toNat - 'A'.toNat + 10
  else c.toNat

def parseNumV6 (str : String) : Option UInt16 :=
  let len := str.length
  if 0 < len && len ≤ 4 && str.all isHexDigit
  then
    let n := str.foldl (fun n c => n * 16 + toHexNat c) 0
    if n ≤ 0xffff then .some (UInt16.ofNat n) else .none
  else .none

def parseNumSegsV6 (str : String) : Option (List UInt16) :=
  if str.isEmpty
  then .some []
  else (str.split (· = ':')).mapM parseNumV6

def parseSegsV6 (str : String) : Option IPv6Addr := do
  let segs ←
    match str.splitOn "::" with
    | [s₁] => parseNumSegsV6 s₁
    | [s₁, s₂] => do
      let ns₁ ← parseNumSegsV6 s₁
      let ns₂ ← parseNumSegsV6 s₂
      let len := ns₁.length + ns₂.length
      if len < 8
      then .some (ns₁ ++ (List.replicate (8 - len) 0) ++ ns₂)
      else .none
    | _ => .none
  match segs with
  | [a₀, a₁, a₂, a₃, a₄, a₅, a₆, a₇] =>
    .some (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇)
  | _ => .none

def parseIPv6Net (str : String) : Option IPNet :=
  match str.split (· = '/') with
  | strV6 :: rest => do
    let pre ←
      match rest with
      | []       => .some (Fin.ofNat V6_SIZE)
      | [strPre] => parseCIDRV6 strPre
      | _        => .none
    let v6 ← parseSegsV6 strV6
    .some (IPNet.V6 v6 pre)
  | _ => .none

def parse (str : String) : Option IPNet :=
  let ip := parseIPv4Net str
  if ip.isSome then ip else parseIPv6Net str

-- as of this writing, only handles nats up to 0xffff
def toHex (n : Nat) : String :=
  let a0 := hexDigitRepr ((n % 0x10000) / 0x1000)
  let a1 := hexDigitRepr ((n % 0x1000) / 0x100)
  let a2 := hexDigitRepr ((n % 0x100) / 0x10)
  let a3 := hexDigitRepr ((n % 0x10) / 0x1)
  s!"{a0}{a1}{a2}{a3}"

def unParse (ip : IPNet) : String :=
  match ip with
  | .V4 v p =>
    let a0 := (v >>> 24) &&& 0xFF
    let a1 := (v >>> 16) &&& 0xFF
    let a2 := (v >>> 8) &&& 0xFF
    let a3 := v &&& 0xFF
    s!"{a0}.{a1}.{a2}.{a3}/{p}"
  | .V6 v p =>
    let a0 := toHex ((v >>> 112) &&& 0xFFFF)
    let a1 := toHex ((v >>> 96) &&& 0xFFFF)
    let a2 := toHex ((v >>> 80) &&& 0xFFFF)
    let a3 := toHex ((v >>> 64) &&& 0xFFFF)
    let a4 := toHex ((v >>> 48) &&& 0xFFFF)
    let a5 := toHex ((v >>> 32) &&& 0xFFFF)
    let a6 := toHex ((v >>> 16) &&& 0xFFFF)
    let a7 := toHex (v &&& 0xFFFF)
    s!"{a0}:{a1}:{a2}:{a3}:{a4}:{a5}:{a6}:{a7}/{p}"

def ip (str : String) : Option IPNet := parse str

def IPNet.lt : IPNet → IPNet → Bool
  | .V4 _ _, .V6 _ _ => true
  | .V6 _ _, .V4 _ _ => false
  | .V4 v₁ p₁, .V4 v₂ p₂ => v₁.val < v₂.val || (v₁.val = v₂.val && p₁.val < p₂.val)
  | .V6 v₁ p₁, .V6 v₂ p₂ => v₁.val < v₂.val || (v₁.val = v₂.val && p₁.val < p₂.val)

----- IPNet deriviations -----

deriving instance Repr, DecidableEq, Inhabited for IPNet

instance : LT IPNet where
  lt := fun d₁ d₂ => IPNet.lt d₁ d₂

instance IPNet.decLt (d₁ d₂ : IPNet) : Decidable (d₁ < d₂) :=
if h : IPNet.lt d₁ d₂ then isTrue h else isFalse h

end IPAddr

end Cedar.Spec.Ext
