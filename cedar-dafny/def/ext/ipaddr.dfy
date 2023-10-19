/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

include "../base.dfy"
include "fun.dfy"
include "parser.dfy"

// IpAdddr extension type
module def.ext.ipaddr {
  import opened base
  import opened fun
  import opened core
  import opened parseIPAddr

  type IPAddr = core.IPNet

  type Coercions<!T(==,!new)> = fun.Coercions<IPAddr, T>

  datatype IPAddrFunctions<!T(==,!new)> = IPAddrFunctions(coerce: Coercions<T>)
  {

    // Returns the map from IPAddr extension function names to their implementations.
    static function register(coerce: Coercions<T>): map<Name, ExtFun<T>>
    {
      var fns := IPAddrFunctions(coerce);
      map[
        Name.fromStr("ip")          := ExtFun(fns.ip),
        Name.fromStr("isIpv4")      := ExtFun(fns.isIpv4),
        Name.fromStr("isIpv6")      := ExtFun(fns.isIpv6),
        Name.fromStr("isLoopback")  := ExtFun(fns.isLoopback),
        Name.fromStr("isMulticast") := ExtFun(fns.isMulticast),
        Name.fromStr("isInRange")   := ExtFun(fns.isInRange)
      ]
    }

    function ip(args: seq<T>): Result<T> {
      var s :- checkUnary(args, coerce.String);
      match parse(s) {
        case Some(ip) => Ok(coerce.fromExt(ip))
        case None => Err(ExtensionError)
      }
    }

    function isIpv4(args: seq<T>): Result<T> {
      var ip :- checkUnary(args, coerce.Ext);
      Ok(coerce.fromBool(ip.isV4()))
    }

    function isIpv6(args: seq<T>): Result<T> {
      var ip :- checkUnary(args, coerce.Ext);
      Ok(coerce.fromBool(ip.isV6()))
    }

    function isLoopback(args: seq<T>): Result<T> {
      var ip :- checkUnary(args, coerce.Ext);
      Ok(coerce.fromBool(ip.isLoopback()))
    }

    function isMulticast(args: seq<T>): Result<T> {
      var ip :- checkUnary(args, coerce.Ext);
      Ok(coerce.fromBool(ip.isMulticast()))
    }

    function isInRange(args: seq<T>): Result<T> {
      var (ip0, ip1) :- checkBinary(args, coerce.Ext);
      Ok(coerce.fromBool(ip0.inRange(ip1)))
    }
  }
}

module def.ext.ipaddr.core {
  // The 16 bit number in each group of IPv6 addresses
  newtype numV6 = x: nat | x <= 0xffff
  // The 8 bit number in each group of IPv4 addresses
  newtype numV4 = x: nat | x <= 0xff

  // The network address bit width
  const V6_SIZE := 128
  const V4_SIZE := 32
  newtype prefixV6 = x: nat | x <= V6_SIZE
  newtype prefixV4 = x: nat | x <= V4_SIZE

  // Normalized address space because we support IPv4 and IPv6 address comparison
  // newtype u128 = i: nat | i < 0x1_0000_0000_0000_0000_0000_0000_0000_0000
  type u128 = nat
  type Value = u128

  // Constants
  const LOOP_BACK_ADDRESS_V4 := IPv4Addr.Addr(127, 0, 0, 0)
  const LOOP_BACK_NET_V4 := V4(LOOP_BACK_ADDRESS_V4, 8)
  const LOOP_BACK_ADDRESS_V6 := IPv6Addr.Addr(0, 0, 0, 0, 0, 0, 0, 1)
  const LOOP_BACK_NET_V6 := V6(LOOP_BACK_ADDRESS_V6, 128)
  const MULTICAST_ADDRESS_V4 := IPv4Addr.Addr(224, 0, 0, 0)
  const MULTICAST_NET_V4 := V4(MULTICAST_ADDRESS_V4, 4)
  const MULTICAST_ADDRESS_V6 := IPv6Addr.Addr(65280, 0, 0, 0, 0, 0, 0, 0)
  const MULTICAST_NET_V6 := V6(MULTICAST_ADDRESS_V6, 8)

  // IPv4 address: a 32 bit number partitioned into 4 groups.
  // a0 is most signifcant and a3 is the least significant.
  // In other words, the number represented is a0++a1++a2++a3
  datatype IPv4Addr =
    Addr(
      a0: numV4,
      a1: numV4,
      a2: numV4,
      a3: numV4
    ) {
    function getAddrValue(): Value {
      ((a0 as nat)*0x100_0000 +
      (a1 as nat)*0x1_0000 +
      (a2 as nat)*0x100 +
      (a3 as nat)) as u128
    }
  }

  // TODO: prove getaddrValue . valueToIPv4Addr == id
  function valueToIPv4Addr(v: Value): IPv4Addr {
    var a3:= (v % 0x100) as numV4;
    var a2 := ((v / 0x100) % 0x100) as numV4;
    var a1 := ((v / 0x1_0000) % 0x100) as numV4;
    var a0 := ((v / 0x100_0000) % 0x100) as numV4;
    IPv4Addr.Addr(a0, a1, a2, a3)
  }

  // IPv6 address: a 128 bit number partitioned into 8 groups
  // a0 is most signifcant and a7 is the least significant.
  // In other words, the number represented is a0++a1++a2++a3++a4++a5++a6++a7
  datatype IPv6Addr =
    Addr(
      a0: numV6,
      a1: numV6,
      a2: numV6,
      a3: numV6,
      a4: numV6,
      a5: numV6,
      a6: numV6,
      a7: numV6
    ) {
    function getAddrValue(): Value {
      ((a0 as nat)*0x1_0000_0000_0000_0000_0000_0000_0000 +
      (a1 as nat)*0x1_0000_0000_0000_0000_0000_0000 +
      (a2 as nat)*0x1_0000_0000_0000_0000_0000 +
      (a3 as nat)*0x1_0000_0000_0000_0000 +
      (a4 as nat)*0x1_0000_0000_0000 +
      (a5 as nat)*0x1_0000_0000 +
      (a6 as nat)*0x1_0000 +
      (a7 as nat)) as u128
    }
  }

  // TODO: prove getaddrValue . valueToIPv4Addr == id
  function valueToIPv6Addr(v: Value): IPv6Addr {
    var a7 := (v % 0x1_0000) as numV6;
    var a6 := ((v / 0x1_0000) % 0x1_0000) as numV6;
    var a5 := ((v / 0x1_0000_0000) % 0x1_0000) as numV6;
    var a4 := ((v / 0x1_0000_0000_0000) % 0x1_0000) as numV6;
    var a3 := ((v / 0x1_0000_0000_0000_0000) % 0x1_0000) as numV6;
    var a2 := ((v / 0x1_0000_0000_0000_0000_0000) % 0x1_0000) as numV6;
    var a1 := ((v / 0x1_0000_0000_0000_0000_0000_0000) % 0x1_0000) as numV6;
    var a0 := ((v / 0x1_0000_0000_0000_0000_0000_0000_0000) % 0x1_0000) as numV6;
    IPv6Addr.Addr(a0, a1, a2, a3, a4, a5, a6, a7)
  }

  datatype IPNet =
    V6(addrV6: IPv6Addr, v6Prefix: prefixV6) |
    V4(addrV4: IPv4Addr, v4Prefix: prefixV4) {
    function normalize(): IPNet {
      var v := this.applySubnetMask();
      match this {
        case V6(addr, prefix) => V6(valueToIPv6Addr(v), prefix)
        case V4(addr, prefix) => V4(valueToIPv4Addr(v), prefix)
      }
    }

    predicate isV4() {
      V4?
    }

    predicate isV6() {
      V6?
    }

    function getAddrValue(): Value {
      match this {
        case V6(addr, _) => addr.getAddrValue()
        case V4(addr, _) => addr.getAddrValue()
      }
    }

    function getSubnetBitWidth(): nat {
      if V6? then V6_SIZE - v6Prefix as nat else V4_SIZE - v4Prefix as nat
    }

    // Getting the last n bits of a number x amounts to x >> n << n.
    // (>> n) amounts to (/Powerof2(n)) and
    // (<< n) amounts to (*Powerof2(n))
    function applySubnetMask(): Value {
      var offset := powerOf2(getSubnetBitWidth()) as u128;
      ((getAddrValue()/ offset) * offset) as u128
    }

    // i.e., 1 << n
    function getSubnetSize(): Value {
      powerOf2(getSubnetBitWidth()) as u128
    }

    predicate inRange(other: IPNet) {
      match (this, other) {
        case (V4(_, _), V6(_, _)) => false
        case (V6(_, _), V4(_, _)) => false
        case _ =>
          // lower value of the range
          var tl := applySubnetMask();
          // higher value of the range
          var th := tl + getSubnetSize() - 1;
          // Likewise, values of the range other represents
          var ol := other.applySubnetMask();
          var oh := ol + other.getSubnetSize() - 1;
          // Interval inclusion test
          oh >= th && tl >= ol
      }
    }

    predicate isLoopback() {
      if V6? then inRange(LOOP_BACK_NET_V6) else inRange(LOOP_BACK_NET_V4)
    }

    predicate isMulticast() {
      if V6? then inRange(MULTICAST_NET_V6) else inRange(MULTICAST_NET_V4)
    }
  }

  function {:opaque} powerOf2(x: nat): (res: nat)
    ensures res >= 1
  {
    if x == 0 then 1 else 2*powerOf2(x - 1)
  }
}

module def.ext.ipaddr.parseIPAddr {
  import opened utils.parser
  import opened std
  import opened core

  export
    provides
      parse,
      std,
      core

  // A segment of IPv6 address is either a 16 bit number or a "::"
  datatype SegV6 = Num(n: numV6) | DC

  function parseDot(s: string): (res: Option<string>)
  {
    ParseChar('.', s)
  }

  function parseColon(s: string): (res: Option<string>)
  {
    ParseChar(':', s)
  }

  function parseSlash(s: string): (res: Option<string>)
  {
    ParseChar('/', s)
  }

  function parseCIDRV4(s: string): (res: Option<(nat, string)>)
    ensures res.Some? ==> res.value.0 <= V4_SIZE
  {
    var ns :- parseSlash(s);
    match ParseDecStr(ns) {
      case Some((ds, ns')) =>
        if 0 < |ds| <= 2
        then
          var n := DecStrToNat(ds);
          if n <= V4_SIZE then
            Some((n, ns'))
          else None
        else None
      case None => None
    }
  }

  // Parse a group of number in strict dotted decimal format
  function parseNumV4(s: string): (res: Option<(numV4, string)>)
  {
    match ParseDecStr(s) {
      case Some((ds, ns)) =>
        if 0 < |ds| <= 3
        then
          var n := DecStrToNat(ds);
          if n <= 0xff then
            // Reference: https://github.com/rust-lang/rust/pull/86984
            if ds[0] == '0' ==> (|ds| == 1 && n == 0) then
              Some((n as numV4, ns))
            else None
          else None
        else None
      case None => None
    }
  }

  function parseSegsV4(s: string): (res: Option<(seq<numV4>, string)>)
    ensures res.Some? ==> |res.value.0| == 4
  {
    var (n0, s1_) :- parseNumV4(s);
    var s1   :- parseDot(s1_);
    var (n1, s2_) :- parseNumV4(s1);
    var s2   :- parseDot(s2_);
    var (n2, s3_) :- parseNumV4(s2);
    var s3  :- parseDot(s3_);
    var (n3, s4_) :- parseNumV4(s3);
    Some(([n0, n1, n2, n3], s4_))
  }

  function parseIPv4Net(s: string): (res: Option<IPNet>)
  {
    var (ds, ns) :- parseSegsV4(s);
    match EoS(ns) {
      case Some(_) => Some(V4(IPv4Addr.Addr(ds[0], ds[1], ds[2], ds[3]), V4_SIZE as prefixV4))
      case None =>
        var (sn, ns') :- parseCIDRV4(ns);
        var _ :- EoS(ns');
        Some(V4(IPv4Addr.Addr(ds[0], ds[1], ds[2], ds[3]), sn as prefixV4))
    }
  }

  function parseNumV6(s: string): (res: Option<(numV6, string)>)
  {
    match ParseHexStr(s) {
      case Some((ds, ns)) =>
        if 0 < |ds| <= 4 then
          HexPowerMonotonic(|ds|, 4);
          Some((HexStrToNat(ds) as numV6, ns))
        else None
      case None => None
    }
  }

  // Parse (":" digits)+
  function parseNumSegsV6'(s: string): Option<(seq<numV6>, string)>
    decreases |s|
  {
    if |s| == 0 then None
    else
      match parseColon(s) {
        case Some(s') =>
          var (d, ns) :- parseNumV6(s');
          match parseNumSegsV6'(ns) {
            case Some((ds, ns')) => Some(([d]+ds, ns'))
            case None => Some(([d], ns))
          }
        case None => None
      }
  }

  // Parse digits (":" digits)+
  function parseNumSegsV6(s: string): Option<(seq<numV6>, string)>
  {
    var (d, ns) :- parseNumV6(s);
    match parseNumSegsV6'(ns) {
      case Some((ds, ns')) => Some(([d]+ds, ns'))
      case None => Some(([d], ns))
    }
  }

  function wrapNumSegs(ds: seq<numV6>): (res: seq<SegV6>)
    ensures |res| == |ds| && forall i | 0 <= i < |ds| :: res[i].Num? && res[i].n == ds[i]
  {
    if |ds| == 0 then []
    else [SegV6.Num(ds[0])] + wrapNumSegs(ds[1..])
  }

  ghost function countDC(s: seq<SegV6>): nat
  {
    if |s| == 0 then 0 else (if s[0].DC? then 1 else 0) + countDC(s[1..])
  }

  lemma WrapNumSegsNoDC(ds: seq<numV6>)
    ensures countDC(wrapNumSegs(ds)) == 0
  {}

  lemma Count0MeansNone(s: seq<SegV6>)
    ensures countDC(s) == 0 ==> forall i | 0 <= i < |s| :: s[i].Num?
  {
    if |s| == 0 {

    } else {
      Count0MeansNone(s[1..]);
    }
  }

  lemma CountDCLast(s: seq<numV6>)
    ensures countDC(wrapNumSegs(s)+[DC]) == 1
  {
    if |s| == 0 {

    } else {
      assert wrapNumSegs(s)+[DC] == wrapNumSegs([s[0]]) + (wrapNumSegs(s[1..]) + [DC]);
    }
  }

  lemma CountDCComp(l: seq<SegV6>, r: seq<SegV6>)
    ensures countDC(l+r) == countDC(l)+countDC(r)
  {
    if |l| == 0 {
      assert l + r == r;
    } else {
      assert l + r == [l[0]] + (l[1..] + r);
    }
  }

  lemma CountDCMid(l: seq<numV6>, r: seq<numV6>)
    ensures countDC(wrapNumSegs(l)+[DC]+wrapNumSegs(r)) == 1
  {
    CountDCLast(l);
    WrapNumSegsNoDC(r);
    CountDCComp(wrapNumSegs(l)+[DC], wrapNumSegs(r));
  }

  function parseSegsV6(s: string): (res: Option<(seq<SegV6>, string)>)
    ensures res.Some? ==> countDC(res.value.0) <= 1
    ensures res.Some? ==> |res.value.0| >= 1
  {
    if |s| >= 2 && s[..2] == "::" then
      match parseNumSegsV6(s[2..]) {
        case Some((ds, ns)) =>
          WrapNumSegsNoDC(ds);
          Some(([DC]+wrapNumSegs(ds), ns))
        case None =>
          Some(([DC], s[2..]))
      }
    else
      match parseNumSegsV6(s) {
        case Some((ds, ns)) =>
          if |ns| >= 2 && ns[..2] == "::" then
            match parseNumSegsV6(ns[2..]) {
              case Some((ds', ns')) =>
                CountDCMid(ds, ds');
                Some((wrapNumSegs(ds) + [DC] + wrapNumSegs(ds'), ns'))
              case None =>
                CountDCLast(ds);
                Some((wrapNumSegs(ds) + [DC], ns[2..]))
            }
          else
            WrapNumSegsNoDC(ds);
            Some((wrapNumSegs(ds), ns))
        case None => None
      }
  }

  function findDCIdx(segs: seq<SegV6>): (res: Option<nat>)
    ensures res.Some? ==> res.value < |segs|
    ensures res.Some? ==> segs[res.value].DC?
    ensures res.None? ==> forall i | 0 <= i < |segs| :: segs[i].Num?
  {
    if |segs| == 0
    then None
    else
      if segs[0].DC? then Some(0)
      else
        var idx :- findDCIdx(segs[1..]);
        Some(idx + 1)
  }

  lemma CountDC1SepMeansNoDc(segs: seq<SegV6>)
    requires countDC(segs) <= 1
    ensures findDCIdx(segs).Some? ==> countDC(segs[0..findDCIdx(segs).value]) == 0 && countDC(segs[findDCIdx(segs).value+1..]) == 0
  {
    var idx := findDCIdx(segs);
    if idx.None? {

    } else {
      assert segs == segs[0..idx.value+1] + segs[idx.value+1..];
      CountDCComp(segs[0..idx.value+1], segs[idx.value+1..]);
      assert countDC(segs[0..idx.value+1]) + countDC(segs[idx.value+1..]) == countDC(segs);
      assert segs[0..idx.value+1] == segs[0..idx.value] + [segs[idx.value]];
      CountDCComp(segs[0..idx.value], [segs[idx.value]]);
      assert countDC(segs[0..idx.value]) + countDC([segs[idx.value]]) == countDC(segs[0..idx.value+1]);
    }
  }

  function zeroSegs(n: nat): (res: seq<SegV6>)
    decreases n
    ensures |res| == n
    ensures forall i | 0 <= i < n :: res[i].Num? && res[i].n == 0
  {
    if n == 0 then [] else [SegV6.Num(0)] + zeroSegs(n - 1)
  }

  function tryExpandSegs(segs: seq<SegV6>): (res: Option<seq<SegV6>>)
    requires countDC(segs) <= 1
    ensures res.Some? ==> |res.value| == 8
    ensures res.Some? ==> forall i | 0 <= i < 8 :: res.value[i].Num?
  {
    if |segs| > 8
    then None
    else
      CountDC1SepMeansNoDc(segs);
      var dcIdx := findDCIdx(segs);
      match dcIdx {
        case Some(idx) =>
          Count0MeansNone(segs[..idx]);
          Count0MeansNone(segs[idx+1..]);
          Some(segs[..idx] + zeroSegs(8 - |segs| + 1) + segs[idx+1..])
        case None => if |segs| == 8 then Some(segs) else None
      }
  }

  function parseCIDRV6(s: string): (res: Option<(nat, string)>)
    ensures res.Some? ==> res.value.0 <= V6_SIZE
  {
    var ns :- parseSlash(s);
    match ParseDecStr(ns) {
      case Some((ds, ns')) =>
        if 0 < |ds| <= 3 then
          var n := DecStrToNat(ds);
          if n <= V6_SIZE then Some((n, ns'))
          else None
        else None
      case None => None
    }
  }

  function parseIPv6Net(s: string): Option<IPNet>
  {
    var (ds, ns) :- parseSegsV6(s);
    match(EoS(ns)) {
      case Some(_) =>
        var ds' :- tryExpandSegs(ds);
        Some(V6(IPv6Addr.Addr(ds'[0].n, ds'[1].n, ds'[2].n, ds'[3].n, ds'[4].n, ds'[5].n, ds'[6].n, ds'[7].n), V6_SIZE as prefixV6))
      case None =>
        var (sn, ns') :- parseCIDRV6(ns);
        var _ :- EoS(ns');
        var ds' :- tryExpandSegs(ds);
        Some(V6(IPv6Addr.Addr(ds'[0].n, ds'[1].n, ds'[2].n, ds'[3].n, ds'[4].n, ds'[5].n, ds'[6].n, ds'[7].n), sn as prefixV6))
    }
  }

  function parse(s: string): Option<IPNet>
  {
    // Is it V4?
    match parseIPv4Net(s) {
      case Some(ip) => Some(ip)
      case None =>
        // No. Is it V6?
        parseIPv6Net(s)
    }
  }
}
