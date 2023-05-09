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

// Decimal extension type
module def.ext.decimal {
  import opened base
  import opened fun
  import opened core
  import opened parseDecimal

  type Decimal = core.Decimal

  type Coercions<!T(==,!new)> = fun.Coercions<Decimal, T>

  datatype DecimalFunctions<!T(==,!new)> = DecimalFunctions(coerce: Coercions<T>)
  {

    // Returns the map from Decimal extension function names to their implementations.
    static function register(coerce: Coercions<T>): map<Name, ExtFun<T>>
    {
      var fns := DecimalFunctions(coerce);
      map[
        Name.fromStr("decimal")             := ExtFun(fns.decimal),
        Name.fromStr("lessThan")            := ExtFun(fns.lt),
        Name.fromStr("lessThanOrEqual")     := ExtFun(fns.lte),
        Name.fromStr("greaterThan")         := ExtFun(fns.gt),
        Name.fromStr("greaterThanOrEqual")  := ExtFun(fns.gte)
      ]
    }

    function decimal(args: seq<T>): Result<T> {
      var s :- checkUnary(args, coerce.String);
      match Parse(s) {
        case Some(d) => Ok(coerce.fromExt(d))
        case None => Err(ExtensionError)
      }
    }

    function lt(args: seq<T>): Result<T> {
      var (d0, d1) :- checkBinary(args, coerce.Ext);
      Ok(coerce.fromBool(d0.i < d1.i))
    }

    function lte(args: seq<T>): Result<T> {
      var (d0, d1) :- checkBinary(args, coerce.Ext);
      Ok(coerce.fromBool(d0.i <= d1.i))
    }

    function gt(args: seq<T>): Result<T> {
      var (d0, d1) :- checkBinary(args, coerce.Ext);
      Ok(coerce.fromBool(d0.i > d1.i))
    }

    function gte(args: seq<T>): Result<T> {
      var (d0, d1) :- checkBinary(args, coerce.Ext);
      Ok(coerce.fromBool(d0.i >= d1.i))
    }
  }
}

module def.ext.decimal.core {
  // A decimal number consists of an integer part and a fractional part.
  // The former is the integer number before the decimal point.
  // The latter is the decimal number minus its integer part.
  // For instance, 10.234 is a decimal number. Its integer part is 10 and its fractional part is 0.234
  // We restrict the number of the digits after the decimal point to 4.

  const DIGITS := 4
  const i64_MIN := -0x8000_0000_0000_0000
  const i64_MAX := 0x7fff_ffff_ffff_ffff
  // The internal representation of a decimal
  newtype i64 = i: int | i64_MIN <= i <= i64_MAX
  datatype Decimal = Decimal(i: i64)
}

module def.ext.decimal.parseDecimal {
  import opened utils.parser
  import opened std
  import opened core
  export
    provides
      Parse,
      std,
      core

  function ParseComponents(s: string): Option<(string, string)>
  {
    var (ls, r) :- ParseDecStr(s);
    var rr :- ParseChar('.', r);
    var (rs, rrr) :- ParseDecStr(rr);
    var _ :- EoS(rrr);
    if 0 < |rs| <= DIGITS
    then Some((ls, rs))
    else None
  }

  function FillZeros(n: nat, zs: nat): nat {
    if zs == 0 then n else 10 * FillZeros(n, zs - 1)
  }

  function ParseNat(s: string): Option<nat> {
    var (ls, rs) :- ParseComponents(s);
    var i := FillZeros(DecStrToNat(ls+rs), DIGITS - |rs|);
    Some(i)
  }

  function Parse(s: string): Option<Decimal> {
    match ParseChar('-', s) {
      case Some(s') =>
        var n :- ParseNat(s');
        var i := -(n as int);
        if i < i64_MIN then None else Some(Decimal.Decimal(i as i64))
      case None =>
        var n :- ParseNat(s);
        var i := n as int;
        if i > i64_MAX then None else Some(Decimal.Decimal(i as i64))
    }
  }

  lemma ParseDigitsAndDot(s1: string, s2: string)
    requires |s1| > 0
    requires forall i | 0 <= i < |s1| :: '0' <= s1[i] <= '9'
    ensures ParseDecStr(s1+"."+s2).Some? && ParseDecStr(s1+"."+s2).value.0 == s1 && ParseDecStr(s1+"."+s2).value.1 == "."+s2
  {
    if |s1| == 1 {
      assert (s1+"."+s2)[1..] == "."+s2;
      assert ParseDecStr("."+s2).None?;
    } else {
      ParseDecAll(s1);
      ParseDigitsAndDot(s1[1..],s2);
      assert s1+"."+s2 == [s1[0]]+(s1[1..]+"."+s2);
    }
  }

  lemma ParsePosNumStr(l: string, r: string)
    requires |l| > 0
    requires forall i | 0 <= i < |l| :: '0' <= l[i] <= '9'
    requires |r| > 0
    requires forall i | 0 <= i < |r| :: '0' <= r[i] <= '9'
    requires 0 < |r| <= DIGITS
    ensures ParseComponents(l+"."+r).Some? && ParseComponents(l+"."+r).value.0 == l && ParseComponents(l+"."+r).value.1 == r
  {
    ParseDecAll(l);
    ParseDecAll(r);
    ParseDigitsAndDot(l,r);
  }
}
