include "../std.dfy"

module def.ext.utils.parser {
  import opened std

  function ParseChar(c: char, s: string): (res: Option<(string)>)
  {
    if |s| == 0 then None
    else if s[0] == c
    then Some(s[1..])
    else None
  }

  function EoS(s: string): (res: Option<()>)
  {
    if |s| == 0 then Some(()) else None
  }

  function ParseDigits(s: string, pred: char -> bool): (res: Option<(string, string)>)
    ensures res.Some? ==> |res.value.1| <= |s|
    ensures res.Some? ==> |res.value.0| > 0 && forall i | 0 <= i < |res.value.  0| :: pred(res.value.0[i])
  {
    if |s| == 0 then None
    else if pred(s[0])
    then
      match ParseDigits(s[1..], pred) {
        case Some((ns, r)) => Some(([s[0]]+ns, r))
        case None => Some(([s[0]], s[1..]))
      }
    else None
  }

  predicate IsHexDigit(x: char)
  {
    '0' <= x <= '9' || 'a' <= x <= 'f' || 'A' <= x <= 'F'
  }

  predicate IsDecDigit(x: char)
  {
    '0' <= x <= '9'
  }

  function ParseHexStr(s: string): (res: Option<(string, string)>)
    ensures res.Some? ==> |res.value.1| <= |s|
    ensures res.Some? ==> |res.value.0| > 0 && forall i | 0 <= i < |res.value.0| :: IsHexDigit(res.value.0[i])
  {
    ParseDigits(s, IsHexDigit)
  }

  function ParseDecStr(s: string): (res: Option<(string, string)>)
    ensures res.Some? ==> |res.value.1| <= |s|
    ensures res.Some? ==> |res.value.0| > 0 && forall i | 0 <= i < |res.value.0| :: IsDecDigit(res.value.0[i])
  {
    ParseDigits(s, IsDecDigit)
  }

  ghost function HexPowerOf(n: nat): nat
    decreases n
  {
    match n {
      case 0 => 1
      case _ => 16*HexPowerOf(n-1)
    }
  }
  lemma HexPowerMonotonic(n1: nat, n2: nat)
    ensures n1 < n2 ==> HexPowerOf(n1) < HexPowerOf(n2)
  {
  }

  function HexStrToNat(s: string): (res: nat)
    requires |s| > 0 && forall i | 0 <= i < |s| :: IsHexDigit(s[i])
    ensures res < HexPowerOf(|s|)
  {
    var ld := s[|s| - 1];
    var lo :=
      if 'a' <= ld <= 'f'
      then (ld - 'a') as nat + 10
      else if 'A' <= ld <= 'F'
        then (ld - 'A') as nat + 10
        else (ld - '0') as nat;
    if |s| == 1
    then lo
    else lo + 16 * HexStrToNat(s[0..|s| - 1])
  }

  function DecStrToNat(s: string): nat
    requires |s| > 0 && forall i | 0 <= i < |s| :: IsDecDigit(s[i])
  {
    var lo := (s[|s| - 1] - '0') as nat;
    if |s| == 1
    then lo
    else lo + 10 * DecStrToNat(s[0..|s| - 1])
  }

  lemma ParseDigitsAll(s: string, pred: char -> bool)
    requires |s| > 0
    requires forall i | 0 <= i < |s| :: pred(s[i])
    ensures ParseDigits(s, pred).Some? && ParseDigits(s, pred).value.0 == s && |ParseDigits(s, pred).value.1| == 0
  {}

  lemma ParseDecAll(s: string)
    requires |s| > 0
    requires forall i | 0 <= i < |s| :: IsDecDigit(s[i])
    ensures ParseDecStr(s).Some? && ParseDecStr(s).value.0 == s && |ParseDecStr(s).value.1| == 0
  {
    ParseDigitsAll(s, IsDecDigit);
  }
}
