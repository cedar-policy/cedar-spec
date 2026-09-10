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

import Cedar.Spec.Ext.IPAddr
import Cedar.Thm.Ext.IPAddr.Grammar
import UnitTest.Run

/-! # Grammar ⟺ parser agreement tests

Cross-validates the parser-independent IP grammar (`Cedar.Thm.Ext.IPAddr.Grammar`'s
`IsWfIPNet`, phrased as a `Prop` over component witnesses) against the actual parser
`IPAddr.ip`, on the acceptance/rejection ground truth of `UnitTest.IPAddr` plus adversarial
edge cases.

Since `IsWfIPNet` is an existential `Prop`, the check runs through `isWfIPNetB` — an
executable structural mirror that decomposes a string the same way a grammar witness must
render (`splitToList` on `'/'`, `'.'`, `':'`; `splitOn "::"`), checking the same
canonical-number / hex-group / group-count / prefix-bound side conditions. The eventual
decidability bridge `IsWfIPNet str ↔ isWfIPNetB str` is the proof obligation that will make
this mirror authoritative; until then this suite pins both the mirror and the parser to the
same vectors, so a drift in either shows up as a test failure.

Value agreement (`v4Value`/`v6Value` vs the parser's `IPNet`) is spot-checked on explicit
witnesses for representative forms (V4 bare/prefixed; V6 full, gap, empty-side gap). -/

namespace UnitTest.IPAddrGrammar

open Cedar.Spec.Ext.IPAddr
open Cedar.Thm.IPAddr

/-! ## Executable mirror of the grammar predicates -/

private def isHexDigitB (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- Mirror of `IsCanonicalNat`: nonempty digits, no leading zero unless exactly `"0"`. -/
private def isCanonicalNatB (s : String) : Bool :=
  0 < s.length && s.toList.all (·.isDigit) && (s.toList.head? != some '0' || s == "0")

/-- Mirror of `IsHexGroup`: 1–4 hex digits. -/
private def isHexGroupB (s : String) : Bool :=
  0 < s.length && s.length ≤ 4 && s.toList.all isHexDigitB

/-- Mirror of `IsWfV4`: `g.g.g.g[/p]` with canonical ≤3-digit groups ≤255 and canonical
    ≤2-digit prefix ≤32. -/
private def isWfV4B (str : String) : Bool :=
  match str.splitToList (· = '/') with
  | [addr] => wfAddr addr
  | [addr, p] => wfAddr addr && isCanonicalNatB p && p.length ≤ 2 && numValue p ≤ 32
  | _ => false
  where wfAddr (addr : String) : Bool :=
    match addr.splitToList (· = '.') with
    | [g0, g1, g2, g3] =>
      [g0, g1, g2, g3].all (fun g => isCanonicalNatB g && g.length ≤ 3 && numValue g ≤ 255)
    | _ => false

/-- Mirror of `IsWfV6`: full 8-group form or one `::` with the sides totalling < 8 groups,
    all groups 1–4 hex digits; canonical ≤3-digit prefix ≤128. -/
private def isWfV6B (str : String) : Bool :=
  match str.splitToList (· = '/') with
  | [addr] => wfAddr addr
  | [addr, p] => wfAddr addr && isCanonicalNatB p && p.length ≤ 3 && numValue p ≤ 128
  | _ => false
  where
    sideGroups (s : String) : Option (List String) :=
      if s = "" then some [] else
      let gs := s.splitToList (· = ':')
      if gs.all (· ≠ "") then some gs else none
    wfAddr (addr : String) : Bool :=
      match addr.splitOn "::" with
      | [full] =>
        let gs := full.splitToList (· = ':')
        gs.length == 8 && gs.all isHexGroupB
      | [l, r] =>
        match sideGroups l, sideGroups r with
        | some ls, some rs => ls.length + rs.length < 8 && (ls ++ rs).all isHexGroupB
        | _, _ => false
      | _ => false

/-- Mirror of `IsWfIPNet`. -/
private def isWfIPNetB (str : String) : Bool := isWfV4B str || isWfV6B str

/-! ## Agreement suite: mirror ⟺ parser on the ground-truth vectors -/

/-- The mirror must agree with `(ip str).isSome` on every vector. -/
private def testAgree (str : String) : TestCase IO :=
  test s!"grammar ⟺ parser on {str}" ⟨λ _ => checkEq (isWfIPNetB str) (ip str).isSome⟩

/-- All acceptance/rejection vectors from `UnitTest.IPAddr`, plus adversarial edges:
    whitespace, unicode digits, `+`/`_`/`0x` notations, an exactly-8-sided gap, a double
    slash, an 8-group string with a stray `::`, and hex groups with leading zeros. -/
private def vectors : List String := [
  -- valid (from testsForValidStrings + the toString tests)
  "127.0.0.1", "127.3.4.1/2", "::", "::/5", "a::", "::f", "F:AE::F:5:F:F:0", "a::f/120",
  "192.168.0.1/32", "0.0.0.0/1", "8.8.8.8/24", "1:2:3:4:a:b:c:d/128",
  "1:22:333:4444:a:bb:ccc:dddd/128", "7:70:700:7000::a00/128", "::ffff/128", "ffff::/4",
  -- invalid (from testsForInvalidStrings)
  "127.0.0.1.", ".127.0.0.1", "127.0..0.1", "256.0.0.1", "127.0.a.1", "127.3.4.1/33",
  "::::", "::f::", "F:AE::F:5:F:F:0:0", "F:A:F:5:F:F:0:0:1", "F:A", "::ffff1",
  "F:AE::F:5:F:F:0/129", "::ffff:127.0.0.1", "::/00", "::/01", "::/001",
  "127.0.0.1/01", "F:AE::F:5:F:F:0/01",
  -- adversarial edges
  "FfFf::", "00ff::", "0000::", " 127.0.0.1", "127.0.0.1 ", "+127.0.0.1", "١.0.0.1",
  "127.0.0.1/", "1:2:3:4:5:6:7:8/128/1", "1:2:3:4:5:6:7:8::", "::1:2:3:4:5:6:7:8",
  "1:2:3:4::5:6:7:8", "0x1f::", "1_2.0.0.1", "12_::"
]

def testsForGrammarParserAgreement :=
  suite "IPAddr grammar ⟺ parser agreement" (vectors.map testAgree)

/-! ## Value agreement: grammar witnesses' `v4Value`/`v6Value` vs the parser's `IPNet` -/

private def testValue (str : String) (expected : Cedar.Spec.Ext.IPAddr.IPNet) : TestCase IO :=
  test s!"value of {str}" ⟨λ _ => checkEq (ip str) (some expected)⟩

def testsForValueAgreement :=
  suite "IPAddr grammar value ⟺ parser value"
  [
    testValue "127.0.0.1" (v4Value ⟨"127", "0", "0", "1"⟩ none),
    testValue "127.3.4.1/2" (v4Value ⟨"127", "3", "4", "1"⟩ (some "2")),
    testValue "1:2:3:4:a:b:c:d/128"
      (v6Value (.full ["1", "2", "3", "4", "a", "b", "c", "d"]) (some "128")),
    testValue "::" (v6Value (.gap [] []) none),
    testValue "a::" (v6Value (.gap ["a"] []) none),
    testValue "::f" (v6Value (.gap [] ["f"]) none),
    testValue "F:AE::F:5:F:F:0" (v6Value (.gap ["F", "AE"] ["F", "5", "F", "F", "0"]) none),
    testValue "a::f/120" (v6Value (.gap ["a"] ["f"]) (some "120")),
    testValue "7:70:700:7000::a00/128"
      (v6Value (.gap ["7", "70", "700", "7000"] ["a00"]) (some "128"))
  ]

def tests := [testsForGrammarParserAgreement, testsForValueAgreement]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.IPAddrGrammar
