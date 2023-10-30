/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import UnitTest.Run

/-! This file defines unit tests for IPAddr functions. -/

namespace UnitTest.IPAddr

open Cedar.Spec.Ext.IPAddr

private def ipv4 (a₀ a₁ a₂ a₃ : UInt8) (pre : Nat) : IPNet :=
  IPNet.V4 (IPv4Addr.mk a₀ a₁ a₂ a₃) (Fin.ofNat pre)

private def ipv6 (a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇ : UInt16) (pre : Nat) : IPNet :=
  IPNet.V6 (IPv6Addr.mk a₀ a₁ a₂ a₃ a₄ a₅ a₆ a₇) (Fin.ofNat pre)

private def testValid (str : String) (ip : IPNet) : TestCase :=
  test str (checkEq (parse str) ip)

def testsForValidStrings :=
  suite "IPAddr.parse for valid strings"
  [
    testValid "127.0.0.1" (ipv4 127 0 0 1 V4_SIZE),
    testValid "127.3.4.1/2" (ipv4 127 3 4 1 2),
    testValid "::" (ipv6 0 0 0 0 0 0 0 0 V6_SIZE),
    testValid "::/5" (ipv6 0 0 0 0 0 0 0 0 5),
    testValid "a::" (ipv6 0xa 0 0 0 0 0 0 0 V6_SIZE),
    testValid "::f" (ipv6 0 0 0 0 0 0 0 0xf V6_SIZE),
    testValid "F:AE::F:5:F:F:0" (ipv6 0xf 0xae 0 0xf 0x5 0xf 0xf 0 V6_SIZE),
    testValid "a::f/120" (ipv6 0xa 0 0 0 0 0 0 0xf 120)
  ]

private def testInvalid (str : String) (msg : String) : TestCase :=
  test s!"{str} [{msg}]" (checkEq (parse str) .none)

def testsForInvalidStrings :=
  suite "IPAddr.parse for invalid strings"
  [
    testInvalid "127.0.0.1." "trailing dot",
    testInvalid ".127.0.0.1" "leading dot",
    testInvalid "127.0..0.1" "double dot",
    testInvalid "256.0.0.1" "group out of range",
    testInvalid "127.0.a.1" "no hex in IPv4",
    testInvalid "127.3.4.1/33" "prefix out of range",
    testInvalid "::::" "too many double colons",
    testInvalid "::f::" "too many double colons",
    testInvalid "F:AE::F:5:F:F:0:0" "too many groups",
    testInvalid "F:A:F:5:F:F:0:0:1" "too many groups",
    testInvalid "F:A" "too few groups",
    testInvalid "::ffff1" "group out of range",
    testInvalid "F:AE::F:5:F:F:0/129" "prefix out of range",
    testInvalid "::ffff:127.0.0.1" "no IPv4 embedded in IPv6",
    testInvalid "::/00" "no leading zeros",
    testInvalid "::/01" "no leading zeros",
    testInvalid "::/001" "no leading zeros",
    testInvalid "127.0.0.1/01" "no leading zeros",
    testInvalid "F:AE::F:5:F:F:0/01" "no leading zeros"
  ]

deriving instance Inhabited for IPNet

private def parse! (str : String) : IPNet :=
  match parse str with
  | .some ip => ip
  | .none => panic! s!"not a valid IP address {str}"


private def testIsLoopback (str : String) (expected : Bool) : TestCase :=
  test s!"isLoopback {str}" (checkEq (parse! str).isLoopback expected)

private def testToUInt128 (str : String) (expected : UInt128) : TestCase :=
  test s!"toUInt128 {str}" (checkEq (parse! str).toUInt128 expected)

def testsForIsLoopback :=
  suite "IPAddr.isLoopback"
  [
    testIsLoopback "127.0.0.1" true,
    testIsLoopback "::B" false,
    testIsLoopback "::1" true,
    -- As in Rust, IPv4 embedded in IPv6 only uses IPv6 loopback:
    testIsLoopback "::ffff:ff00:0001" false
  ]

def testsForUInt128Conversion :=
  suite "IPAddr.toUInt128"
  [
    testToUInt128 "192.0.2.235" 3221226219,
    testToUInt128 "::1:2" (0x10000 + 0x2)
  ]

def ip! (str : String) : IPNet :=
  match (ip str) with
  | .some ip => ip
  | .none => panic! s!"not a valid IP address {str}"

def testInRange (str₁ str₂ : String) (expected : Bool) : TestCase :=
  test s!"inRange {str₁} {str₂}" (checkEq ((ip! str₁).inRange (ip! str₂)) expected)

def testsForInRange :=
  suite "IPAddr.inRange"
  [
    testInRange "238.238.238.238" "238.238.238.41/12" true,
    testInRange "238.238.238.238" "238.238.238.238" true,
    testInRange "F:AE::F:5:F:F:0" "F:AE::F:5:F:F:0" true,
    testInRange "F:AE::F:5:F:F:1" "F:AE::F:5:F:F:0/127" true,
    testInRange "F:AE::F:5:F:F:2" "F:AE::F:5:F:F:0/127" false,
    testInRange "0.0.0.0" "::" false,
    testInRange "::" "0.0.0.0" false,
    testInRange "10.0.0.0" "10.0.0.0/24" true,
    testInRange "10.0.0.0" "10.0.0.0/32" true,
    testInRange "10.0.0.0" "10.0.0.1/24" true,
    testInRange "10.0.0.0" "10.0.0.1/32" false,
    testInRange "10.0.0.1" "10.0.0.0/24" true,
    testInRange "10.0.0.1" "10.0.0.1/24" true,
    testInRange "10.0.0.0/24" "10.0.0.0/32" false,
    testInRange "10.0.0.0/32" "10.0.0.0/24" true,
    testInRange "10.0.0.1/24" "10.0.0.0/24" true,
    testInRange "10.0.0.1/24" "10.0.0.1/24" true,
    testInRange "10.0.0.0/24" "10.0.0.1/24" true,
    testInRange "10.0.0.0/24" "10.0.0.0/29" false,
    testInRange "10.0.0.0/29" "10.0.0.0/24" true,
    testInRange "10.0.0.0/24" "10.0.0.1/29" false,
    testInRange "10.0.0.0/29" "10.0.0.1/24" true,
    testInRange "10.0.0.1/24" "10.0.0.0/29" false,
    testInRange "10.0.0.1/29" "10.0.0.0/24" true,
    testInRange "10.0.0.0/32" "10.0.0.0/32" true,
    testInRange "10.0.0.0/32" "10.0.0.0" true
  ]

private def testEq (str₁ str₂ : String) (expected : Bool) : TestCase :=
  let eq : Bool := (ip! str₁) = (ip! str₂)
  test s!"{str₁} == {str₂}" (checkEq eq expected)

def testsForIpNetEquality :=
  suite "IpAddr.eq"
  [
    testEq "10.0.0.0"    "10.0.0.0"    true,
    testEq "10.0.0.0"    "10.0.0.1"    false,
    testEq "10.0.0.0/32" "10.0.0.0"    true,
    testEq "10.0.0.0/24" "10.0.0.0"    false,
    testEq "10.0.0.0/24" "10.0.0.0/24" true,
    testEq "10.0.0.0/24" "10.0.0.0/29" false
  ]

def tests := [
  testsForValidStrings,
  testsForInvalidStrings,
  testsForIsLoopback,
  testsForUInt128Conversion,
  testsForInRange,
  testsForIpNetEquality]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.IPAddr
