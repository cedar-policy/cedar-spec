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

import Cedar.Spec.WildcardDelimited
import UnitTest.Run

/-! This file defines unit tests for the delimiter-aware wildcard matching functions. -/

namespace UnitTest.WildcardDelimited

open Cedar.Spec

private def testMatch (str : String) (pat : DelimPattern) (delim : Char) (expected : Bool) : TestCase IO :=
  test s!"{expected}: \"{str}\" like({reprStr pat}, {delim})" ⟨λ _ =>
    checkEq
      (wildcardMatchDelimited str pat delim, matchesDelimited str.toList pat delim)
      (expected, expected)⟩

private def justChars (str : String) : DelimPattern :=
  str.toList.map .justChar

def hostTests :=
  suite "wildcardMatchDelimited: hostnames"
  [
    testMatch "api.example.com"
      ([.star] ++ justChars ".example.com") '.' true,
    testMatch "example.com"
      ([.star] ++ justChars ".example.com") '.' false,
    testMatch "deep.api.example.com"
      ([.star] ++ justChars ".example.com") '.' false,
    testMatch "deep.api.example.com"
      ([.multiStar] ++ justChars ".example.com") '.' true,
    testMatch "example.com"
      ([.multiStar] ++ justChars ".example.com") '.' false,
    testMatch "example.com"
      ([.star] ++ justChars "example.com") '.' true,
    testMatch "tenant-api.example.com"
      ([.star] ++ justChars "-api.example.com") '.' true,
    testMatch "deep.api.example.com" [.star] '.' false,
    testMatch "deep.api.example.com" [.multiStar] '.' true,
    testMatch "" [.multiStar] '.' true,
    testMatch "api.x.y.com"
      (justChars "api." ++ [.multiStar] ++ justChars ".com") '.' true,
    testMatch "api.com"
      (justChars "api." ++ [.multiStar] ++ justChars ".com") '.' false,
  ]

def pathTests :=
  suite "wildcardMatchDelimited: paths"
  [
    testMatch "/repos/o/pulls/1/reviews"
      (justChars "/repos/" ++ [.star] ++ justChars "/pulls/" ++ [.star] ++ justChars "/reviews") '/' true,
    testMatch "/repos/o/sub/pulls/1/reviews"
      (justChars "/repos/" ++ [.star] ++ justChars "/pulls/" ++ [.star] ++ justChars "/reviews") '/' false,
    testMatch "a/b/error.log"
      ([.multiStar] ++ justChars "/error.log") '/' true,
    testMatch "/v1/chat"
      (justChars "/v1/" ++ [.multiStar]) '/' true,
    testMatch "/v1"
      (justChars "/v1/" ++ [.multiStar]) '/' false,
    testMatch "/api//admin"
      (justChars "/api/" ++ [.star] ++ justChars "/admin") '/' true,
  ]

def edgeCaseTests :=
  suite "wildcardMatchDelimited: edge cases"
  [
    testMatch "" [] '.' true,
    testMatch "a" [] '.' false,
    testMatch "" [.star] '.' true,
    testMatch "" [.multiStar] '.' true,
    testMatch "x" [.star] '.' true,
    testMatch "." [.star] '.' false,
    testMatch "." [.multiStar] '.' true,
    testMatch "a.b" (justChars "a.b") '.' true,
    testMatch "a.b" (justChars "a." ++ [.star]) '.' true,
    testMatch "a.b.c" (justChars "a." ++ [.star]) '.' false,
    testMatch "a*b" (justChars "a" ++ [.justChar '*'] ++ justChars "b") '.' true,
  ]

def interleavedTests :=
  suite "wildcardMatchDelimited: interleaved * and **"
  [
    testMatch "aXbXc"
      ([.multiStar] ++ [.justChar 'X'] ++ [.multiStar]) '.' true,
    testMatch "aYb"
      ([.multiStar] ++ [.justChar 'X'] ++ [.multiStar]) '.' false,
    testMatch "aX.b.c"
      ([.multiStar] ++ [.justChar 'X'] ++ [.multiStar]) '.' true,

    testMatch "/a/foo/b/c/bar/d"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.multiStar]) '/' true,
    testMatch "/a/foo"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.multiStar]) '/' false,
    testMatch "foobar"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.multiStar]) '/' true,

    testMatch "xfoo/a/b/baryz"
      ([.star] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.star]) '/' true,
    testMatch "x/foo/a/bar/y"
      ([.star] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.star]) '/' false,
    testMatch "foo/bar/x"
      ([.star] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.star]) '/' false,

    testMatch "aXYb"
      ([.multiStar] ++ [.justChar 'X'] ++ [.star] ++ [.justChar 'Y'] ++ [.multiStar]) '.' true,
    testMatch "a.X.Y.b"
      ([.multiStar] ++ [.justChar 'X'] ++ [.star] ++ [.justChar 'Y'] ++ [.multiStar]) '.' false,
    testMatch "aXZYb"
      ([.multiStar] ++ [.justChar 'X'] ++ [.star] ++ [.justChar 'Y'] ++ [.multiStar]) '.' true,

    testMatch "xyz"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' true,
    testMatch "AxByCzD"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' true,
    testMatch "A.xByCzD"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' true,
    testMatch "x.y.z"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' false,

    testMatch "foo/a/b/bar"
      (justChars "foo" ++ [.multiStar] ++ justChars "bar") '/' true,
    testMatch "foo/a/b"
      (justChars "foo" ++ [.multiStar] ++ justChars "bar") '/' false,

    testMatch "/a/foo"
      ([.multiStar] ++ justChars "foo") '/' true,
    testMatch "foo/a"
      ([.multiStar] ++ justChars "foo") '/' false,

    testMatch "x/a/y/b/z/c"
      ([.multiStar] ++ [.justChar 'a'] ++ [.multiStar] ++ [.justChar 'b'] ++ [.multiStar] ++ [.justChar 'c']) '/' true,
    testMatch "abc"
      ([.multiStar] ++ [.justChar 'a'] ++ [.multiStar] ++ [.justChar 'b'] ++ [.multiStar] ++ [.justChar 'c']) '/' true,
    testMatch "a/b"
      ([.multiStar] ++ [.justChar 'a'] ++ [.multiStar] ++ [.justChar 'b'] ++ [.multiStar] ++ [.justChar 'c']) '/' false,

    testMatch "/a/foo/b/foo/c"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar]) '/' true,
    testMatch "/a/b/c"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar]) '/' false,
  ]

def tests := [ hostTests, pathTests, edgeCaseTests, interleavedTests ]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.WildcardDelimited
