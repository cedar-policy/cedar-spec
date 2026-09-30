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

/-!
Unit tests for `wildcardMatchDelimited`.

For every case we check *both* the specification (`matchesDelimited`, the
clean recursive definition) and the DP implementation (`wildcardMatchDelimited`,
the memoised version) — the tests fail if they disagree.  This is the pragmatic
substitute for the (currently deferred) formal correctness theorem.
-/

namespace UnitTest.WildcardDelimited

open Cedar.Spec

/--
Test that both implementations agree with `expected` on the given input.
We combine the two results into a triple with `expected` doubled, so the
test fails distinctly when only one of the two disagrees.
-/
private def testMatch (str : String) (pat : DelimPattern) (delim : Char) (expected : Bool) : TestCase IO :=
  test s!"{expected}: \"{str}\" like({reprStr pat}, {delim})" ⟨λ _ =>
    checkEq
      (wildcardMatchDelimited str pat delim, matchesDelimited str.toList pat delim)
      (expected, expected)⟩

private def justChars (str : String) : DelimPattern :=
  str.toList.map .justChar

/-!
### Hostname examples

Match table from the RFC.  Delimiter is `'.'`.
-/
def hostTests :=
  suite "wildcardMatchDelimited: hostnames"
  [
    -- `*.example.com` matches one subdomain
    testMatch "api.example.com"
      ([.star] ++ justChars ".example.com") '.' true,
    -- `*.example.com` does NOT match bare `example.com` (literal `.` needs a char)
    testMatch "example.com"
      ([.star] ++ justChars ".example.com") '.' false,
    -- `*.example.com` does NOT match multi-level subdomain
    testMatch "deep.api.example.com"
      ([.star] ++ justChars ".example.com") '.' false,
    -- `**.example.com` matches multi-level subdomain
    testMatch "deep.api.example.com"
      ([.multiStar] ++ justChars ".example.com") '.' true,
    -- `**.example.com` does NOT match bare `example.com`
    testMatch "example.com"
      ([.multiStar] ++ justChars ".example.com") '.' false,
    -- `*example.com` matches bare `example.com` (`*` consumes empty)
    testMatch "example.com"
      ([.star] ++ justChars "example.com") '.' true,
    -- `*-api.example.com` matches `tenant-api.example.com`
    testMatch "tenant-api.example.com"
      ([.star] ++ justChars "-api.example.com") '.' true,
    -- `*` alone doesn't match multi-level
    testMatch "deep.api.example.com" [.star] '.' false,
    -- `**` matches everything
    testMatch "deep.api.example.com" [.multiStar] '.' true,
    testMatch "" [.multiStar] '.' true,
    -- `api.**.com` requires at least one middle label
    testMatch "api.x.y.com"
      (justChars "api." ++ [.multiStar] ++ justChars ".com") '.' true,
    testMatch "api.com"
      (justChars "api." ++ [.multiStar] ++ justChars ".com") '.' false,
  ]

/-!
### URL path examples

Delimiter is `'/'`.
-/
def pathTests :=
  suite "wildcardMatchDelimited: paths"
  [
    -- `/repos/*/pulls/*/reviews` matches simple case
    testMatch "/repos/o/pulls/1/reviews"
      (justChars "/repos/" ++ [.star] ++ justChars "/pulls/" ++ [.star] ++ justChars "/reviews") '/' true,
    -- `/repos/*/pulls/*/reviews` does NOT match nested case
    testMatch "/repos/o/sub/pulls/1/reviews"
      (justChars "/repos/" ++ [.star] ++ justChars "/pulls/" ++ [.star] ++ justChars "/reviews") '/' false,
    -- `**/error.log` matches multi-segment prefix
    testMatch "a/b/error.log"
      ([.multiStar] ++ justChars "/error.log") '/' true,
    -- `/v1/**` matches subtree
    testMatch "/v1/chat"
      (justChars "/v1/" ++ [.multiStar]) '/' true,
    -- `/v1/**` does NOT match bare `/v1` (literal `/` required)
    testMatch "/v1"
      (justChars "/v1/" ++ [.multiStar]) '/' false,
    -- Zero-or-more: `/api/*/admin` admits `/api//admin`
    testMatch "/api//admin"
      (justChars "/api/" ++ [.star] ++ justChars "/admin") '/' true,
  ]

/-!
### Edge cases: empty inputs, escaped chars, no-delimiter interaction.
-/
def edgeCaseTests :=
  suite "wildcardMatchDelimited: edge cases"
  [
    -- Empty pattern matches only empty text
    testMatch "" [] '.' true,
    testMatch "a" [] '.' false,
    -- `*` alone matches empty
    testMatch "" [.star] '.' true,
    testMatch "" [.multiStar] '.' true,
    -- `*` alone matches single non-delimiter char
    testMatch "x" [.star] '.' true,
    testMatch "." [.star] '.' false,   -- `*` can't consume delim
    testMatch "." [.multiStar] '.' true, -- `**` can
    -- Literal delimiter in pattern
    testMatch "a.b" (justChars "a.b") '.' true,
    -- `a.*` matches `a.b` (`*` consumes `b`)
    testMatch "a.b" (justChars "a." ++ [.star]) '.' true,
    testMatch "a.b.c" (justChars "a." ++ [.star]) '.' false,
    -- Escaped asterisk (literal `*` in pattern, in Lean spelled `.justChar '*'`)
    testMatch "a*b" (justChars "a" ++ [.justChar '*'] ++ justChars "b") '.' true,
  ]

/-!
### Interleaved `*` and `**` with literals

RFC #115 allows `**` in any position, not just at the end.  These tests
pin membership answers for several interleaved patterns.  Envoy / OpenAPI
forbid `**` in non-final position for capture-disambiguation reasons;
Cedar's `like` returns Bool with no capture, so the restriction doesn't
apply.
-/
def interleavedTests :=
  suite "wildcardMatchDelimited: interleaved * and **"
  [
    -- `**X**` on `aXbXc` — multiple decompositions, still matches.
    testMatch "aXbXc"
      ([.multiStar] ++ [.justChar 'X'] ++ [.multiStar]) '.' true,
    testMatch "aYb"
      ([.multiStar] ++ [.justChar 'X'] ++ [.multiStar]) '.' false,
    testMatch "aX.b.c"
      ([.multiStar] ++ [.justChar 'X'] ++ [.multiStar]) '.' true,

    -- `**foo**bar**` with delim `/`.
    testMatch "/a/foo/b/c/bar/d"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.multiStar]) '/' true,
    testMatch "/a/foo"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.multiStar]) '/' false,
    testMatch "foobar"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.multiStar]) '/' true,

    -- `*foo**bar*` — leading/trailing `*` restricted to one segment.
    testMatch "xfoo/a/b/baryz"
      ([.star] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.star]) '/' true,
    testMatch "x/foo/a/bar/y"
      ([.star] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.star]) '/' false,
    testMatch "foo/bar/x"
      ([.star] ++ justChars "foo" ++ [.multiStar] ++ justChars "bar" ++ [.star]) '/' false,

    -- `**X*Y**` — `*` between X and Y can't cross delim.
    testMatch "aXYb"
      ([.multiStar] ++ [.justChar 'X'] ++ [.star] ++ [.justChar 'Y'] ++ [.multiStar]) '.' true,
    testMatch "a.X.Y.b"
      ([.multiStar] ++ [.justChar 'X'] ++ [.star] ++ [.justChar 'Y'] ++ [.multiStar]) '.' false,
    testMatch "aXZYb"
      ([.multiStar] ++ [.justChar 'X'] ++ [.star] ++ [.justChar 'Y'] ++ [.multiStar]) '.' true,

    -- `**x*y*z**` interleaved.
    testMatch "xyz"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' true,
    testMatch "AxByCzD"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' true,
    testMatch "A.xByCzD"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' true,
    testMatch "x.y.z"
      ([.multiStar] ++ [.justChar 'x'] ++ [.star] ++ [.justChar 'y'] ++ [.star] ++ [.justChar 'z'] ++ [.multiStar]) '.' false,

    -- `**` only in the middle, not at end.
    testMatch "foo/a/b/bar"
      (justChars "foo" ++ [.multiStar] ++ justChars "bar") '/' true,
    testMatch "foo/a/b"
      (justChars "foo" ++ [.multiStar] ++ justChars "bar") '/' false,

    -- `**` only at the start.
    testMatch "/a/foo"
      ([.multiStar] ++ justChars "foo") '/' true,
    testMatch "foo/a"
      ([.multiStar] ++ justChars "foo") '/' false,

    -- Three `**`s with single literals.
    testMatch "x/a/y/b/z/c"
      ([.multiStar] ++ [.justChar 'a'] ++ [.multiStar] ++ [.justChar 'b'] ++ [.multiStar] ++ [.justChar 'c']) '/' true,
    testMatch "abc"
      ([.multiStar] ++ [.justChar 'a'] ++ [.multiStar] ++ [.justChar 'b'] ++ [.multiStar] ++ [.justChar 'c']) '/' true,
    testMatch "a/b"
      ([.multiStar] ++ [.justChar 'a'] ++ [.multiStar] ++ [.justChar 'b'] ++ [.multiStar] ++ [.justChar 'c']) '/' false,

    -- Multiple-decomposition case (ambiguous for capture, deterministic for Bool).
    testMatch "/a/foo/b/foo/c"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar]) '/' true,
    testMatch "/a/b/c"
      ([.multiStar] ++ justChars "foo" ++ [.multiStar]) '/' false,
  ]

def tests := [ hostTests, pathTests, edgeCaseTests, interleavedTests ]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.WildcardDelimited
