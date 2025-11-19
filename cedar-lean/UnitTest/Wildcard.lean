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

import Cedar.Spec.Wildcard
import UnitTest.Run

/-! This file defines unit tests for the wildcard matching functions. -/

namespace UnitTest.Wildcard

open Cedar.Spec

private def testWildcardMatch (str : String) (pat : Pattern) (expected : Bool) : TestCase IO :=
  test s!"{expected}: {str} like {reprStr pat}" ⟨λ _ => checkEq (wildcardMatch str pat) expected⟩

private def justChars (str : String) : Pattern :=
  str.data.map (fun c => .justChar c)

def testsForWildcardMatch :=
  suite "wildcardMatch"
  [
    testWildcardMatch "" [] true,
    testWildcardMatch "a" [] false,
    testWildcardMatch "a" [.justChar 'a'] true,
    testWildcardMatch "" [.star] true,
    testWildcardMatch "a" [.star] true,
    testWildcardMatch "abababa" (justChars "abababa") true,
    testWildcardMatch "abababa" [.star] true,
    testWildcardMatch "abababa" ([.star] ++ (justChars "aba")) true,
    testWildcardMatch "abababa" ((justChars "aba") ++ [.star]) true,
    testWildcardMatch "abababa" ([.star] ++ (justChars "aba") ++ [.star]) true,
    testWildcardMatch "abababa" [.justChar 'a', .star] true,
    testWildcardMatch "abababa" [.justChar 'a', .star, .justChar 'b'] false,
    testWildcardMatch "abababa" [.star, .justChar 'a', .star, .star, .justChar 'b', .star, .star,.justChar 'b', .star] true,
    testWildcardMatch "abababa" [.star, .justChar 'a', .star, .star, .justChar 'b', .star, .star,.justChar 'b'] false,
    testWildcardMatch
      "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"
      [.star, .star, .star, .star, .star, .justChar '\\', .justChar '0', .justChar '\\', .justChar '0', .star]
      false
  ]

def tests := [ testsForWildcardMatch  ]

-- Uncomment for interactive debugging
-- #eval TestSuite.runAll tests

end UnitTest.Wildcard
