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

import Cedar.SymCC
import Cedar.SymCCOpt
import SymTest.Util

/-!
This file contains end-to-end tests for the top-level verification interface
exposed in Cedar.SymCC, focusing on the functions that return counterexamples.
-/

namespace SymTest.Verifier

open Cedar Spec Validation Data UnitTest SymCC

/--
`property` is the property which we have a counterexample _to_. Thus, the
`property` function is expected to return `false` on the counterexample.
-/
private def testVerifyCex (desc : String) (query : SolverM (Option Env)) (property : Env → Bool) : TestCase SolverM :=
  test desc ⟨λ _ => do
    match ← query with
    | some env =>
      -- dbg_trace "here {reprStr env}"
      checkEq (property env) false
    | none     => checkEq "none" "some cex"⟩

private def testVerifyQed (desc : String) (query : SolverM (Option Env)) : TestCase SolverM :=
  test desc ⟨λ _ => do checkEq (← query) none⟩

private def policy (id : String) (effect : Effect) (condition : Expr) : Policy := {
  id             := id,
  effect         := effect,
  principalScope := .principalScope .any,
  actionScope    := .actionScope .any,
  resourceScope  := .resourceScope .any,
  condition      := [⟨.when, condition⟩]
}

private def readCtxType : RecordType := Map.make [
  ("a", .required .int),
  ("b", .required (.ext .datetime))
]

private def typeEnvRead := Photoflash.env Photoflash.readPhoto readCtxType
private def εnvRead := SymEnv.ofTypeEnv typeEnvRead

/-
permit (principal, action, resource)
when { principal == principal };
-/
private def policyAllowAll := -- simplifed to true by SymCC
  policy "AllowAll" .permit (.binaryApp .eq (.var .principal) (.var .principal))

/-
permit (principal, action, resource)
when { !(resource == resource) };
-/
private def policyAllowNone := -- simplifed to false by SymCC
  policy "AllowNone" .permit (.unaryApp .not (.binaryApp .eq (.var .resource) (.var .resource)))

/-
forbid (principal, action, resource)
when { principal == principal };
-/
private def policyForbidAll :=
  policy "ForbidAll" .forbid (.binaryApp .eq (.var .principal) (.var .principal))

/-
forbid (principal, action, resource)
when { !(resource == resource) };
-/
private def policyForbidNone :=
  policy "ForbidNone" .forbid (.unaryApp .not (.binaryApp .eq (.var .resource) (.var .resource)))

/-
permit (principal, action, resource)
when { context.a - 1 <= %n% };
-/
private def policyOverflowError (n : Int64) := -- can throw overflow error
  policy "OverflowError" .permit
    (.binaryApp .lessEq
      (.binaryApp .sub (.getAttr (.var .context) "a") (.lit (.int 1)))
      (.lit (.int n)))

/-
permit (principal, action, resource)
when { context.a <= %n+1% };
-/
private def policyNoOverflowError (n : Int64) (_ : n < Int64.MAX) := -- no overflow error when n < Int64.MAX
  policy "OverflowError" .permit
    (.binaryApp .lessEq
      (.getAttr (.var .context) "a")
      (.lit (.int (n + 1))))

/-
permit (principal, action, resource)
when { context.b < context.b.offset(duration(%dur%)) };
-/
private def policyDatetimeError (dur : String) := -- can throw extension (overflow) error
  policy "ExtensionError" .permit
    (.binaryApp .less
      (.getAttr (.var .context) "b")
      (.call .offset [
        (.getAttr (.var .context) "b"),
        (.call .duration [.lit (.string dur)])]))

/-
A group of policies that together allow or deny all access,
depending on whether the effect is permit or forbid:

%effect% (principal, action, resource)
when { context.a == 0 };

%effect% (principal, action, resource)
when { context.a < 0 };

%effect% (principal, action, resource)
when { 0 < context.a };
-/
private def policiesAlways (effect : Effect) : Policies := [
  policy "a==0" effect
    (.binaryApp .eq (.getAttr (.var .context) "a") (.lit (.int 0))),
  policy "a<0" effect
    (.binaryApp .less (.getAttr (.var .context) "a") (.lit (.int 0))),
  policy "0<a" effect
    (.binaryApp .less (.lit (.int 0)) (.getAttr (.var .context) "a"))
]

inductive Finding where
  | cex : Finding
  | qed : Finding
deriving Repr, Inhabited, DecidableEq

instance : ToString Finding where
  toString f := if f = .cex then "cex" else "qed"

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyNeverErrors? (expected : Finding) (p : Policy) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] neverErrors? {p.id}"
  let cp := CompiledPolicy.compile p typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (neverErrors? p εnvRead)
        (λ env => evaluate p.toExpr env.request env.entities matches .ok _),
      testVerifyCex (desc ++ " (optimized)") (do neverErrorsOpt? (← cp))
        (λ env => evaluate p.toExpr env.request env.entities matches .ok _),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (neverErrors? p εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do neverErrorsOpt? (← cp))
    ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyAlwaysMatches? (expected : Finding) (p : Policy) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] alwaysMatches? {p.id}"
  let cp := CompiledPolicy.compile p typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (alwaysMatches? p εnvRead)
        (λ env => evaluate p.toExpr env.request env.entities = .ok true),
      testVerifyCex (desc ++ " (optimized)") (do alwaysMatchesOpt? (← cp))
        (λ env => evaluate p.toExpr env.request env.entities = .ok true),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (alwaysMatches? p εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do alwaysMatchesOpt? (← cp))
    ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyNeverMatches? (expected : Finding) (p : Policy) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] neverMatches? {p.id}"
  let cp := CompiledPolicy.compile p typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (neverMatches? p εnvRead)
        (λ env => evaluate p.toExpr env.request env.entities ≠ .ok true),
      testVerifyCex (desc ++ " (optimized)") (do neverMatchesOpt? (← cp))
        (λ env => evaluate p.toExpr env.request env.entities ≠ .ok true),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (neverMatches? p εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do neverMatchesOpt? (← cp))
    ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyMatchesEquivalent? (expected : Finding) (p₁ p₂ : Policy) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] matchesEquivalent? {p₁.id} {p₂.id}"
  let cp₁ := CompiledPolicy.compile p₁ typeEnvRead |> IO.ofExcept
  let cp₂ := CompiledPolicy.compile p₂ typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
    testVerifyCex (desc ++ " (unoptimized)") (matchesEquivalent? p₁ p₂ εnvRead)
      (λ env =>
        let p₁matches := evaluate p₁.toExpr env.request env.entities == .ok true
        let p₂matches := evaluate p₂.toExpr env.request env.entities == .ok true
        p₁matches = p₂matches),
    testVerifyCex (desc ++ " (unoptimized)") (do matchesEquivalentOpt? (← cp₁) (← cp₂))
      (λ env =>
        let p₁matches := evaluate p₁.toExpr env.request env.entities == .ok true
        let p₂matches := evaluate p₂.toExpr env.request env.entities == .ok true
        p₁matches = p₂matches),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (matchesEquivalent? p₁ p₂ εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do matchesEquivalentOpt? (← cp₁) (← cp₂))
  ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyMatchesImplies? (expected : Finding) (p₁ p₂ : Policy) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] matchesImplies? {p₁.id} {p₂.id}"
  let cp₁ := CompiledPolicy.compile p₁ typeEnvRead |> IO.ofExcept
  let cp₂ := CompiledPolicy.compile p₂ typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
    testVerifyCex (desc ++ " (unoptimized)") (matchesImplies? p₁ p₂ εnvRead)
      (λ env =>
        let p₁matches := evaluate p₁.toExpr env.request env.entities == .ok true
        let p₂matches := evaluate p₂.toExpr env.request env.entities == .ok true
        p₁matches → p₂matches),
    testVerifyCex (desc ++ " (unoptimized)") (do matchesImpliesOpt? (← cp₁) (← cp₂))
      (λ env =>
        let p₁matches := evaluate p₁.toExpr env.request env.entities == .ok true
        let p₂matches := evaluate p₂.toExpr env.request env.entities == .ok true
        p₁matches → p₂matches),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (matchesImplies? p₁ p₂ εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do matchesImpliesOpt? (← cp₁) (← cp₂))
  ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyMatchesDisjoint? (expected : Finding) (p₁ p₂ : Policy) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] matchesDisjoint? {p₁.id} {p₂.id}"
  let cp₁ := CompiledPolicy.compile p₁ typeEnvRead |> IO.ofExcept
  let cp₂ := CompiledPolicy.compile p₂ typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
    testVerifyCex (desc ++ " (unoptimized)") (matchesDisjoint? p₁ p₂ εnvRead)
      (λ env =>
        let p₁matches := evaluate p₁.toExpr env.request env.entities == .ok true
        let p₂matches := evaluate p₂.toExpr env.request env.entities == .ok true
        ¬p₁matches ∨ ¬p₂matches),
    testVerifyCex (desc ++ " (unoptimized)") (do matchesDisjointOpt? (← cp₁) (← cp₂))
      (λ env =>
        let p₁matches := evaluate p₁.toExpr env.request env.entities == .ok true
        let p₂matches := evaluate p₂.toExpr env.request env.entities == .ok true
        ¬p₁matches ∨ ¬p₂matches),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (matchesDisjoint? p₁ p₂ εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do matchesDisjointOpt? (← cp₁) (← cp₂))
  ]

private def authorize (ps : Policies) (env : Env) : Bool :=
  (Spec.isAuthorized env.request env.entities ps).decision matches .allow

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyImplies? (expected : Finding) (ps₁ ps₂ : Policies) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] implies? [{ps₁.map Policy.id}] [{ps₂.map Policy.id}]"
  let cps₁ := CompiledPolicies.compile ps₁ typeEnvRead |> IO.ofExcept
  let cps₂ := CompiledPolicies.compile ps₂ typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (implies? ps₁ ps₂ εnvRead)
        (λ env => !(authorize ps₁ env) || (authorize ps₂ env)),
      testVerifyCex (desc ++ " (optimized)") (do impliesOpt? (← cps₁) (← cps₂))
        (λ env => !(authorize ps₁ env) || (authorize ps₂ env)),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (implies? ps₁ ps₂ εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do impliesOpt? (← cps₁) (← cps₂))
    ]

/-- Returns two `TestCase`s, one which tests unoptimized SymCC, the other which tests SymCCOpt -/
private def testVerifyAlwaysAllows? (expected : Finding) (ps : Policies) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] alwaysAllows? [{ps.map Policy.id}]"
  let cps := CompiledPolicies.compile ps typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (alwaysAllows? ps εnvRead)
        (λ env => authorize ps env = true),
      testVerifyCex (desc ++ " (optimized)") (do alwaysAllowsOpt? (← cps))
        (λ env => authorize ps env = true),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (alwaysAllows? ps εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do alwaysAllowsOpt? (← cps)),
    ]

private def testVerifyAlwaysDenies? (expected : Finding) (ps : Policies) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] alwaysDenies? [{ps.map Policy.id}]"
  let cps := CompiledPolicies.compile ps typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (alwaysDenies? ps εnvRead)
        (λ env => authorize ps env = false),
      testVerifyCex (desc ++ " (optimized)") (do alwaysDeniesOpt? (← cps))
        (λ env => authorize ps env = false),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (alwaysDenies? ps εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do alwaysDeniesOpt? (← cps)),
    ]

private def testVerifyEquivalent? (expected : Finding) (ps₁ ps₂ : Policies) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] equivalent? [{ps₁.map Policy.id}] [{ps₂.map Policy.id}]"
  let cps₁ := CompiledPolicies.compile ps₁ typeEnvRead |> IO.ofExcept
  let cps₂ := CompiledPolicies.compile ps₂ typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (equivalent? ps₁ ps₂ εnvRead)
        (λ env => (authorize ps₁ env) = (authorize ps₂ env)),
      testVerifyCex (desc ++ " (optimized)") (do equivalentOpt? (← cps₁) (← cps₂))
        (λ env => (authorize ps₁ env) = (authorize ps₂ env)),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (equivalent? ps₁ ps₂ εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do equivalentOpt? (← cps₁) (← cps₂)),
    ]

private def testVerifyDisjoint? (expected : Finding) (ps₁ ps₂ : Policies) : List (TestCase SolverM) :=
  let desc := s!"[{expected}] disjoint? [{ps₁.map Policy.id}] [{ps₂.map Policy.id}]"
  let cps₁ := CompiledPolicies.compile ps₁ typeEnvRead |> IO.ofExcept
  let cps₂ := CompiledPolicies.compile ps₂ typeEnvRead |> IO.ofExcept
  match expected with
  | .cex => [
      testVerifyCex (desc ++ " (unoptimized)") (disjoint? ps₁ ps₂ εnvRead)
        (λ env => (authorize ps₁ env) != true || (authorize ps₂ env) != true),
      testVerifyCex (desc ++ " (optimized)") (do disjointOpt? (← cps₁) (← cps₂))
        (λ env => (authorize ps₁ env) != true || (authorize ps₂ env) != true),
    ]
  | .qed => [
      testVerifyQed (desc ++ " (unoptimized)") (disjoint? ps₁ ps₂ εnvRead),
      testVerifyQed (desc ++ " (optimized)") (do disjointOpt? (← cps₁) (← cps₂)),
    ]

def testTrivialPolicies :=
  suite "Reduction of trivial policies" [
    testCompile policyAllowAll.id policyAllowAll.toExpr εnvRead (.ok (.some true)),
    testCompile policyAllowNone.id policyAllowNone.toExpr εnvRead (.ok (.some false)),
  ]

def testsForNeverErrors? :=
  suite "SymCC.neverErrors?" $ List.flatten [
    testVerifyNeverErrors? .qed policyAllowAll,
    testVerifyNeverErrors? .qed policyAllowNone,
    testVerifyNeverErrors? .qed policyForbidAll,
    testVerifyNeverErrors? .qed policyForbidNone,
    testVerifyNeverErrors? .cex (policyOverflowError 100),
    testVerifyNeverErrors? .cex (policyDatetimeError "1d"),
  ]

def testsForAlwaysMatches? :=
  suite "SymCC.alwaysMatches?" $ List.flatten [
    testVerifyAlwaysMatches? .qed policyAllowAll,
    testVerifyAlwaysMatches? .qed policyForbidAll,
    testVerifyAlwaysMatches? .cex policyAllowNone,
    testVerifyAlwaysMatches? .cex policyForbidNone,
    testVerifyAlwaysMatches? .cex (policyOverflowError 100),
  ]

def testsForNeverMatches? :=
  suite "SymCC.neverMatches?" $ List.flatten [
    testVerifyNeverMatches? .cex policyAllowAll,
    testVerifyNeverMatches? .cex policyForbidAll,
    testVerifyNeverMatches? .qed policyAllowNone,
    testVerifyNeverMatches? .qed policyForbidNone,
    testVerifyNeverMatches? .cex (policyOverflowError 100),
  ]

def testsForMatchesEquivalent? :=
  suite "SymCC.matchesEquivalent?" $ List.flatten [
    testVerifyMatchesEquivalent? .qed policyAllowAll policyAllowAll,
    testVerifyMatchesEquivalent? .qed policyForbidAll policyForbidAll,
    testVerifyMatchesEquivalent? .qed policyAllowAll policyForbidAll, -- matches-equivalent, but not equivalent
    testVerifyMatchesEquivalent? .qed policyForbidAll policyAllowAll,
    testVerifyMatchesEquivalent? .cex policyAllowAll policyAllowNone,
    testVerifyMatchesEquivalent? .cex policyForbidAll policyAllowNone, -- equivalent, but not matches-equivalent
  ]

def testsForMatchesImplies? :=
  suite "SymCC.matchesImplies?" $ List.flatten [
    testVerifyMatchesImplies? .qed policyAllowAll policyAllowAll,
    testVerifyMatchesImplies? .qed policyAllowNone policyAllowAll,
    testVerifyMatchesImplies? .cex policyAllowAll policyAllowNone,
    testVerifyMatchesImplies? .qed policyAllowAll policyForbidAll, -- matches-implies, but not implies
    testVerifyMatchesImplies? .cex policyForbidAll policyAllowNone, -- implies, but not matches-implies
  ]

def testsForMatchesDisjoint? :=
  suite "SymCC.matchesDisjoint?" $ List.flatten [
    testVerifyMatchesDisjoint? .qed policyAllowAll policyAllowNone,
    testVerifyMatchesDisjoint? .qed policyForbidAll policyForbidNone,
    testVerifyMatchesDisjoint? .cex policyForbidAll policyForbidAll, -- disjoint, but not matches-disjoint
  ]

def testsForImplies? :=
  suite "SymCC.implies?" $ List.flatten [
    testVerifyImplies? .qed [policyAllowAll] [policyAllowAll],
    testVerifyImplies? .qed [policyAllowNone] [policyAllowAll],
    testVerifyImplies? .cex [policyAllowAll] [policyAllowNone],
    testVerifyImplies? .cex [policyAllowAll] [policyForbidAll], -- matches-implies, but not implies
    testVerifyImplies? .qed [policyForbidAll] [policyAllowNone], -- implies, but not matches-implies
    testVerifyImplies? .cex [policyAllowAll] [policyOverflowError 10],
    testVerifyImplies? .qed [policyOverflowError 10] [policyOverflowError 11],
    testVerifyImplies? .qed [policyDatetimeError "2d"] [policyDatetimeError "1d"],
    testVerifyImplies? .qed
      [policyOverflowError 10, policyDatetimeError "2d"]
      [policyOverflowError 11, policyDatetimeError "1d"],
    testVerifyImplies? .cex [policyDatetimeError "1d"] [policyDatetimeError "2d"],
    testVerifyImplies? .cex
      [policyOverflowError 10, policyDatetimeError "1d"]
      [policyOverflowError 11, policyDatetimeError "2d"],
    testVerifyImplies? .cex
      [policyOverflowError 11, policyDatetimeError "2d"]
      [policyOverflowError 10, policyDatetimeError "1d"],
  ]

def testsForAlwaysAllows? :=
  suite "SymCC.alwaysAllows?" $ List.flatten [
    testVerifyAlwaysAllows? .qed [policyAllowAll],
    testVerifyAlwaysAllows? .cex [policyAllowNone],
    testVerifyAlwaysAllows? .cex [policyForbidAll],
    testVerifyAlwaysAllows? .cex [policyAllowNone, policyOverflowError 10, policyDatetimeError "1d"],
    testVerifyAlwaysAllows? .qed (policiesAlways .permit),
    testVerifyAlwaysAllows? .cex (policiesAlways .forbid),
  ]

def testsForAlwaysDenies? :=
  suite "SymCC.alwaysDenies?" $ List.flatten [
    testVerifyAlwaysDenies? .cex [policyAllowAll],
    testVerifyAlwaysDenies? .qed [policyAllowNone],
    testVerifyAlwaysDenies? .qed [policyForbidAll],
    testVerifyAlwaysDenies? .cex [policyAllowNone, policyOverflowError 10, policyDatetimeError "1d"],
    testVerifyAlwaysDenies? .cex (policiesAlways .permit),
    testVerifyAlwaysDenies? .qed (policiesAlways .forbid),
  ]

def testsForEquivalent? :=
  suite "SymCC.equivalent?" $ List.flatten [
    testVerifyEquivalent? .qed [policyAllowAll] [policyAllowAll],
    testVerifyEquivalent? .qed [policyForbidAll] [policyForbidAll],
    testVerifyEquivalent? .cex [policyAllowAll] [policyForbidAll], -- matches-equivalent, but not equivalent
    testVerifyEquivalent? .cex [policyForbidAll] [policyAllowAll],
    testVerifyEquivalent? .cex [policyAllowAll] [policyAllowNone],
    testVerifyEquivalent? .qed [policyForbidAll] [policyAllowNone], -- equivalent, but not matches-equivalent
    testVerifyEquivalent? .qed [policyAllowAll] (policiesAlways .permit),
    testVerifyEquivalent? .qed [policyAllowNone] (policiesAlways .forbid),
    testVerifyEquivalent? .cex [policyOverflowError 3] [policyOverflowError 12],
    testVerifyEquivalent? .cex [policyDatetimeError "4d"] [policyDatetimeError "10d"],
    testVerifyEquivalent? .cex [policyOverflowError 3] [policyNoOverflowError 3 (by decide)],
  ]

def testsForDisjoint? :=
  suite "SymCC.disjoint?" $ List.flatten [
    testVerifyDisjoint? .qed [policyAllowAll] (policiesAlways .forbid),
    testVerifyDisjoint? .qed [policyAllowNone] (policiesAlways .permit),
    testVerifyDisjoint? .qed ((policiesAlways .permit).take 2) ((policiesAlways .permit).drop 2),
    testVerifyDisjoint? .qed (policyAllowAll :: ((policiesAlways .forbid).take 2)) (policyAllowAll :: ((policiesAlways .forbid).drop 2)),
    testVerifyDisjoint? .cex [policyOverflowError 3] [policyOverflowError 12],
    testVerifyDisjoint? .cex [policyDatetimeError "4d"] [policyDatetimeError "10d"],
    testVerifyDisjoint? .cex [policyOverflowError 3] [policyNoOverflowError 3 (by decide)],
  ]

def testsForEncoder? :=
  suite "SymCC.Encoder" $ List.flatten [
    testVerifyAlwaysAllows? .cex [
      policy "AllowAll" .permit (.binaryApp .eq (.var .principal) (.lit (.entityUID ⟨Photoflash.userType, "\""⟩) ))
    ],
    testVerifyAlwaysAllows? .cex [
      policy "AllowAll" .permit (.binaryApp .eq (.var .principal) (.lit (.entityUID ⟨Photoflash.userType, "🐼"⟩) ))
    ],
  ]

def tests := [
  testTrivialPolicies,
  testsForNeverErrors?,
  testsForAlwaysMatches?,
  testsForNeverMatches?,
  testsForMatchesEquivalent?,
  testsForMatchesImplies?,
  testsForMatchesDisjoint?,
  testsForImplies?,
  testsForAlwaysAllows?,
  testsForAlwaysDenies?,
  testsForEquivalent?,
  testsForDisjoint?,
  testsForEncoder?,
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Verifier
