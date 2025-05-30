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
import SymTest.Util

/-!
This file contains end-to-end tests for the top-level verification interface
exposed in Cedar.SymCC, focusing on the functions that return counterexamples.
-/

namespace SymTest.Verifier

open Cedar Spec Validation Data UnitTest SymCC

private def testVerifyCex (desc : String) (εnv : SymEnv) (query : SymEnv → SolverM (Option Env)) (property : Env → Bool) : TestCase SolverM :=
  test desc ⟨λ _ => do
    match ← query εnv with
    | some env =>
      -- dbg_trace "here {reprStr env}"
      checkEq (property env) false
    | none     => checkEq "none" "some cex"⟩

private def testVerifyQed (desc : String) (εnv : SymEnv) (query : SymEnv → SolverM (Option Env)) : TestCase SolverM :=
  test desc ⟨λ _ => do checkEq (← query εnv) none⟩

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

private def εnvRead := SymEnv.ofTypeEnv (Photoflash.env Photoflash.readPhoto readCtxType)

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

private def testVerifyNeverErrors? (expected : Finding) (p : Policy) : TestCase SolverM :=
  let desc := s!"[{expected}] neverErrors? {p.id}"
  match expected with
  | .cex => testVerifyCex desc εnvRead (neverErrors? p)
      (λ env => evaluate p.toExpr env.request env.entities matches .ok _)
  | .qed => testVerifyQed desc εnvRead (neverErrors? p)

private def authorize (ps : Policies) (env : Env) : Bool :=
  (Spec.isAuthorized env.request env.entities ps).decision matches .allow

private def testVerifyImplies? (expected : Finding) (ps₁ ps₂ : Policies) : TestCase SolverM :=
  let desc := s!"[{expected}] implies? [{ps₁.map Policy.id}] [{ps₂.map Policy.id}]"
  match expected with
  | .cex => testVerifyCex desc εnvRead (implies? ps₁ ps₂)
      (λ env => !(authorize ps₁ env) || (authorize ps₂ env))
  | .qed => testVerifyQed desc εnvRead (implies? ps₁ ps₂)

private def testVerifyAlwaysAllows? (expected : Finding) (ps : Policies) : TestCase SolverM :=
  let desc := s!"[{expected}] alwaysAllows? [{ps.map Policy.id}]"
  match expected with
  | .cex => testVerifyCex desc εnvRead (alwaysAllows? ps)
      (λ env => authorize ps env = true)
  | .qed => testVerifyQed desc εnvRead (alwaysAllows? ps)

private def testVerifyAlwaysDenies? (expected : Finding) (ps : Policies) : TestCase SolverM :=
  let desc := s!"[{expected}] alwaysDenies? [{ps.map Policy.id}]"
  match expected with
  | .cex => testVerifyCex desc εnvRead (alwaysDenies? ps)
      (λ env => authorize ps env = false)
  | .qed => testVerifyQed desc εnvRead (alwaysDenies? ps)

private def testVerifyEquivalent? (expected : Finding) (ps₁ ps₂ : Policies) : TestCase SolverM :=
  let desc := s!"[{expected}] equivalent? [{ps₁.map Policy.id}] [{ps₂.map Policy.id}]"
  match expected with
  | .cex => testVerifyCex desc εnvRead (equivalent? ps₁ ps₂)
      (λ env => (authorize ps₁ env) = (authorize ps₂ env))
  | .qed => testVerifyQed desc εnvRead (equivalent? ps₁ ps₂)

private def testVerifyDisjoint? (expected : Finding) (ps₁ ps₂ : Policies) : TestCase SolverM :=
  let desc := s!"[{expected}] disjoint? [{ps₁.map Policy.id}] [{ps₂.map Policy.id}]"
  match expected with
  | .cex => testVerifyCex desc εnvRead (disjoint? ps₁ ps₂)
      (λ env => (authorize ps₁ env) != true || (authorize ps₂ env) != true)
  | .qed => testVerifyQed desc εnvRead (disjoint? ps₁ ps₂)

def testTrivialPolicies :=
  suite "Reduction of trivial policies" [
    testReduce policyAllowAll.id policyAllowAll.toExpr εnvRead (.ok (.some true)),
    testReduce policyAllowNone.id policyAllowNone.toExpr εnvRead (.ok (.some false)),
  ]

def testsForNeverErrors? :=
  suite "SymCC.neverErrors?" [
    testVerifyNeverErrors? .qed policyAllowAll,
    testVerifyNeverErrors? .qed policyAllowNone,
    testVerifyNeverErrors? .cex (policyOverflowError 100),
    testVerifyNeverErrors? .cex (policyDatetimeError "1d"),
  ]

def testsForImplies? :=
  suite "SymCC.implies?" [
    testVerifyImplies? .qed [policyAllowNone] [policyAllowAll],
    testVerifyImplies? .cex [policyAllowAll] [policyAllowNone],
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
  suite "SymCC.alwaysAllows?" [
    testVerifyAlwaysAllows? .qed [policyAllowAll],
    testVerifyAlwaysAllows? .cex [policyAllowNone, policyOverflowError 10, policyDatetimeError "1d"],
    testVerifyAlwaysAllows? .qed (policiesAlways .permit),
  ]

def testsForAlwaysDenies? :=
  suite "SymCC.alwaysDenies?" [
    testVerifyAlwaysDenies? .qed [policyAllowNone],
    testVerifyAlwaysDenies? .cex [policyAllowNone, policyOverflowError 10, policyDatetimeError "1d"],
    testVerifyAlwaysDenies? .qed (policiesAlways .forbid),
  ]

def testsForEquivalent? :=
  suite "SymCC.equivalent?" [
    testVerifyEquivalent? .qed [policyAllowAll] (policiesAlways .permit),
    testVerifyEquivalent? .qed [policyAllowNone] (policiesAlways .forbid),
    testVerifyEquivalent? .cex [policyOverflowError 3] [policyOverflowError 12],
    testVerifyEquivalent? .cex [policyDatetimeError "4d"] [policyDatetimeError "10d"],
    testVerifyEquivalent? .cex [policyOverflowError 3] [policyNoOverflowError 3 (by decide)],
  ]

def testsForDisjoint? :=
  suite "SymCC.disjoint?" [
    testVerifyDisjoint? .qed [policyAllowAll] (policiesAlways .forbid),
    testVerifyDisjoint? .qed [policyAllowNone] (policiesAlways .permit),
    testVerifyDisjoint? .qed ((policiesAlways .permit).take 2) ((policiesAlways .permit).drop 2),
    testVerifyDisjoint? .qed (policyAllowAll :: ((policiesAlways .forbid).take 2)) (policyAllowAll :: ((policiesAlways .forbid).drop 2)),
    testVerifyDisjoint? .cex [policyOverflowError 3] [policyOverflowError 12],
    testVerifyDisjoint? .cex [policyDatetimeError "4d"] [policyDatetimeError "10d"],
    testVerifyDisjoint? .cex [policyOverflowError 3] [policyNoOverflowError 3 (by decide)],
  ]

def tests := [
  testTrivialPolicies,
  testsForNeverErrors?,
  testsForImplies?,
  testsForAlwaysAllows?,
  testsForAlwaysDenies?,
  testsForEquivalent?,
  testsForDisjoint?,
]

-- Uncomment for interactive debugging
-- #eval do TestSuite.runAll tests |>.run (← Solver.cvc5)

end SymTest.Verifier
