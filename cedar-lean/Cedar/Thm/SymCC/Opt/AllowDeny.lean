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

/-!
Proofs about various functions applied to `allowAll` and `denyAll` policies, and empty policy sets.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.SymCC

/--
`wellTypedPolicies` on the empty policy set
-/
theorem wellTypedPolicies_empty (Γ : Validation.TypeEnv) :
  wellTypedPolicies [] Γ = .ok []
:= by
  simp [wellTypedPolicies, pure, Except.pure]

/--
`wellTypedPolicies` on `Policy.allowAll`
-/
theorem wellTypedPolicies_allowAll (Γ : Validation.TypeEnv) :
  wellTypedPolicies [Policy.allowAll] Γ = .ok [verifyAlwaysAllows.allowAll]
:= by
  simp [wellTypedPolicies, wellTypedPolicy]
  simp [Validation.typecheckPolicy, Policy.allowAll, verifyAlwaysAllows.allowAll]
  simp [Policy.toExpr, PrincipalScope.toExpr, ActionScope.toExpr, ResourceScope.toExpr, Scope.toExpr, Conditions.toExpr]
  simp [Validation.typeOf, Validation.substituteAction, Validation.mapOnVars, Validation.typeOfLit, Validation.ok, Validation.typeOfAnd, Validation.TypedExpr.typeOf, Validation.TypedExpr.toExpr, Validation.subty, Validation.lub?, Validation.lubBool]

/--
`SymCC.isAuthorized` on the empty policy set
-/
theorem isAuthorized_empty (εnv : SymEnv) :
  SymCC.isAuthorized [] εnv = .ok (.bool false)
:= by
  simp [SymCC.isAuthorized, SymCC.satisfiedPolicies]
  simp [
    Factory.and, Factory.or, Factory.not, Factory.anyTrue, Factory.eq, Factory.eq.simplify,
    Factory.someOf, Term.typeOf, TermPrim.typeOf
  ]

/--
`SymCC.isAuthorized` on `verifyAlwaysAllows.allowAll`
-/
theorem isAuthorized_allowAll (εnv : SymEnv) :
  SymCC.isAuthorized [verifyAlwaysAllows.allowAll] εnv = .ok (.bool true)
:= by
  simp [verifyAlwaysAllows.allowAll, SymCC.isAuthorized, SymCC.satisfiedPolicies, compileWithEffect]
  simp [Policy.toExpr, PrincipalScope.toExpr, ActionScope.toExpr, ResourceScope.toExpr, Scope.toExpr, Conditions.toExpr, Condition.toExpr]
  simp [compile, compilePrim, compileAnd]
  simp [
    Factory.and, Factory.or, Factory.not, Factory.anyTrue, Factory.eq, Factory.eq.simplify, Factory.ite, Factory.ite.simplify,
    Factory.someOf, Factory.noneOf, Factory.ifSome, Factory.isNone, Factory.option.get, Term.typeOf, TermPrim.typeOf
  ]
