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

module

public import Cedar.SymCC.Enforcer -- TODO: this import need not be public
public import Cedar.SymCC.Authorizer -- TODO: this import need not be public
public import Cedar.SymCC.Compiler -- TODO: this import need not be public

/-!
This file contains `verify*` functions that use the Cedar symbolic compiler,
authorizer, and hierarchy enforcer to generate a list of `Asserts`. These are
boolean terms whose conjunction is unsatisfiable if and only if the verified
property holds.
-/

@[expose] public section -- TODO: make the public interface more granular/intentional, instead of having everything public and exposed

namespace Cedar.SymCC

open Factory Cedar.Spec

abbrev Asserts := List Term

/--
Returns asserts that are unsatisfiable iff the evaluation of `p`, represented as
a Term of type .option .bool, satisfies `φ` on all inputs drawn from `εnv`.  See also
`verifyNeverErrors`, `verifyAlwaysMatches`, and `verifyNeverMatches`.
-/
def verifyEvaluate (φ : Term → Term) (p : Policy) (εnv : SymEnv) : Result Asserts := do
  let x := p.toExpr
  let t ← compile x εnv
  (enforce [x] εnv).elts ++ [not (φ t)]

/--
Returns asserts that are unsatisfiable iff the evaluation of `p₁` and `p₂`,
represented as Terms of type .option .bool, satisfy `φ` on all inputs drawn from
`εnv`. See also `verifyMatchesImplies`, `verifyMatchesEquivalent`, and
`verifyMatchesDisjoint`.
-/
def verifyEvaluatePair (φ : Term → Term → Term) (p₁ p₂ : Policy) (εnv : SymEnv) : Result Asserts := do
  let x₁ := p₁.toExpr
  let x₂ := p₂.toExpr
  let t₁ ← compile x₁ εnv
  let t₂ ← compile x₂ εnv
  (enforce [x₁, x₂] εnv).elts ++ [not (φ t₁ t₂)]

/--
Returns asserts that are unsatisfiable iff the authorization decisions produced
by `ps₁` and `ps₂`, represented as Terms of type .bool, satisfy `φ` on all
inputs drawn from `εnv`. See also `verifyAlwaysAllows`, `verifyAlwaysDenies`,
`verifyImplies`, `verifyEquivalent`, and `verifyDisjoint`.
-/
def verifyIsAuthorized (φ : Term → Term → Term) (ps₁ ps₂ : Policies) (εnv : SymEnv) : Result Asserts := do
  let t₁ ← isAuthorized ps₁ εnv
  let t₂ ← isAuthorized ps₂ εnv
  let xs := (ps₁ ++ ps₂).map Policy.toExpr
  (enforce xs εnv).elts ++ [not (φ t₁ t₂)]

/--
Returns asserts that are unsatisfiable iff `p` does not error on any input in
`εnv`. If the asserts are satisfiable, then there is some input in `εnv` on
which `p` errors.
-/
def verifyNeverErrors (p : Policy) (εnv : SymEnv) : Result Asserts :=
  verifyEvaluate isSome p εnv

/--
Returns asserts that are unsatisfiable iff `p` matches all inputs in `εnv`.
If the asserts are satisfiable, then there is some input in `εnv` which `p`
doesn't match.
-/
def verifyAlwaysMatches (p : Policy) (εnv : SymEnv) : Result Asserts :=
  -- never errors, _and_ is always true
  verifyEvaluate (eq · (⊙true)) p εnv

/--
Returns asserts that are unsatisfiable iff `p` matches no inputs in `εnv`.
If the asserts are satisfiable, then there is some input in `εnv` which `p`
does match.
-/
def verifyNeverMatches (p : Policy) (εnv : SymEnv) : Result Asserts :=
  -- always evaluates to ⊙false _or_ error; i.e., never evaluates to ⊙true
  verifyEvaluate (λ t => not (eq t (⊙true))) p εnv

/--
Returns asserts that are unsatisfiable iff `p₁` and `p₂` match exactly the same
set of inputs in `εnv`.
-/
def verifyMatchesEquivalent (p₁ p₂ : Policy) (εnv : SymEnv) : Result Asserts :=
  verifyEvaluatePair (λ t₁ t₂ =>
    let t₁matches := eq t₁ (⊙true)
    let t₂matches := eq t₂ (⊙true)
    eq t₁matches t₂matches)
    p₁ p₂ εnv

/--
Returns asserts that are unsatisfiable iff `p₁` matching implies that `p₂`
matches, for every input in `εnv`. In other words, for every request where `p₁`
matches, `p₂` also matches.
-/
def verifyMatchesImplies (p₁ p₂ : Policy) (εnv : SymEnv) : Result Asserts :=
  verifyEvaluatePair (λ t₁ t₂ =>
    let t₁matches := eq t₁ (⊙true)
    let t₂matches := eq t₂ (⊙true)
    implies t₁matches t₂matches)
    p₁ p₂ εnv

/--
Returns asserts that are unsatisfiable iff there is no input in `εnv` that is
matched by both `p₁` and `p₂`. In other words, the sets of inputs matched by
`p₁` and `p₂` are disjoint. If this query is satisfiable, then there is at
least one input that is matched by both `p₁` and `p₂`.
-/
def verifyMatchesDisjoint (p₁ p₂ : Policy) (εnv : SymEnv) : Result Asserts :=
  verifyEvaluatePair (λ t₁ t₂ =>
    let t₁matches := eq t₁ (⊙true)
    let t₂matches := eq t₂ (⊙true)
    disjoint t₁matches t₂matches)
    p₁ p₂ εnv
where
  disjoint (t₁ t₂ : Term) := not (and t₁ t₂)

/--
Returns asserts that are unsatisfiable iff the authorization decision of `ps₁`
implies that of `ps₂` for every input in `εnv`. In other words, every input
allowed by `ps₁` is allowed by `ps₂`.
-/
def verifyImplies (ps₁ ps₂ : Policies) (εnv : SymEnv) : Result Asserts :=
  verifyIsAuthorized implies ps₁ ps₂ εnv

/--
Returns asserts that are unsatisfiable iff `ps` allows all inputs in `εnv`.
-/
def verifyAlwaysAllows (ps : Policies) (εnv : SymEnv) : Result Asserts := do
  verifyImplies [allowAll] ps εnv
where
  -- This policy chosen not because it's readable or optimized, but because it
  -- is the policy produced by `wellTypedPolicy Policy.allowAll Γ`
  allowAll : Policy := {
    id             := "allowAll",
    effect         := .permit,
    principalScope := .principalScope .any,
    actionScope    := .actionScope .any,
    resourceScope  := .resourceScope .any,
    condition      := [{
      kind := .when,
      body := Expr.and
        (.lit (.bool true))
        (Expr.and
          (.lit (.bool true))
          (Expr.and
            (.lit (.bool true))
            (.lit (.bool true))))
    }]
  }

/--
Returns asserts that are unsatisfiable iff `ps` denies all inputs in `εnv`.
-/
def verifyAlwaysDenies (ps : Policies) (εnv : SymEnv) : Result Asserts := do
  verifyImplies ps [] εnv

/--
Returns asserts that are unsatisfiable iff `ps₁` and `ps₂` produce the same
authorization decision on all inputs in `εnv`.
-/
def verifyEquivalent (ps₁ ps₂ : Policies) (εnv : SymEnv) : Result Asserts :=
  verifyIsAuthorized eq ps₁ ps₂ εnv

/--
Returns asserts that are unsatisfiable iff there is no input in `εnv` that is
allowed by both `ps₁` and `ps₂`.  This checks that the authorization semantics
of `ps₁` and `ps₂` are disjoint. If this query is satisfiable, then there is at
least one input that is allowed by both `ps₁` and `ps₂`.
-/
def verifyDisjoint (ps₁ ps₂ : Policies) (εnv : SymEnv) : Result Asserts :=
  verifyIsAuthorized disjoint ps₁ ps₂ εnv
where
  disjoint (t₁ t₂ : Term) := not (and t₁ t₂)

end Cedar.SymCC
