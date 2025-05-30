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

import Cedar.SymCC.Enforcer
import Cedar.SymCC.Compiler

/-!

This file defines the Cedar symbolic authorizer.

The symbolic authorizer takes as input a set of policies and a symbolic
environment. Given these inputs, it produces a Term encoding of the
authorization decision for those policies. The output term is of type boolean.
If this boolean term evaluates to true, then access is allowed. Otherwise,
access is denied.

-/

namespace Cedar.SymCC

open Factory Cedar.Spec

def compileWithEffect (effect : Effect) (policy : Policy) (εnv : SymEnv) : Result (Option Term) :=
  if policy.effect == effect
  then compile policy.toExpr εnv
  else .ok .none

def satisfiedPolicies (effect : Effect) (policies : Policies) (εnv : SymEnv) : Result Term := do
  let ts ← policies.filterMapM (compileWithEffect effect · εnv)
  anyTrue (eq · (someOf true)) ts

def isAuthorized (policies : Policies) (εnv : SymEnv) : Result Term := do
  let forbids ← satisfiedPolicies .forbid policies εnv
  let permits ← satisfiedPolicies .permit policies εnv
  and permits (not forbids)

end Cedar.SymCC
