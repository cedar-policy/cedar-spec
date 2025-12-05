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

import Cedar.SymCCOpt.Compiler

namespace Cedar.SymCC.Opt

open Factory Cedar.Spec

def compileWithEffect (effect : Effect) (policy : Policy) (εnv : SymEnv) : Result (Option CompileResult) :=
  if policy.effect == effect
  then Opt.compile policy.toExpr εnv
  else .ok .none

def satisfiedPolicies (effect : Effect) (policies : Policies) (εnv : SymEnv) : Result CompileResult := do
  let ress ← policies.filterMapM (compileWithEffect effect · εnv)
  .ok {
    term := anyTrue (eq · (someOf true)) (ress.map CompileResult.term)
    footprint := ress.mapUnion CompileResult.footprint
  }

def isAuthorized (policies : Policies) (εnv : SymEnv) : Result CompileResult := do
  let forbids ← satisfiedPolicies .forbid policies εnv
  let permits ← satisfiedPolicies .permit policies εnv
  .ok {
    term := and permits.term (not forbids.term)
    footprint := permits.footprint ∪ forbids.footprint
  }

end Cedar.SymCC.Opt
