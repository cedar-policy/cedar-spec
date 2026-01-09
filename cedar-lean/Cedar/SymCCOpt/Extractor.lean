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

import Cedar.SymCC.Extractor
import Cedar.SymCCOpt.CompiledPolicies

/-!
# Extracting strongly well-formed counterexamples to verification queries

This file defines the function `extractOpt?`, which turns interpretations
into concrete, strongly well-formed counterexamples to verification queries.

See notes on the unoptimized version, `extract?` in `SymCC/Extractor.lean`.

This optimized version is proved equivalent to the unoptimized version in `Thm/SymCC/Opt.lean`.
-/

namespace Cedar.SymCC

open Data Factory Spec

/--
Caller guarantees that all of the `CompiledPolicies` were compiled for the same `εnv`.
-/
def CompiledPolicies.extractOpt? (cps : List CompiledPolicies) (I : Interpretation) : Option Env :=
  match cps with
  | [] => none
  | { εnv, .. } :: _ =>
    let ps := List.flatten $ cps.map CompiledPolicies.policies
    let footprint := cps.mapUnion CompiledPolicies.footprint
    SymEnv.concretize? (Expr.set (ps.map Policy.toExpr)) (εnv.interpret (I.repair footprint εnv))

/--
Like `CompiledPolicies.extractOpt?`, but takes a list of `CompiledPolicy` rather
than `CompiledPolicies`.

Caller guarantees that all of the `CompiledPolicy`s were compiled for the same `εnv`.
-/
def CompiledPolicy.extractOpt? (cps : List CompiledPolicy) (I : Interpretation) : Option Env :=
  match cps with
  | [] => none
  | { εnv, .. } :: _ =>
    let ps := cps.map CompiledPolicy.policy
    let footprint := cps.mapUnion CompiledPolicy.footprint
    SymEnv.concretize? (Expr.set (ps.map Policy.toExpr)) (εnv.interpret (I.repair footprint εnv))

end Cedar.SymCC
