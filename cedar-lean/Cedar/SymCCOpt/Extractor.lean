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
Optimized version of `extract?` in `SymCC/Extractor.lean`.

Caller guarantees that all of the `CompiledPolicy`s and/or `CompiledPolicies` were compiled for the same `εnv`.
-/
def extractOpt? (cpₛs : List CompiledPolicyₛ) (I : Interpretation) : Option Env :=
  match cpₛs with
  | [] => none
  | cpₛ :: _ =>
    let ps := cpₛs.flatMap CompiledPolicyₛ.allPolicies
    let footprint := cpₛs.mapUnion CompiledPolicyₛ.footprint
    let εnv := cpₛ.εnv
    SymEnv.concretize? (Expr.set (ps.map Policy.toExpr)) (εnv.interpret (I.repair footprint εnv))

end Cedar.SymCC
