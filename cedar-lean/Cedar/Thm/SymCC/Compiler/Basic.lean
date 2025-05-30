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

import Cedar.Thm.SymCC.Data
import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Interpretation
import Cedar.Thm.SymCC.Term.Interpret
import Cedar.Thm.SymCC.Term.Lit
import Cedar.Thm.SymCC.Term.PE
import Cedar.Thm.SymCC.Term.Same
import Cedar.Thm.SymCC.Term.TypeOf
import Cedar.Thm.SymCC.Term.WF
import Cedar.Thm.SymCC.Tactics

/-!
This file contains basic definitions and lemmas for proofs about `compile`.
--/

namespace Cedar.Thm

open Spec SymCC Factory

def ReduceEvaluate (x : Expr) : Prop :=
  ∀ {env : Env} {εnv : SymEnv} {t : Term},
    env ∼ εnv →
    env.WellFormedFor x →
    εnv.WellFormedFor x →
    compile x εnv = .ok t →
    evaluate x env.request env.entities ∼ t

def ReduceInterpret (x : Expr) : Prop :=
  ∀ {εnv : SymEnv} {I : Interpretation} {t : Term},
    I.WellFormed εnv.entities →
    εnv.WellFormedFor x →
    compile x εnv = .ok t →
    compile x (εnv.interpret I) = .ok (t.interpret I)

end Cedar.Thm
