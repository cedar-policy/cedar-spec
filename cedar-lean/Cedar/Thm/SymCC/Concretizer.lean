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
import Cedar.Thm.SymCC.Concretizer.Lit
import Cedar.Thm.SymCC.Concretizer.Same
import Cedar.Thm.SymCC.Concretizer.WF
import Cedar.Thm.SymCC.Env.Interpret

/-!
This file proves a key auxiliary lemma used to show the completeness of Cedar's
symbolic compiler: for every symbolic environment `εnv` that is well-formed for
an expression `x`, and for interpretation `I` that is well-formed for εnv, there
is concrete environment `env` that is well-formed with respect to `x` and that
corresponds to the interpretation of `εnv` under `I`. The concrete environment
`env` is obtained by concretizing `εnv.interpret I` with respect to `x`.
--/

namespace Cedar.Thm

open Spec SymCC

theorem exists_wf_env {x : Expr} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormedFor x →
  I.WellFormed εnv.entities →
  ∃ (env : Env),
    env ∼ εnv.interpret I ∧
    env.WellFormedFor x
:= by
  intro hwε hI
  have hlit := interpret_εnv_lit hwε.left hI
  replace hwε := interpret_εnv_wf_for_expr hwε hI
  have ⟨env, h⟩ := concretize?_wfl_implies_some (And.intro hwε hlit)
  exists env
  simp only [
    concretize?_some_same hwε h,
    concretize?_some_wf hwε h,
    and_self]

theorem exists_wf_env_for_policies {ps : Policies} {εnv : SymEnv} {I : Interpretation} :
  εnv.WellFormedForPolicies ps →
  I.WellFormed εnv.entities →
  ∃ (env : Env),
    env ∼ εnv.interpret I ∧
    env.WellFormedForPolicies ps
:= by
  intro hwε hI
  rw [wf_εnv_for_policies_iff_wf_εnv_for_set] at hwε
  have ⟨env, heq, hwe⟩ := exists_wf_env hwε hI
  exists env
  simp only [heq, wf_env_for_policies_iff_wf_env_for_set, hwe, and_self]

end Cedar.Thm
