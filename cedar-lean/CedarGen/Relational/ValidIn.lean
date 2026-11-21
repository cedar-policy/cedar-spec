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

import Cedar.Thm.Validation.Relational
import Specimen

/-! # Checking a generated policy against the validator

`validIn ets acts envs p` runs `validate` on `p`, with `envs` in place of the schema's
environments. It is the decision procedure for `ValidPolicy` the policy generators end with,
so that whatever they produce is a policy the validator accepts. `validIn_iff` shows it
decides `ValidPolicy`. -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

def validIn (ets : EntitySchema) (acts : ActionSchema) (envs : List TypeEnv) (p : Policy) : Bool :=
  match checkEntities ⟨ets, acts⟩ p.toExpr, envs.mapM (typecheckPolicy p) with
  | .ok (), .ok txs => !allFalse txs
  | _, _ => false

instance : DecOpt (ValidPolicy ets acts envs p) where
  decOpt _ := .ok (validIn ets acts envs p)

/-- `validIn` decides `ValidPolicy`. -/
theorem validIn_iff {ets : EntitySchema} {acts : ActionSchema} {envs : List TypeEnv} {p : Policy}
    (hndE : (ets.toList.map Prod.fst).Nodup) (hndA : (acts.toList.map Prod.fst).Nodup)
    (hwf : ∀ env ∈ envs, EnvAssumptions env) :
    validIn ets acts envs p = true ↔ ValidPolicy ets acts envs p := by
  constructor
  · intro h
    cases hce : checkEntities ⟨ets, acts⟩ p.toExpr with
    | error e => simp [validIn, hce] at h
    | ok u =>
      cases hm : envs.mapM (typecheckPolicy p) with
      | error e => simp [validIn, hce, hm] at h
      | ok txs =>
        simp only [validIn, hce, hm, Bool.not_eq_eq_eq_not, Bool.not_true] at h
        obtain ⟨bs, hbs⟩ := mapM_typecheckPolicy_bool hm
        exact .mk _ _ _ _ _ bs (policyExpr_toExpr p) (entitiesDeclared_of_checkEntities hndE _ hce)
          ((typedInEnvs_iff hwf).mpr ⟨txs, hm, hbs⟩) ((allFalse_eq_false_iff hbs).mp h)
  · intro h
    cases h with
    | mk x bs hpe hent htyped hsome =>
      rw [hpe.eq_toExpr] at hent htyped
      obtain ⟨txs, hm, hbs⟩ := (typedInEnvs_iff hwf).mp htyped
      simp [validIn, hent.checkEntities_ok hndE hndA, hm, (allFalse_eq_false_iff hbs).mpr hsome]

end Cedar.Validation.Relational
