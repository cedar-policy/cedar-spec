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

import Cedar.TPE
import Cedar.TPE.Authorizer
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.Conversion
import Cedar.Thm.TPE.Policy
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.Authorization

/-!
Common lemmas describing the behavior of partial authorization in terms of
higher-level properties. These lemmas capture the relationship between residual
policy evaluation and concrete policy evaluation, eliminating repeated proof
structure across `Cedar.Thm.TPE` and `Cedar.Thm.TPE.Authorizer`.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm
/-- Extract the `Forall₂` relationship between policies and residual policies
from a successful `TPE.isAuthorized` call. This captures the common preamble
used in nearly every partial authorization soundness theorem. -/
theorem tpe_isAuthorized_forall₂
  {schema : Schema}
  {policies : List Policy}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {response : TPE.Response} :
  TPE.isAuthorized schema policies preq pes = Except.ok response →
  ∃ rps,
    List.Forall₂ (λ p rp => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes = Except.ok rp) policies rps ∧
    response = isAuthorized.isAuthorizedFromResiduals rps
:= by
  intro h
  simp only [TPE.isAuthorized] at h
  cases h₁ : List.mapM (λ p => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes) policies <;>
    simp only [bind_pure_comp, h₁, Except.map_ok, Except.map_error, Except.ok.injEq, reduceCtorEq] at h
  rw [List.mapM_ok_iff_forall₂] at h₁
  exact ⟨_, h₁, h.symm⟩

/-- If partial evaluation of a policy produces a residual `r`, and `r.isTrue`,
then the original policy is satisfied under concrete evaluation. -/
theorem residual_true_implies_policy_satisfied
  {schema : Schema}
  {p : Policy}
  {r : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  (h_eval : evaluatePolicy schema p preq pes = .ok r)
  (h_valid : isValidAndConsistent schema req es preq pes = .ok ())
  (h_true : r.isTrue) :
  Spec.evaluate p.toExpr req es = .ok (.prim (.bool true))
:= by
  have ⟨ty, hr⟩ : ∃ ty, r = .val (.prim (.bool true)) ty := by
    simp only [Residual.isTrue] at h_true; grind
  have ha := partial_evaluate_policy_is_sound h_eval h_valid
  simp only [hr, Residual.evaluate] at ha
  exact to_option_right_ok' ha

/-- If partial evaluation of a policy produces a residual `r`, and the original
policy is satisfied under concrete evaluation, then `r.evaluate req es = .ok true`. -/
theorem policy_satisfied_implies_residual_eval_true
  {schema : Schema}
  {p : Policy}
  {r : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  (h_eval : evaluatePolicy schema p preq pes = .ok r)
  (h_valid : isValidAndConsistent schema req es preq pes = .ok ())
  (h_sat : Spec.evaluate p.toExpr req es = .ok (.prim (.bool true))) :
  r.evaluate req es = .ok (.prim (.bool true))
:= by
  have ha := partial_evaluate_policy_is_sound h_eval h_valid
  rw [h_sat] at ha
  exact to_option_left_ok' ha
/-- If partial evaluation of a policy produces a residual `r`, and `r.isError`,
then the original policy errors under concrete evaluation. -/
theorem residual_error_implies_policy_error
  {schema : Schema}
  {p : Policy}
  {r : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  (h_eval : evaluatePolicy schema p preq pes = .ok r)
  (h_valid : isValidAndConsistent schema req es preq pes = .ok ())
  (h_err : r.isError) :
  ∃ e, Spec.evaluate p.toExpr req es = .error e
:= by
  have ⟨ty, hr⟩ : ∃ ty, r = .error ty := by
    simp only [Residual.isError] at h_err; grind
  have ha := partial_evaluate_policy_is_sound h_eval h_valid
  simp only [hr, Residual.evaluate] at ha
  exact to_option_right_err ha

/-- If partial evaluation of a policy produces a residual `r`, and the original
policy errors under concrete evaluation, then `r.evaluate req es` also errors. -/
theorem policy_error_implies_residual_eval_error
  {schema : Schema}
  {p : Policy}
  {r : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  (h_eval : evaluatePolicy schema p preq pes = .ok r)
  (h_valid : isValidAndConsistent schema req es preq pes = .ok ())
  (h_err : ∃ e, Spec.evaluate p.toExpr req es = .error e) :
  ∃ e, r.evaluate req es = .error e
:= by
  have ⟨e, h_err⟩ := h_err
  have ha := partial_evaluate_policy_is_sound h_eval h_valid
  rw [h_err] at ha
  exact to_option_left_err ha

/-- If partial evaluation of a policy produces a residual that is `val false`,
then the original policy is not satisfied under concrete evaluation. -/
theorem residual_false_implies_policy_not_satisfied
  {schema : Schema}
  {p : Policy}
  {r : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  (h_eval : evaluatePolicy schema p preq pes = .ok r)
  (h_valid : isValidAndConsistent schema req es preq pes = .ok ())
  (h_false : r.isFalse) :
  ¬ satisfied p req es
:= by
  have ⟨ty, hr⟩ : ∃ ty, r = .val (.prim (.bool false)) ty := by
    simp only [Residual.isFalse] at h_false; grind
  have ha := partial_evaluate_policy_is_sound h_eval h_valid
  simp only [hr, Residual.evaluate] at ha
  simp only [satisfied, decide_eq_true_eq]
  intro h_sat
  rw [h_sat] at ha
  simp [Except.toOption] at ha

/-- Combined lemma: if a residual is true or false or error, the concrete
evaluation matches. If the residual is none of these (i.e., it's a proper
residual expression), then the concrete evaluation result is determined by
evaluating the residual. -/
theorem residual_satisfied_iff_policy_satisfied
  {schema : Schema}
  {p : Policy}
  {r : Residual}
  {req : Request}
  {es : Entities}
  {preq : PartialRequest}
  {pes : PartialEntities}
  (h_eval : evaluatePolicy schema p preq pes = .ok r)
  (h_valid : isValidAndConsistent schema req es preq pes = .ok ()) :
  (Spec.evaluate p.toExpr req es).toOption = (r.evaluate req es).toOption
:= partial_evaluate_policy_is_sound h_eval h_valid
/-- Given the `Forall₂` relationship from partial authorization, if a residual
policy `rp` is in the residual list, then there exists a corresponding policy
`p` in the original list with matching id and effect, and `evaluatePolicy`
produced the residual. -/
theorem forall₂_residual_to_policy
  {schema : Schema}
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {rp : ResidualPolicy}
  (h_forall : List.Forall₂ (λ p rp => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes = Except.ok rp) policies rps)
  (h_mem : rp ∈ rps) :
  ∃ p ∈ policies, ∃ r, evaluatePolicy schema p preq pes = .ok r ∧ rp = ⟨p.id, p.effect, r⟩
:= by
  have ⟨p, hp₁, hp₂⟩ := List.forall₂_implies_all_right h_forall rp h_mem
  cases hp₃ : evaluatePolicy schema p preq pes <;>
    simp only [hp₃, Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at hp₂
  exact ⟨p, hp₁, _, hp₃, hp₂.symm⟩

/-- Given the `Forall₂` relationship from partial authorization, if a policy
`p` is in the original list, then there exists a corresponding residual policy
in the residual list, and `evaluatePolicy` produced the residual. -/
theorem forall₂_policy_to_residual
  {schema : Schema}
  {policies : List Policy}
  {rps : List ResidualPolicy}
  {preq : PartialRequest}
  {pes : PartialEntities}
  {p : Policy}
  (h_forall : List.Forall₂ (λ p rp => ResidualPolicy.mk p.id p.effect <$> evaluatePolicy schema p preq pes = Except.ok rp) policies rps)
  (h_mem : p ∈ policies) :
  ∃ rp ∈ rps, ∃ r, evaluatePolicy schema p preq pes = .ok r ∧ rp = ⟨p.id, p.effect, r⟩
:= by
  have ⟨rp, hrp₁, hrp₂⟩ := List.forall₂_implies_all_left h_forall p h_mem
  cases hrp₃ : evaluatePolicy schema p preq pes <;>
    simp only [hrp₃, Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at hrp₂
  exact ⟨rp, hrp₁, _, rfl, hrp₂.symm⟩

end Cedar.Thm
