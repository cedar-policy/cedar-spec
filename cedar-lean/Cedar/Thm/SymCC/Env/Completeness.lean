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

import Cedar.Thm.Validation.Typechecker.Types
import Cedar.Thm.SymCC.Concretizer
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Term.Interpret
import Cedar.SymCC.Concretizer
import Cedar.SymCC.Env

/-!
This file contains the completeness theorems of `Sym.ofEnv`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC
open Cedar.Validation

theorem ofEnv_valid_uid_implies_wf_uid
  {Γ : TypeEnv} {uid : EntityUID}
  (h : (SymEnv.ofEnv Γ).entities.isValidEntityUID uid) :
  EntityUID.WellFormed Γ uid
:= sorry

theorem ofEnv_request_completeness
  {Γ : TypeEnv} {req : Request} {I : Interpretation}
  (hwf : Γ.WellFormed)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hsame_I : req ∼ (SymEnv.ofEnv Γ).request.interpret I) :
  InstanceOfRequestType req Γ
:= by
  have ⟨hwf_vars, _⟩ := hwf_I
  have hwf_εnv := ofEnv_is_wf hwf
  have ⟨hwf_req, _⟩ := hwf_εnv
  simp only [
    Same.same, SameRequests, SymRequest.interpret,
    SymEnv.ofEnv, SymRequest.ofRequestType,
    Term.interpret, Term.prim.injEq, TermPrim.entity.injEq,
  ] at hsame_I hwf_req
  -- The original symbolic principal/action/resource/context are well-formed
  have ⟨hwf_princ, _, hwf_act, _, hwf_res, _, hwf_ctx, _⟩ := hwf_req
  -- The interpreted principal/action/resource/context are well-formed
  have ⟨hwf_I_princ, hty_I_princ⟩ := interpret_term_wf hwf_I hwf_princ
  simp only [Term.typeOf, TermType.ofType, Term.interpret] at hwf_I_princ hty_I_princ
  have ⟨hwf_I_act, hty_I_act⟩ := interpret_term_wf hwf_I hwf_act
  simp only [Term.typeOf, TermType.ofType, Term.interpret] at hwf_I_act hty_I_act
  have ⟨hwf_I_res, hty_I_res⟩ := interpret_term_wf hwf_I hwf_res
  simp only [Term.typeOf, TermType.ofType, Term.interpret] at hwf_I_res hty_I_res
  have ⟨hwf_I_ctx, hty_I_ctx⟩ := interpret_term_wf hwf_I hwf_ctx
  simp only [Term.typeOf, TermType.ofType, Term.interpret] at hwf_I_ctx hty_I_ctx
  -- Interpretation equals the concrete version
  have ⟨hsame_princ, hsame_act, hsame_res, hsame_ctx⟩ := hsame_I
  simp only [TermType.ofType] at hsame_princ hsame_res
  simp only [hsame_princ] at hwf_I_princ hty_I_princ
  simp only [hsame_res] at hwf_I_res hty_I_res
  simp only [SameValues] at hsame_ctx
  -- simp only [hsame_ctx] at hwf_I_ctx hty_I_ctx
  and_intros
  -- The concrete principal is well-formed and -typed
  · simp only [
      Term.typeOf, TermPrim.typeOf, TermType.ofType,
      TermType.prim.injEq,
      TermPrimType.entity.injEq,
    ] at hty_I_princ
    simp [hty_I_princ]
  · cases hwf_I_princ with | prim_wf hwf_I_princ =>
    cases hwf_I_princ with | entity_wf hwf_I_princ =>
    apply ofEnv_valid_uid_implies_wf_uid
    exact hwf_I_princ
  -- The concrete action is correct
  · simp [hsame_act]
  -- The concrete resource is well-formed and -typed
  · simp only [
      Term.typeOf, TermPrim.typeOf, TermType.ofType,
      TermType.prim.injEq,
      TermPrimType.entity.injEq,
    ] at hty_I_res
    simp [hty_I_res]
  · cases hwf_I_res with | prim_wf hwf_I_res =>
    cases hwf_I_res with | entity_wf hwf_I_res =>
    apply ofEnv_valid_uid_implies_wf_uid
    exact hwf_I_res
  -- The concrete context is well-formed and -typed
  · -- Need the fact that if a term is well-formed and well-typed
    -- then interpreting and concretizing it (`value?`) produces a
    -- well-typed expression (in the sense of `InstanceOfType`)
    --
    -- We have something weaker `term_prim_value?_some_implies_ws`
    -- but it only shows well-structuredness (i.e. all `Map` and `Set`)
    -- are well-formed
    sorry
  all_goals sorry

theorem ofEnv_completeness
  {Γ : TypeEnv} {env : Env}
  (hwf : Γ.WellFormed)
  (hmem : env ∈ᵢ SymEnv.ofEnv Γ) :
  InstanceOfWellFormedEnvironment env.request env.entities Γ
:= by
  have ⟨I, hwf_I, hsame_I⟩ := hmem
  constructor
  · exact hwf
  constructor
  · apply ofEnv_request_completeness hwf hwf_I hsame_I.1
  sorry

end Cedar.Thm
