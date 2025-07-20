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

import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Term.Interpret.WF

/-!
This file contains the soundness theorems of `Sym.ofEnv`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC
open Cedar.Validation
open Cedar.Data

/--
Inverse of `entity_uid_wf_implies_sym_entities_is_valid_entity_uid`
-/
theorem sym_entities_is_valid_entity_uid_implies_entity_uid_wf
  {Γ : TypeEnv} {uid : EntityUID}
  (hwf : Γ.WellFormed)
  (huid : (SymEnv.ofEnv Γ).entities.isValidEntityUID uid) :
  EntityUID.WellFormed Γ uid
:= by
  sorry

/--
If a term type is both the result of
`TermType.ofType` and `Term.typeOf`
for some well-formed `CedarType`
and well-formed `Term`,
then the if the the term is conretizable (via `value?`),
the resulting `Value` should be well-typed.

         ofType
TermType <----- CedarType
   ^               ^
   |               *
   | typeOf        * InstanceOfType
   |               *
   |               *
 Term ---------> Value
        value?
-/
theorem ofType_typeOf_pullback
  {Γ : TypeEnv}
  {t : Term} {ty : CedarType} {v : Value}
  (hwf_Γ : Γ.WellFormed)
  (hwf_ty : ty.WellFormed Γ)
  (hwf_t : t.WellFormed (SymEnv.ofEnv Γ).entities)
  (heq : t.typeOf = TermType.ofType ty)
  (hval : t.value? = .some v) :
  InstanceOfType Γ v ty
:= by
  cases t with
  | prim p =>
    cases p with
    | bool b =>
      simp only [Term.typeOf, TermPrim.typeOf, TermType.bool] at heq
      unfold TermType.ofType at heq
      split at heq
      any_goals simp only [TermType.prim.injEq, reduceCtorEq] at heq
      simp only [Term.value?, TermPrim.value?, Option.some.injEq] at hval
      simp only [←hval]
      constructor

      sorry
    | _ =>
      sorry
  | _ => sorry

theorem ofEnv_request_completeness
  {Γ : TypeEnv} {env : Env} {I : Interpretation}
  (hwf_Γ : Γ.WellFormed)
  (hwf_env : env.StronglyWellFormed)
  (hwf_I : I.WellFormed (SymEnv.ofEnv Γ).entities)
  (hsame_I : env ∼ SymEnv.interpret I (SymEnv.ofEnv Γ)) :
  InstanceOfRequestType env.request Γ
:= by
  have ⟨hwf_I_vars, _⟩ := hwf_I
  have ⟨⟨hsame_I_princ, hsame_I_act, hsame_I_res, hsame_I_ctx⟩, _⟩ := hsame_I
  have hwf_sym_req := ofEnv_request_is_swf hwf_Γ
  have ⟨⟨hwf_sym_princ, _, hwf_sym_act, _, hwf_sym_res, _, hwf_sym_ctx, _⟩, _⟩ := hwf_sym_req
  simp only [
    SymEnv.interpret,
    SymRequest.interpret,
  ] at hsame_I_princ hsame_I_act hsame_I_res hsame_I_ctx
  and_intros
  -- Well-formed symbolic principal => well-formed concrete principal
  · have ⟨_, hwt_I_princ⟩ := interpret_term_wf hwf_I hwf_sym_princ
    simp only [hsame_I_princ, Term.typeOf, TermPrim.typeOf] at hwt_I_princ
    simp only [
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
      Term.typeOf,
      TermType.ofType,
    ] at hwt_I_princ
    simp only [TermType.prim.injEq, TermPrimType.entity.injEq] at hwt_I_princ
    simp [hwt_I_princ]
  · have ⟨hwf_I_princ, _⟩ := interpret_term_wf hwf_I hwf_sym_princ
    simp only [hsame_I_princ] at hwf_I_princ
    cases hwf_I_princ with | prim_wf hwf_I_princ =>
    cases hwf_I_princ with | entity_wf hwf_I_princ =>
    exact sym_entities_is_valid_entity_uid_implies_entity_uid_wf hwf_Γ hwf_I_princ
  -- Well-formed symbolic action => well-formed concrete action
  · simp only [
      Term.interpret,
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
    ] at hsame_I_act
    simp only [Term.prim.injEq, TermPrim.entity.injEq] at hsame_I_act
    simp [hsame_I_act]
  -- Well-formed symbolic resource => well-formed concrete resource
  · have ⟨_, hwt_I_res⟩ := interpret_term_wf hwf_I hwf_sym_res
    simp only [hsame_I_res, Term.typeOf, TermPrim.typeOf] at hwt_I_res
    simp only [
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
      Term.typeOf,
      TermType.ofType,
    ] at hwt_I_res
    simp only [TermType.prim.injEq, TermPrimType.entity.injEq] at hwt_I_res
    simp [hwt_I_res]
  · have ⟨hwf_I_res, _⟩ := interpret_term_wf hwf_I hwf_sym_res
    simp only [hsame_I_res] at hwf_I_res
    cases hwf_I_res with | prim_wf hwf_I_res =>
    cases hwf_I_res with | entity_wf hwf_I_res =>
    exact sym_entities_is_valid_entity_uid_implies_entity_uid_wf hwf_Γ hwf_I_res
  · have ⟨hwf_I_ctx, hwt_I_ctx⟩ := interpret_term_wf hwf_I hwf_sym_ctx
    simp only [
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
      Term.typeOf,
    ] at hwt_I_ctx
    simp only [
      SameValues,
      SymEnv.ofEnv,
      SymRequest.ofRequestType,
    ] at hsame_I_ctx
    have ⟨_, _, _, hwt_ctx⟩ := wf_env_implies_wf_request hwf_Γ
    apply ofType_typeOf_pullback hwf_Γ hwt_ctx hwf_I_ctx hwt_I_ctx hsame_I_ctx
    -- Ideally we should have the "commuting" diagram (modulo `.some`)
    --        cedarType?
    --          ----->
    --          ofType
    -- TermType <----- CedarType
    --    ^               ^
    --    |               |
    --    | typeOf        | InstanceOfType
    --    |               |
    --    |               |
    --  Term ---------> Value
    --         value?
    --       <---------
    --       symbolize?

theorem ofEnv_completeness
  {Γ : TypeEnv} {env : Env}
  (hwf : Γ.WellFormed)
  (hwf_env : env.StronglyWellFormed)
  (hinst : env ∈ᵢ SymEnv.ofEnv Γ) :
  InstanceOfWellFormedEnvironment env.request env.entities Γ
:= by
  constructor
  · exact hwf
  have ⟨I, hwf_I, hsame_I⟩ := hinst
  constructor
  · exact ofEnv_request_completeness hwf hwf_env hwf_I hsame_I
  · sorry

end Cedar.Thm
