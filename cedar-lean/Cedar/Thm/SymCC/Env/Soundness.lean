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
import Cedar.SymCC.Concretizer
import Cedar.SymCC.Symbolizer
import Cedar.SymCC.Env

/-!
This file contains the soundness theorems of `Sym.ofEnv`
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Spec
open Cedar.SymCC
open Cedar.Validation

/--
`Value.symbolize?` is total on well-typed values,
and the resulting term is a well-formed literal
-/
theorem value_symbolize?_same
  {Γ : TypeEnv} {v : Value} {ty : CedarType}
  (hwf : Γ.WellFormed)
  (hwf_ty : ty.WellFormed Γ)
  (hwt : InstanceOfType Γ v ty) :
  ∃ t,
    v.symbolize? ty = .some t ∧
    v ∼ t
:= by
  cases hwt with
  | instance_of_bool
  | instance_of_string
  | instance_of_entity
  | instance_of_ext
  | instance_of_int =>
    simp [
      Value.symbolize?, Prim.symbolize,
      Same.same, SameValues,
      Term.value?, TermPrim.value?, BitVec.int64?,
    ]
  | instance_of_set s sty hwt =>
    simp [Value.symbolize?]
    sorry
  | instance_of_record rec =>
    sorry

theorem env_symbolize?_same_request
  {Γ : TypeEnv} {env : Env}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env.request ∼ ((SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)).request
:= by
  have hwf := hinst.wf_env
  simp only [
    SymEnv.interpret,
    Env.symbolize?,
    SymEnv.ofEnv,
    SymRequest.ofRequestType,
    SymRequest.interpret,
    Request.symbolize?,
    Value.symbolize?,
    Prim.symbolize,
  ]
  and_intros
  all_goals
    simp only [Term.interpret]
  -- Actions match
  · have ⟨_, ⟨_, h, _, _⟩, _⟩ := hinst
    simp [h]
  -- Same context after interpretation
  · have hwf_ctx_ty : (CedarType.record Γ.reqty.context).WellFormed Γ := by
      have ⟨_, _, _, h⟩ := wf_env_implies_wf_request hwf
      exact h
    have hwt_ctx : InstanceOfType Γ env.request.context (.record Γ.reqty.context) := by
      have ⟨_, ⟨_, _, _, h⟩, _⟩ := hinst
      exact h
    have ⟨sym_ctx, hsym_ctx, hsame_sym_ctx⟩ := value_symbolize?_same hwf hwf_ctx_ty hwt_ctx
    simp only [Value.symbolize?, Option.bind_eq_bind] at hsym_ctx
    simp only [Option.bind_eq_bind, hsym_ctx]
    exact hsame_sym_ctx

theorem env_symbolize?_same_entities
  {Γ : TypeEnv} {env : Env}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env.entities ∼ ((SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)).entities
:= by
  sorry

theorem env_symbolize?_same
  {Γ : TypeEnv} {env : Env}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env ∼ (SymEnv.ofEnv Γ).interpret (env.symbolize? Γ)
:= by
  constructor
  · exact env_symbolize?_same_request hinst
  · exact env_symbolize?_same_entities hinst

theorem ofEnv_soundness
  {Γ : TypeEnv} {env : Env}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ) :
  env ∈ᵢ SymEnv.ofEnv Γ
:= by
  have ⟨hwf, hinst_req, hinst_sch⟩ := hinst
  exists env.symbolize? Γ
  constructor
  · sorry
  . exact env_symbolize?_same hinst

end Cedar.Thm
