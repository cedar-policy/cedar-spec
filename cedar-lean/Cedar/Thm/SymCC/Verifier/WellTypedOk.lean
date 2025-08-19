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

import Cedar.Thm.SymbolicCompilation
import Cedar.Thm.SymCC.WellTyped

/-! `verify*` functions always succeed on well-formed inputs. --/

namespace Cedar.Thm

open Spec SymCC Validation

/-- `verifyEvaluate` succeeds on sufficiently well-formed inputs. -/
theorem verifyEvaluate_is_ok {φ : Term → Term} {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .some p') :
  ∃ asserts, verifyEvaluate φ p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨tx, hwt_tx, heq_tx⟩ := wellTypedPolicy_some_implies_well_typed_expr hwt
  simp only [verifyEvaluate]
  have ⟨_, hok, _⟩ := compile_well_typed hwf hwt_tx
  simp only [heq_tx] at hok
  simp [hok]

/-- `compileWithEffect` succeeds on sufficiently well-formed inputs. -/
theorem compileWithEffect_is_ok (effect : Effect) {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .some p') :
  ∃ asserts, compileWithEffect effect p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨tx, hwt_tx, heq_tx⟩ := wellTypedPolicy_some_implies_well_typed_expr hwt
  simp only [compileWithEffect]
  have ⟨_, hok, _⟩ := compile_well_typed hwf hwt_tx
  simp only [heq_tx] at hok
  simp only [hok]
  split <;> simp

/-- `satisfiedPolicies` succeeds on sufficiently well-formed inputs. -/
theorem satisfiedPolicies_is_ok (effect : Effect) {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .some ps') :
  ∃ asserts, satisfiedPolicies effect ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [SymCC.satisfiedPolicies]
  have ⟨ts, hts⟩ :
    ∃ ts,
      List.filterMapM (fun x => compileWithEffect effect x (SymEnv.ofEnv Γ)) ps' = .ok ts
  := by
    induction ps' generalizing ps with
    | nil => exists []
    | cons hd tl ih =>
      simp only [List.filterMapM_cons]
      have hwt_policies := List.mapM_some_implies_all_from_some hwt
      have ⟨p, hmem_p, hwt_p⟩ := hwt_policies hd List.mem_cons_self
      have ⟨asserts, hasserts⟩ := compileWithEffect_is_ok effect hwf hwt_p
      simp only [hasserts, bind_pure_comp, Except.bind_ok]
      cases ps with
      | nil => contradiction
      | cons ps_hd ps_tl =>
        simp only [
          wellTypedPolicies, List.mapM_cons,
          Option.pure_def,
          bind, Option.bind,
        ] at hwt
        split at hwt
        contradiction
        simp only at hwt
        split at hwt
        contradiction
        rename_i heq
        simp only [Option.some.injEq, List.cons.injEq] at hwt
        simp only [hwt.2] at heq
        have ⟨ts_tl, hts_tl⟩ := ih heq
        split
        · exists ts_tl
        · simp [hts_tl]
  simp [hts]

/-- `isAuthorized` succeeds on sufficiently well-formed inputs. -/
theorem isAuthorized_is_ok {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .some ps') :
  ∃ asserts, isAuthorized ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [SymCC.isAuthorized]
  have ⟨_, h₁⟩ := satisfiedPolicies_is_ok .forbid hwf hwt
  have ⟨_, h₂⟩ := satisfiedPolicies_is_ok .permit hwf hwt
  simp [h₁, h₂]

/-- `verifyIsAuthorized` succeeds on sufficiently well-formed inputs. -/
theorem verifyIsAuthorized_is_ok (φ : Term → Term → Term) {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .some ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .some ps₂') :
  ∃ asserts, verifyIsAuthorized φ ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [verifyIsAuthorized]
  have ⟨_, h₁⟩ := isAuthorized_is_ok hwf hwt₁
  have ⟨_, h₂⟩ := isAuthorized_is_ok hwf hwt₂
  simp [h₁, h₂]

/-- `verifyNeverErrors` succeeds on sufficiently well-formed inputs. -/
theorem verifyNeverErrors_is_ok {p p' : Policy} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicy p Γ = .some p') :
  ∃ asserts, verifyNeverErrors p' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyEvaluate_is_ok hwf hwt

/-- `verifyImplies` succeeds on sufficiently well-formed inputs. -/
theorem verifyImplies_is_ok {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .some ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .some ps₂') :
  ∃ asserts, verifyImplies ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyIsAuthorized_is_ok _ hwf hwt₁ hwt₂

private theorem compileWithEffect_allowAll_is_ok (effect : Effect) (Γ : TypeEnv) :
  ∃ asserts, compileWithEffect effect verifyAlwaysAllows.allowAll (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [compileWithEffect]
  split
  · simp [
      verifyAlwaysAllows.allowAll,
      Policy.toExpr,
      Scope.toExpr,
      PrincipalScope.toExpr,
      ActionScope.toExpr,
      ResourceScope.toExpr,
      Conditions.toExpr,
      compile,
      compilePrim,
      compileAnd,
      Term.typeOf,
      TermPrim.typeOf,
      Factory.someOf,
      Factory.ifSome,
      Factory.ite,
      Factory.noneOf,
      Factory.ite.simplify,
      Factory.isNone,
      Factory.option.get,
    ]
  · simp

private theorem satisfiedPolicies_allowAll_is_ok (effect : Effect) (Γ : TypeEnv) :
  ∃ asserts, satisfiedPolicies effect [verifyAlwaysAllows.allowAll] (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [SymCC.satisfiedPolicies]
  have ⟨_, h⟩ := compileWithEffect_allowAll_is_ok effect Γ
  simp only [
    h,
    List.filterMapM, List.filterMapM.loop,
    List.reverse_nil, List.reverse_cons,
    List.nil_append, Except.bind_ok,
  ]
  split <;> simp

private theorem isAuthorized_allowAll_is_ok (Γ : TypeEnv) :
  ∃ asserts, isAuthorized [verifyAlwaysAllows.allowAll] (SymEnv.ofEnv Γ) = .ok asserts
:= by
  simp only [SymCC.isAuthorized]
  have ⟨_, h₁⟩ := satisfiedPolicies_allowAll_is_ok .permit Γ
  have ⟨_, h₂⟩ := satisfiedPolicies_allowAll_is_ok .forbid Γ
  simp [h₁, h₂]

/-- `verifyAlwaysAllows` succeeds on sufficiently well-formed inputs. -/
theorem verifyAlwaysAllows_is_ok {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .some ps') :
  ∃ asserts, verifyAlwaysAllows ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨_, h₁⟩ := isAuthorized_is_ok hwf hwt
  have ⟨_, h₂⟩ := isAuthorized_allowAll_is_ok Γ
  simp [
    verifyAlwaysAllows,
    verifyImplies,
    verifyIsAuthorized,
    h₁, h₂,
  ]

/-- `verifyAlwaysDenies` succeeds on sufficiently well-formed inputs. -/
theorem verifyAlwaysDenies_is_ok {ps ps' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt : wellTypedPolicies ps Γ = .some ps') :
  ∃ asserts, verifyAlwaysDenies ps' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  have ⟨_, h⟩ := isAuthorized_is_ok hwf hwt
  simp only [
    h, verifyAlwaysDenies,
    verifyImplies,
    verifyIsAuthorized,
  ]
  simp [SymCC.isAuthorized, SymCC.satisfiedPolicies]

/-- `verifyEquivalent` succeeds on sufficiently well-formed inputs. -/
theorem verifyEquivalent_is_ok {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .some ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .some ps₂') :
  ∃ asserts, verifyEquivalent ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyIsAuthorized_is_ok _ hwf hwt₁ hwt₂

/-- `verifyDisjoint` succeeds on sufficiently well-formed inputs. -/
theorem verifyDisjoint_is_ok {ps₁ ps₁' ps₂ ps₂' : Policies} {Γ : TypeEnv}
  (hwf : Γ.WellFormed)
  (hwt₁ : wellTypedPolicies ps₁ Γ = .some ps₁')
  (hwt₂ : wellTypedPolicies ps₂ Γ = .some ps₂') :
  ∃ asserts, verifyDisjoint ps₁' ps₂' (SymEnv.ofEnv Γ) = .ok asserts
:= by
  exact verifyIsAuthorized_is_ok _ hwf hwt₁ hwt₂

end Cedar.Thm
