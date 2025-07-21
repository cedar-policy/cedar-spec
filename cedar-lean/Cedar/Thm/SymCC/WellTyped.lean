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
import Cedar.Thm.Validation.SubstituteAction
import Cedar.Thm.Validation.Typechecker.Basic

/-! This file contains some results about `wellTypedPolicies` and `wellTypedPolicy`. -/

namespace Cedar.Thm

open Spec SymCC Validation

/-
Given `wellTypedPolicy p Γ = .some p'`
WTS:
- `env.StronglyWellFormedForPolicy p → env.StronglyWellFormedForPolicy p'`
- `evaluate p.toExpr env.request env.entities = evaluate p'.toExpr env.request env.entities`

Given wellTypedPolicies ps Γ = .some ps'
- `env.StronglyWellFormedForPolicies ps → env.StronglyWellFormedForPolicies ps'`
- `Spec.isAuthorized env.request env.entities ps = Spec.isAuthorized env.request env.entities ps'`
-/

/--
Reduces `wellTypedPolicy` being `some` to the existence of `TypedExpr`s.
-/
theorem wellTypedPolicy_some_implies_exists_typed_exprs
  {Γ : TypeEnv} {p p' : Policy}
  (hsome : wellTypedPolicy p Γ = .some p') :
  ∃ tx tx' : TypedExpr, ∃ c,
    TypedExpr.WellTyped Γ tx.liftBoolTypes ∧
    TypedExpr.WellTyped Γ tx' ∧
    typeOf (substituteAction Γ.reqty.action p.toExpr) ∅ Γ = Except.ok (tx, c) ∧
    p'.toExpr = tx'.toExpr ∧
    tx' =
      (TypedExpr.and (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
      (TypedExpr.and (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
      (TypedExpr.and (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
        (TypedExpr.and
          tx.liftBoolTypes
          (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
          (.bool .anyBool))
      (.bool .anyBool))
      (.bool .anyBool))
      (.bool .anyBool)) ∧
    tx.liftBoolTypes.typeOf = .bool .anyBool
:= by
  simp only [
    wellTypedPolicy,
    bind, Option.bind,
  ] at hsome
  split at hsome
  contradiction
  rename_i tx hwt
  simp only [Option.some.injEq] at hsome
  simp only [←hsome]
  simp only [typecheckPolicy] at hwt
  split at hwt
  · rename_i tx' c hty
    split at hwt
    · rename_i hwt_bool
      have hwf_lift := typechecked_is_well_typed_after_lifting hty
      simp only [Except.toOption, Option.some.injEq] at hwt
      simp only [hwt] at hwf_lift hwt_bool
      have :
        tx.liftBoolTypes.typeOf = .bool .anyBool
      := by
        have := lifted_type_is_top hwt_bool
        simp only [←type_of_after_lifted_is_lifted] at this
        simp only [this]
        rfl
      -- Construct a `TypedExpr` for the condition
      -- TODO: this has likely been done somewhere else?
      generalize htx'' :
        (TypedExpr.and (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
        (TypedExpr.and (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
        (TypedExpr.and (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
          (TypedExpr.and
            tx.liftBoolTypes
            (TypedExpr.lit (Prim.bool true) (.bool .anyBool))
            (.bool .anyBool))
        (.bool .anyBool))
        (.bool .anyBool))
        (.bool .anyBool)) = tx''
      have hwf_tx'' : TypedExpr.WellTyped Γ tx'' := by
        simp only [←htx'']
        constructor
        · repeat constructor
        · constructor
          · repeat constructor
          · constructor
            · repeat constructor
            · constructor
              · exact hwf_lift
              · repeat constructor
              · exact this
              · rfl
            · rfl
            · rfl
          · rfl
          · rfl
        · rfl
        · rfl
      exists tx, tx'', c
      simp only [
        hwf_lift, hwf_tx'', hty, hwt, htx'', this,
        true_and, and_true,
      ]
      simp only [
        Policy.toExpr,
        Scope.toExpr,
        PrincipalScope.toExpr,
        ActionScope.toExpr,
        ResourceScope.toExpr,
        Conditions.toExpr,
        Condition.toExpr,
        List.foldr,
        TypedExpr.toExpr,
        ←htx'',
        type_lifting_preserves_expr tx,
      ]
    · contradiction
  · contradiction

/--
If a policy `p` is well-typed via `wellTypedPolicy`, then there
is a well-typed `TypedExpr` corresponding to `p`'s condition.
-/
theorem wellTypedPolicy_some_implies_well_typed_expr
  {Γ : TypeEnv} {p p' : Policy}
  (hsome : wellTypedPolicy p Γ = .some p') :
  ∃ tx : TypedExpr,
    TypedExpr.WellTyped Γ tx ∧
    tx.toExpr = p'.toExpr
:= by
  have ⟨tx, tx', _, _, hwt, _, h, _⟩ := wellTypedPolicy_some_implies_exists_typed_exprs hsome
  exists tx'
  simp [hwt, h]

/--
`wellTypedPolicy` preserves the result of `evaluate`.
-/
theorem wellTypedPolicy_preserves_evaluation
  {Γ : TypeEnv} {p p' : Policy} {request : Request} {entities : Entities}
  (hinst : InstanceOfWellFormedEnvironment request entities Γ)
  (hwt : wellTypedPolicy p Γ = .some p') :
  evaluate p.toExpr request entities
  = evaluate p'.toExpr request entities
:= by
  have ⟨tx, tx', _, hwt_tx_lift, hwt_tx', hty, heq_p'_tx', heq_tx', hbool⟩ := wellTypedPolicy_some_implies_exists_typed_exprs hwt
  have heq_action : Γ.reqty.action = request.action := by
    have ⟨_, ⟨_, h, _⟩, _⟩ := hinst
    simp [h]
  have :
    evaluate p.toExpr request entities
    = evaluate (substituteAction Γ.reqty.action p.toExpr) request entities
  := by
    simp only [heq_action]
    exact Eq.symm (substitute_action_preserves_evaluation _ _ _)
  rw [this]
  have heq :
    evaluate (substituteAction Γ.reqty.action p.toExpr) request entities
    = evaluate tx.toExpr request entities
  := type_of_preserves_evaluation_results (empty_capabilities_invariant _ _) hinst hty
  rw [heq]
  simp only [
    heq_p'_tx', heq_tx', TypedExpr.toExpr,
    ←type_lifting_preserves_expr tx,
  ]
  simp only [
    evaluate, Result.as,
    Coe.coe, Value.asBool,
    Bool.not_eq_eq_eq_not,
    Bool.not_true, bind_pure_comp,
    Functor.map, Except.map, Except.bind_ok,
    Bool.true_eq_false,
    ↓reduceIte,
  ]
  have ⟨_, ⟨v, heval, hwt_v⟩⟩ := type_of_is_sound (empty_capabilities_invariant _ _) hinst hty
  simp only [EvaluatesTo, heq] at heval
  rcases heval with heval | heval | heval | heval
  · simp [heval]
  · simp [heval]
  · simp [heval]
  . simp [heval]
    simp only [type_of_after_lifted_is_lifted] at hbool
    cases htx_ty : tx.typeOf with
    | bool bt =>
      simp only [htx_ty] at hwt_v
      cases hwt_v with | instance_of_bool b bt hwt_v_bool =>
      cases b <;> simp
    | _ => simp [htx_ty, CedarType.liftBoolTypes] at hbool

end Cedar.Thm
