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

open Spec SymCC Validation Data

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
`wellTypedPolicy` preserves `Entities.ValidRefsFor`.
-/
theorem substitute_action_preserves_valid_refs
  {Γ : TypeEnv} {request : Request} {entities : Entities} {expr : Expr}
  (hinst : InstanceOfWellFormedEnvironment request entities Γ) :
  entities.ValidRefsFor expr ↔ entities.ValidRefsFor (substituteAction request.action expr)
:= by
  have ⟨hwf_Γ, _, ⟨_, hinst_sch⟩⟩ := hinst
  have ⟨_, _, ⟨act_entry, hfind_act, _⟩⟩ := hwf_Γ
  have heq_act : Γ.reqty.action = request.action := by
    have ⟨_, ⟨_, h, _⟩, _⟩ := hinst
    simp [h]
  cases expr with
  | lit p => simp only [substituteAction, mapOnVars]
  | var v =>
    simp only [substituteAction, mapOnVars]
    split
    · constructor
      · intros
        constructor
        simp only [Prim.ValidRef]
        simp only [heq_act] at hfind_act
        have ⟨_, h⟩ := hinst_sch request.action act_entry hfind_act
        simp only [Map.contains, h, Option.isSome]
      · intros
        constructor
    · simp
  | and e₁ e₂ | or e₁ e₂ | binaryApp _ e₁ e₂ =>
    simp only [substituteAction, mapOnVars]
    constructor
    · intros hrefs
      cases hrefs
      rename_i hrefs₁ hrefs₂
      constructor
      · exact (substitute_action_preserves_valid_refs hinst).mp hrefs₁
      · exact (substitute_action_preserves_valid_refs hinst).mp hrefs₂
    · intros hrefs
      cases hrefs
      rename_i hrefs₁ hrefs₂
      constructor
      · exact (substitute_action_preserves_valid_refs hinst).mpr hrefs₁
      · exact (substitute_action_preserves_valid_refs hinst).mpr hrefs₂
  | ite e₁ e₂ e₃ =>
    simp only [substituteAction, mapOnVars]
    constructor
    · intros hrefs
      cases hrefs with | ite_valid hrefs₁ hrefs₂ hrefs₃ =>
      constructor
      · exact (substitute_action_preserves_valid_refs hinst).mp hrefs₁
      · exact (substitute_action_preserves_valid_refs hinst).mp hrefs₂
      · exact (substitute_action_preserves_valid_refs hinst).mp hrefs₃
    · intros hrefs
      cases hrefs with | ite_valid hrefs₁ hrefs₂ hrefs₃ =>
      constructor
      · exact (substitute_action_preserves_valid_refs hinst).mpr hrefs₁
      · exact (substitute_action_preserves_valid_refs hinst).mpr hrefs₂
      · exact (substitute_action_preserves_valid_refs hinst).mpr hrefs₃
  | unaryApp _ e | getAttr e _ | hasAttr e _ =>
    simp only [substituteAction, mapOnVars]
    constructor
    · intros hrefs
      cases hrefs
      rename_i hrefs
      constructor
      exact (substitute_action_preserves_valid_refs hinst).mp hrefs
    · intros hrefs
      cases hrefs
      rename_i hrefs
      constructor
      exact (substitute_action_preserves_valid_refs hinst).mpr hrefs
  | set s | call _ s =>
    simp only [substituteAction, mapOnVars]
    constructor
    · intros hrefs
      cases hrefs
      rename_i hrefs
      constructor
      intros e' hmem_e'
      have ⟨e, _, he'⟩ := List.mem_map.mp hmem_e'
      have hmem_e := e.property
      specialize hrefs e.val hmem_e
      simp only [←he']
      exact (substitute_action_preserves_valid_refs hinst).mp hrefs
    · intros hrefs
      cases hrefs
      rename_i hrefs
      constructor
      intros e hmem_e
      specialize hrefs (substituteAction request.action e)
      apply (substitute_action_preserves_valid_refs hinst).mpr
      apply hrefs
      apply List.mem_map.mpr
      exists ⟨e, hmem_e⟩
      simp [substituteAction]
  | record rec =>
    simp only [substituteAction, mapOnVars]
    constructor
    · intros hrefs
      cases hrefs
      rename_i hrefs
      constructor
      intros attr_expr' hmem_attr_expr'
      simp only [List.map_attach₂_snd] at hmem_attr_expr'
      have ⟨attr_expr, hmem_attr_expr, hattr_expr⟩ := List.mem_map.mp hmem_attr_expr'
      specialize hrefs attr_expr hmem_attr_expr
      simp only [←hattr_expr]
      exact (substitute_action_preserves_valid_refs hinst).mp hrefs
    · intros hrefs
      cases hrefs
      rename_i hrefs
      constructor
      intros attr_expr hmem_attr_expr
      specialize hrefs (attr_expr.fst, (substituteAction request.action attr_expr.snd))
      apply (substitute_action_preserves_valid_refs hinst).mpr
      apply hrefs
      simp only [List.map_attach₂_snd]
      apply List.mem_map.mpr
      exists attr_expr
termination_by sizeOf expr
decreasing_by
  any_goals simp; omega
  any_goals
    simp
    have := List.sizeOf_lt_of_mem hmem_e
    omega
  any_goals
    simp
    have := List.sizeOf_lt_of_mem hmem_attr_expr
    cases attr_expr
    simp at this ⊢
    omega

set_option maxHeartbeats 1000000
/--
`typeOf` preserves `Entities.ValidRefsFor`.
The converse is not true, due to policies with
invalid UID literals, such as
```
// entity User enum ["alice"];
permit(principal, action, resource)
when { if true then User::"alice" else User::"bob" };
```
-/
theorem typeOf_preserves_valid_refs
  {Γ : TypeEnv} (entities : Entities)
  {expr : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf expr c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor expr) :
  entities.ValidRefsFor tx.toExpr
:= by
  cases expr with
  | lit p =>
    simp only [typeOf, typeOfLit] at hty
    cases p with
    | bool | int | string =>
      split at hty
      any_goals contradiction
      all_goals
        simp only [
          ok, List.empty_eq,
          Function.comp_apply,
          Except.ok.injEq,
          Prod.mk.injEq,
          List.nil_eq,
        ] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        repeat constructor
    | entityUID uid =>
      split at hty
      any_goals contradiction
      all_goals
        split at hty
        · simp only [
            ok, List.empty_eq,
            Function.comp_apply,
            Except.ok.injEq,
            Prod.mk.injEq,
            List.nil_eq,
          ] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          cases hrefs
          assumption
        · contradiction
  | var v =>
    simp only [typeOf, typeOfVar] at hty
    split at hty
    all_goals
      simp only [
        ok, List.empty_eq, Function.comp_apply,
        Except.ok.injEq, Prod.mk.injEq,
        List.nil_eq,
      ] at hty
      simp only [←hty.1, TypedExpr.toExpr]
      constructor
  | and e₁ e₂ =>
    cases hrefs with | and_valid hrefs₁ hrefs₂ =>
    simp only [typeOf, typeOfAnd] at hty
    cases hty₁ : typeOf e₁ c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
      have ⟨tx₁, c₃⟩ := r₁
      simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
      split at hty
      any_goals contradiction
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
      · cases hty₂ : typeOf e₂ (c₁ ∪ c₃) Γ with
        | error => simp [hty₂] at hty
        | ok r₂ =>
          have ⟨tx₂, c₄⟩ := r₂
          simp only [hty₂, List.empty_eq, Except.bind_ok] at hty
          split at hty
          any_goals contradiction
          all_goals
            simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
            simp only [←hty.1, TypedExpr.toExpr]
            constructor
            · exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
            · exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
  | or e₁ e₂ =>
    cases hrefs with | or_valid hrefs₁ hrefs₂ =>
    simp only [typeOf, typeOfOr] at hty
    cases hty₁ : typeOf e₁ c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
      have ⟨tx₁, c₃⟩ := r₁
      simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
      split at hty
      any_goals contradiction
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
      · cases hty₂ : typeOf e₂ c₁ Γ with
        | error => simp [hty₂] at hty
        | ok r₂ =>
          have ⟨tx₂, c₄⟩ := r₂
          simp only [hty₂, List.empty_eq, Except.bind_ok] at hty
          split at hty
          any_goals contradiction
          simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          · exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
          · exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
      · cases hty₂ : typeOf e₂ c₁ Γ with
        | error => simp [hty₂] at hty
        | ok r₂ =>
          have ⟨tx₂, c₄⟩ := r₂
          simp only [hty₂, List.empty_eq, Except.bind_ok] at hty
          split at hty
          any_goals contradiction
          all_goals
            simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
            simp only [←hty.1, TypedExpr.toExpr]
            constructor
            · exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
            · exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
  | ite e₁ e₂ e₃ =>
    cases hrefs with | ite_valid hrefs₁ hrefs₂ hrefs₃ =>
    simp only [typeOf, typeOfIf] at hty
    cases hty₁ : typeOf e₁ c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
      have ⟨tx₁, c₃⟩ := r₁
      simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
      split at hty
      any_goals contradiction
      · cases hty₂ : typeOf e₂ (c₁ ∪ c₃) Γ with
        | error => simp [hty₂] at hty
        | ok r₂ =>
          have ⟨tx₂, c₄⟩ := r₂
          simp only [hty₂, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          · exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
          · exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
          · exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
      · cases hty₃ : typeOf e₃ c₁ Γ with
        | error => simp [hty₃] at hty
        | ok r₃ =>
          have ⟨tx₃, c₄⟩ := r₃
          simp only [hty₃, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          · exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
          · exact typeOf_preserves_valid_refs entities hty₃ hrefs₃
          · exact typeOf_preserves_valid_refs entities hty₃ hrefs₃
      · cases hty₂ : typeOf e₂ (c₁ ∪ c₃) Γ with
        | error => simp [hty₂] at hty
        | ok r₂ =>
        cases hty₃ : typeOf e₃ c₁ Γ with
        | error => simp [hty₂, hty₃] at hty
        | ok r₃ =>
        have ⟨tx₂, c₄⟩ := r₂
        have ⟨tx₃, c₅⟩ := r₃
        simp only [hty₂, hty₃, ok, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hty
        split at hty
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          · exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
          · exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
          · exact typeOf_preserves_valid_refs entities hty₃ hrefs₃
        · contradiction
  | unaryApp _ e =>
    simp only [typeOf, typeOfUnaryApp] at hty
    cases hrefs with | unaryApp_valid hrefs =>
    cases hty₁ : typeOf e c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
      have ⟨tx₁, c₃⟩ := r₁
      simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
      split at hty
      any_goals contradiction
      all_goals
        simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        exact typeOf_preserves_valid_refs entities hty₁ hrefs
  | binaryApp _ e₁ e₂ =>
    simp only [typeOf, typeOfBinaryApp] at hty
    cases hrefs with | binaryApp_valid hrefs₁ hrefs₂ =>
    cases hty₁ : typeOf e₁ c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
    cases hty₂ : typeOf e₂ c₁ Γ with
    | error => simp [hty₁, hty₂] at hty
    | ok r₂ =>
      have ⟨tx₁, c₃⟩ := r₁
      have ⟨tx₂, c₄⟩ := r₂
      simp only [hty₁, hty₂, List.empty_eq, Except.bind_ok] at hty
      split at hty
      any_goals contradiction
      any_goals
        simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
        exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
      any_goals
        simp only [bind, Except.bind] at hty
        split at hty
        any_goals contradiction
        all_goals
          simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
          exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
      · simp only [typeOfEq] at hty
        split at hty
        · split at hty
          all_goals
            simp only [
              ok, List.empty_eq, Function.comp_apply,
              Except.ok.injEq, Prod.mk.injEq,
              List.nil_eq,
            ] at hty
            simp only [←hty.1, TypedExpr.toExpr]
            constructor
            exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
            exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
        · split at hty
          · simp only [
              ok, List.empty_eq, Function.comp_apply,
              Except.ok.injEq, Prod.mk.injEq,
              List.nil_eq,
            ] at hty
            simp only [←hty.1, TypedExpr.toExpr]
            constructor
            exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
            exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
          · split at hty
            · simp only [
                ok, List.empty_eq, Function.comp_apply,
                Except.ok.injEq, Prod.mk.injEq,
                List.nil_eq,
              ] at hty
              simp only [←hty.1, TypedExpr.toExpr]
              constructor
              exact typeOf_preserves_valid_refs entities hty₁ hrefs₁
              exact typeOf_preserves_valid_refs entities hty₂ hrefs₂
            · contradiction
  | getAttr e _ =>
    simp only [typeOf, typeOfGetAttr] at hty
    cases hrefs with | getAttr_valid hrefs =>
    cases hty₁ : typeOf e c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
      have ⟨tx₁, c₃⟩ := r₁
      simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
      split at hty
      any_goals contradiction
      · simp only [bind, Except.bind] at hty
        split at hty
        contradiction
        simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        exact typeOf_preserves_valid_refs entities hty₁ hrefs
      · simp only [bind, Except.bind] at hty
        split at hty
        · split at hty
          contradiction
          simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          exact typeOf_preserves_valid_refs entities hty₁ hrefs
        · contradiction
  | hasAttr e _ =>
    simp only [typeOf, typeOfHasAttr] at hty
    cases hrefs with | hasAttr_valid hrefs =>
    cases hty₁ : typeOf e c₁ Γ with
    | error => simp [hty₁] at hty
    | ok r₁ =>
      have ⟨tx₁, c₃⟩ := r₁
      simp only [hty₁, List.empty_eq, Except.bind_ok] at hty
      split at hty
      any_goals contradiction
      · simp only [bind, Except.bind] at hty
        split at hty
        contradiction
        simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
        simp only [←hty.1, TypedExpr.toExpr]
        constructor
        exact typeOf_preserves_valid_refs entities hty₁ hrefs
      · simp only [bind, Except.bind] at hty
        split at hty
        · split at hty
          contradiction
          simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
          simp only [←hty.1, TypedExpr.toExpr]
          constructor
          exact typeOf_preserves_valid_refs entities hty₁ hrefs
        · split at hty
          · simp only [ok, Function.comp_apply, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
            simp only [←hty.1, TypedExpr.toExpr]
            constructor
            exact typeOf_preserves_valid_refs entities hty₁ hrefs
          · contradiction
  | _ => sorry

/--
`wellTypedPolicy` preserves `Entities.ValidRefsFor`.
-/
theorem wellTypedPolicy_preserves_valid_refs
  {Γ : TypeEnv} {request : Request} {entities : Entities} {p p' : Policy}
  (hinst : InstanceOfWellFormedEnvironment request entities Γ)
  (hwt : wellTypedPolicy p Γ = .some p')
  (hswf : entities.ValidRefsFor p.toExpr) :
  entities.ValidRefsFor p'.toExpr
:= by
  have ⟨tx, tx', _, _, _, hty, heq_p', heq_tx'⟩ := wellTypedPolicy_some_implies_exists_typed_exprs hwt
  simp only [
    heq_tx', TypedExpr.toExpr,
    ←type_lifting_preserves_expr tx,
  ] at heq_p'
  simp only [heq_p']
  repeat
    constructor
    repeat constructor
  rotate_left
  repeat constructor
  apply typeOf_preserves_valid_refs entities hty
  have : Γ.reqty.action = request.action := by
    have ⟨_, ⟨_, h, _⟩, _⟩ := hinst
    simp [h]
  simp only [this]
  apply (substitute_action_preserves_valid_refs hinst).mp
  exact hswf

theorem wellTypedPolicy_preserves_StronglyWellFormedForPolicy
  {Γ : TypeEnv} {env : Env} {p p' : Policy}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hwt : wellTypedPolicy p Γ = .some p')
  (hswf : env.StronglyWellFormedForPolicy p) :
  env.StronglyWellFormedForPolicy p'
:= by
  constructor
  · exact hswf.1
  · exact wellTypedPolicy_preserves_valid_refs hinst hwt hswf.2

theorem wellTypedPolicies_preserves_StronglyWellFormedForPolicies
  {Γ : TypeEnv} {env : Env} {ps ps' : Policies}
  (hinst : InstanceOfWellFormedEnvironment env.request env.entities Γ)
  (hwt : wellTypedPolicies ps Γ = .some ps')
  (hswf : env.StronglyWellFormedForPolicies ps) :
  env.StronglyWellFormedForPolicies ps'
:= by
  constructor
  · exact hswf.1
  · intros expr hmem_expr
    have ⟨p', hmem_p', hp'⟩ := List.mem_map.mp hmem_expr
    simp only [←hp']
    have ⟨p, hmem_p, hwt_p⟩ := List.mapM_some_implies_all_from_some hwt p' hmem_p'
    have hmem_p_expr : p.toExpr ∈ ps.map Policy.toExpr := by
      apply List.mem_map.mpr
      exists p
    have := hswf.2 p.toExpr hmem_p_expr
    exact wellTypedPolicy_preserves_valid_refs hinst hwt_p this

/--
`wellTypedPolicy` preserves the result of `evaluate`.
-/
theorem wellTypedPolicy_preserves_evaluation
  {Γ : TypeEnv} {request : Request} {entities : Entities}
  {p p' : Policy}
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

theorem wellTypedPolicies_preserves_policy_id_and_effect
  {Γ : TypeEnv} {p p' : Policy}
  (hwt : wellTypedPolicy p Γ = .some p') :
  p.id = p'.id ∧ p.effect = p'.effect
:= by
  simp only [wellTypedPolicy, bind, Option.bind] at hwt
  split at hwt
  contradiction
  simp only [Option.some.injEq] at hwt
  simp [←hwt]

theorem wellTypedPolicies_preserves_satisfiedWithEffect
  {Γ : TypeEnv} {entities : Entities} {request : Request}
  {p p' : Policy}
  (effect : Effect)
  (hinst : InstanceOfWellFormedEnvironment request entities Γ)
  (hwt : wellTypedPolicy p Γ = .some p') :
  satisfiedWithEffect effect p request entities
  = satisfiedWithEffect effect p' request entities
:= by
  have h := wellTypedPolicy_preserves_evaluation hinst hwt
  simp only [
    satisfiedWithEffect, satisfied,
    h, wellTypedPolicies_preserves_policy_id_and_effect hwt
  ]

theorem wellTypedPolicies_preserves_satisfiedPolicies
  {Γ : TypeEnv} {entities : Entities} {request : Request}
  {ps ps' : Policies}
  (effect : Effect)
  (hinst : InstanceOfWellFormedEnvironment request entities Γ)
  (hwt : wellTypedPolicies ps Γ = .some ps') :
  satisfiedPolicies effect ps request entities
  = satisfiedPolicies effect ps' request entities
:= by
  simp only [Spec.satisfiedPolicies]
  have :
    List.filterMap (λ x => satisfiedWithEffect effect x request entities) ps
    = List.filterMap (λ x => satisfiedWithEffect effect x request entities) ps'
  := by
    apply List.filterMap_eq_filterMap
      (p := λ x y =>
        satisfiedWithEffect effect x request entities
        = satisfiedWithEffect effect y request entities)
    · apply List.mapM_implies_forall₂_option _ hwt
      intros p p' hmem_p hwt_p
      exact wellTypedPolicies_preserves_satisfiedWithEffect effect hinst hwt_p
    · simp
  rw [this]

theorem wellTypedPolicies_preserves_errored
  {Γ : TypeEnv} {entities : Entities} {request : Request}
  {p p' : Policy}
  (hinst : InstanceOfWellFormedEnvironment request entities Γ)
  (hwt : wellTypedPolicy p Γ = .some p') :
  errored p request entities
  = errored p' request entities
:= by
  have h := wellTypedPolicy_preserves_evaluation hinst hwt
  simp only [
    errored, hasError,
    h, wellTypedPolicies_preserves_policy_id_and_effect hwt
  ]

theorem wellTypedPolicies_preserves_errorPolicies
  {Γ : TypeEnv} {entities : Entities} {request : Request}
  {ps ps' : Policies}
  (hinst : InstanceOfWellFormedEnvironment request entities Γ)
  (hwt : wellTypedPolicies ps Γ = .some ps') :
  errorPolicies ps request entities
  = errorPolicies ps' request entities
:= by
  simp only [errorPolicies]
  have :
    List.filterMap (fun x => errored x request entities) ps
    = List.filterMap (fun x => errored x request entities) ps'
  := by
    apply List.filterMap_eq_filterMap
      (p := λ x y => errored x request entities = errored y request entities)
    · apply List.mapM_implies_forall₂_option _ hwt
      intros p p' hmem_p hwt_p
      exact wellTypedPolicies_preserves_errored hinst hwt_p
    · simp
  rw [this]

/-- `wellTypedPolicies` preserves the result of `isAuthorized`. -/
theorem wellTypedPolicies_preserves_isAuthorized
  {Γ : TypeEnv} {entities : Entities} {request : Request}
  {ps ps' : Policies}
  (hinst : InstanceOfWellFormedEnvironment request entities Γ)
  (hwt : wellTypedPolicies ps Γ = .some ps') :
  isAuthorized request entities ps
  = isAuthorized request entities ps'
:= by
  have hpermit := wellTypedPolicies_preserves_satisfiedPolicies .permit hinst hwt
  have hforbid := wellTypedPolicies_preserves_satisfiedPolicies .forbid hinst hwt
  have herror := wellTypedPolicies_preserves_errorPolicies hinst hwt
  simp only [Spec.isAuthorized, hpermit, hforbid, herror]

end Cedar.Thm
