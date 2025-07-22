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

/-! Facts about `Entities.ValidRefsFor`. -/

namespace Cedar.Thm

open Spec SymCC Validation Data

mutual

theorem typeOf_preserves_valid_refs_and
  {Γ : TypeEnv} (entities : Entities)
  {e₁ e₂ : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.and e₁ e₂) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.and e₁ e₂)) :
  entities.ValidRefsFor tx.toExpr
:= by
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
termination_by 1 + sizeOf e₁ + sizeOf e₂
decreasing_by all_goals sorry

theorem typeOf_preserves_valid_refs_or
  {Γ : TypeEnv} (entities : Entities)
  {e₁ e₂ : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.or e₁ e₂) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.or e₁ e₂)) :
  entities.ValidRefsFor tx.toExpr
:= by
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
termination_by sizeOf e₁ + sizeOf e₂
decreasing_by all_goals sorry

theorem typeOf_preserves_valid_refs_binaryApp
  {Γ : TypeEnv} (entities : Entities)
  {op : BinaryOp} {e₁ e₂ : Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.binaryApp op e₁ e₂) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.binaryApp op e₁ e₂)) :
  entities.ValidRefsFor tx.toExpr
:= by
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
termination_by sizeOf e₁ + sizeOf e₂
decreasing_by all_goals sorry

theorem typeOf_preserves_valid_refs_call
  {Γ : TypeEnv} (entities : Entities)
  {xfn : ExtFun} {args : List Expr} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.call xfn args) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.call xfn args)) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, typeOfCall, bind, Except.bind] at hty
  cases hrefs with | call_valid hrefs =>
  split at hty
  contradiction
  rename_i txs htxs
  split at hty
  any_goals contradiction
  any_goals
    try split at hty
    try contradiction
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
    simp only [←hty.1, TypedExpr.toExpr]
    constructor
    intros x' hmem_x'
    simp only [List.map₁_eq_map] at hmem_x'
    have ⟨tx', hmem_tx', htx'⟩ := List.mem_map.mp hmem_x'
    simp only [List.mapM₁_eq_mapM (λ x => justType (typeOf x c₁ Γ)) _] at htxs
    have ⟨x, hmem_x, hx⟩ := List.mapM_ok_implies_all_from_ok htxs tx' hmem_tx'
    simp only [justType] at hx
    cases htyₓ : typeOf x c₁ Γ with
    | error => simp [htyₓ, Except.map] at hx
    | ok r =>
      have ⟨tx, c₄⟩ := r
      simp only [htyₓ, Except.map, Except.ok.injEq] at hx
      simp only [←htx', ←hx]
      specialize hrefs x hmem_x
      exact typeOf_preserves_valid_refs entities htyₓ hrefs
termination_by sizeOf args
decreasing_by all_goals sorry

theorem typeOf_preserves_valid_refs_record
  {Γ : TypeEnv} (entities : Entities)
  {rec : List (Attr × Expr)} {tx : TypedExpr} {c₁ c₂ : Capabilities}
  (hty : typeOf (Expr.record rec) c₁ Γ = Except.ok (tx, c₂))
  (hrefs : entities.ValidRefsFor (Expr.record rec)) :
  entities.ValidRefsFor tx.toExpr
:= by
  simp only [typeOf, bind, Except.bind] at hty
  cases hrefs with | record_valid hrefs =>
  split at hty
  contradiction
  rename_i txs htxs
  simp only [ok, Except.ok.injEq, Prod.mk.injEq] at hty
  simp only [←hty.1, TypedExpr.toExpr]
  constructor
  intros attr_expr' hmem_attr_expr'
  simp only [List.map_attach₂_snd] at hmem_attr_expr'
  have ⟨⟨attr, tx⟩, hmem_attr_tx, hattr_tx⟩ := List.mem_map.mp hmem_attr_expr'
  simp only at hattr_tx
  simp only [←hattr_tx]
  simp only [List.mapM₂_eq_mapM
    (λ x => Except.map (λ y => (x.fst, y.fst)) (typeOf x.snd c₁ Γ)) _] at htxs
  have ⟨⟨attr', x⟩, hmem_attr'_x, hattr'_x⟩ := List.mapM_ok_implies_all_from_ok htxs (attr, tx) hmem_attr_tx
  cases htyₓ : typeOf x c₁ Γ with
  | error => simp [htyₓ, Except.map] at hattr'_x
  | ok r =>
    have ⟨tx', c₄⟩ := r
    simp only [Except.map, htyₓ, Except.ok.injEq, Prod.mk.injEq] at hattr'_x
    simp only [←hattr'_x]
    specialize hrefs (attr', x) hmem_attr'_x
    exact typeOf_preserves_valid_refs entities htyₓ hrefs
termination_by sizeOf recs
decreasing_by all_goals sorry

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
  | and e₁ e₂ => exact typeOf_preserves_valid_refs_and entities hty hrefs
  | or e₁ e₂ => exact typeOf_preserves_valid_refs_or entities hty hrefs
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
  | binaryApp _ e₁ e₂ => exact typeOf_preserves_valid_refs_binaryApp entities hty hrefs
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
  | set s =>
    simp only [typeOf, typeOfSet] at hty
    cases hrefs with | set_valid hrefs =>
    simp only [bind, Except.bind] at hty
    split at hty
    contradiction
    rename_i s' hs'
    split at hty
    contradiction
    rename_i hd tl
    split at hty
    · rename_i ty _
      simp only [ok, List.empty_eq, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at hty
      simp only [←hty.1, TypedExpr.toExpr]
      constructor
      intros x' hmem_x'
      simp only [List.map₁_eq_map] at hmem_x'
      have ⟨tx', hmem_tx', htx'⟩ := List.mem_map.mp hmem_x'
      simp only [List.mapM₁_eq_mapM (λ x => justType (typeOf x c₁ Γ)) _] at hs'
      have ⟨x, hmem_x, hx⟩ := List.mapM_ok_implies_all_from_ok hs' tx' hmem_tx'
      simp only [justType] at hx
      cases htyₓ : typeOf x c₁ Γ with
      | error => simp [htyₓ, Except.map] at hx
      | ok r =>
        have ⟨tx, c₄⟩ := r
        simp only [htyₓ, Except.map, Except.ok.injEq] at hx
        simp only [←htx', ←hx]
        specialize hrefs x hmem_x
        exact typeOf_preserves_valid_refs entities htyₓ hrefs
    · contradiction
  | call _ args => exact typeOf_preserves_valid_refs_call entities hty hrefs
  | record rec => exact typeOf_preserves_valid_refs_record entities hty hrefs
termination_by sizeOf expr
decreasing_by all_goals sorry

end

end Cedar.Thm
