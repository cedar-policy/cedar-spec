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
import Cedar.Thm.TPE.Input
import Cedar.Thm.TPE.PreservesTypeOf
import Cedar.Thm.TPE.WellTypedCases
import Cedar.Thm.Validation.WellTyped.ResidualDefinition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

/-!
This file contains theorems about partial evaluation preserving well-typedness of residuals.
-/

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE


/--
Helper theorem: Partial evaluation preserves well-typedness for variable residuals.
-/
theorem partial_evaluation_well_typed_var {pes}      {env : TypeEnv}
  {v : Var}
  {ty : CedarType}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  :
  PEWellTyped env (Residual.var v ty) (varₚ preq v ty) req preq es pes := by
  intro h_wf h_ref h_wt
  rcases h_ref with ⟨h_rref, h_eref⟩
  unfold varₚ
  cases v with
  | principal =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    cases h : preq.principal.asEntityUID
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_pv
      apply Residual.WellTyped.val
      cases h_pv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | principal =>
            apply InstanceOfType.instance_of_entity req.principal env.reqty.principal
            rcases h_wf with ⟨_, ⟨h_principal, _, _, _⟩, _⟩
            exact h_principal
  | resource =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    cases h : preq.resource.asEntityUID
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_rv
      apply Residual.WellTyped.val
      cases h_rv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | resource =>
            apply InstanceOfType.instance_of_entity req.resource env.reqty.resource
            rcases h_wf with ⟨_, ⟨_, _, h_resource, _⟩, _⟩
            exact h_resource
  | action =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    -- Action is always concrete in partial requests
    dsimp [varₚ.varₒ, someOrSelf]
    apply Residual.WellTyped.val
    cases h_wt with
    | var h₄ =>
      cases h₄ with
      | action =>
        rw [←h_av]
        apply InstanceOfType.instance_of_entity req.action env.reqty.action.ty
        rcases h_wf with ⟨hwf, ⟨_, h_action, _, _⟩, _⟩
        rw [h_action]
        have : InstanceOfEntityType env.reqty.action env.reqty.action.ty env := by
          have ⟨_, _, _, hwf_act, _⟩ := hwf
          simp [
            InstanceOfEntityType, EntityUID.WellFormed,
            ActionSchema.contains, hwf_act,
          ]
        exact this
  | context =>
    simp
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    cases h : preq.context
    . dsimp [varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp [varₚ.varₒ, someOrSelf]
      rw [h] at h_cv
      apply Residual.WellTyped.val
      cases h_cv with
      | some _ h₃ =>
        rw [h₃]
        cases h_wt with
        | var h₄ =>
          cases h₄ with
          | context =>
            rcases h_wf with ⟨_, ⟨_, _, _, h_context⟩, _⟩
            exact type_lifting_preserves_instance_of_type h_context

theorem partial_eval_record_key_preservation_3 {ls : List (Attr × Residual)} :
  ls.find? (λ x => x.fst == k) = .some (k, v) →
  ∃ v₂,
  (List.map
    (fun x =>
      match x with
      | (a, r) => (a, Qualified.required r.typeOf))
    ls).find? (λ x => x.fst == k) = .some (k, v₂)
:= by
  intro h₁
  cases ls
  . simp at h₁
  . simp at h₁
    cases h₁
    . rename_i hd tl h₁
      rcases h₁ with ⟨h₁, h₂⟩
      exists (Qualified.required v.typeOf)
      simp
      left
      cases hd
      rename_i k₂ v₂
      simp
      simp at h₂
      rcases h₂ with ⟨h₃, h₄⟩
      rw [h₃]
      rw [h₄]
      simp
    . rename_i hd tl h₁
      rcases h₁ with ⟨h₁, h₂⟩
      let ih := partial_eval_record_key_preservation_3 h₂
      rcases ih with ⟨v₂, ih⟩
      exists v₂
      simp at ih
      simp
      right
      constructor
      . assumption
      . rcases ih with ⟨a, b, h₃, h₄, h₅⟩
        exists a
        exists b

theorem partial_eval_record_key_preservation_2 {ls : List (Attr × Residual)} :
  (List.map
    (fun x =>
      match x with
      | (a, r) => (a, Qualified.required r.typeOf))
    ls).find? (λ x => x.fst == k) = .some (k, v₃) →
  ∃ v₂,
  v₃ = Qualified.required v₂.typeOf ∧
  List.find? (fun x => decide (x.fst = k)) ls = some (k, v₂)
:= by
  intro h₁
  cases ls
  . contradiction
  case cons h tl =>
    simp at h₁
    cases h₁
    case inl h₂ =>
      simp at h₂
      rcases h₂ with ⟨h₃, h₄, h₅⟩
      exists h.snd
      simp
      left
      constructor
      . assumption
      . cases h
        simp at h₃
        rw [h₃]
    case inr h₂ =>
      rcases h₂ with ⟨h₂, a, b, h₃, h₄, h₅⟩
      exists b
      constructor
      . rw [h₅]
      . unfold List.find?
        have h₆: (decide (h.fst = k)) = false := by
          simp
          assumption
        rw [h₆]
        simp
        unfold Function.comp at h₃
        simp at h₃
        rw [h₄] at h₃
        exact h₃

theorem partial_eval_record_key_preservation_4 {xs : List (Attr × Residual)} {ys : List (Attr × Value)} :
  List.Forall₂ (fun x y => ((fun x => bindAttr x.fst x.snd.asValue) ∘ fun x => (x.fst, TPE.evaluate x.snd preq pes)) x = some y) xs
  ys →
  xs.find? (λ x => x.fst = k) = .some (k, v) →
  ∃ v₃,
  (ys.find? (λ x => x.fst = k) = .some (k, v₃))
:= by
  intro h₁
  cases h₁
  . simp
  case cons a b l₁ l₂ h₂ h₃=>
  . intro h₄
    simp at h₄
    cases h₄
    case inl h₅ =>
      rcases h₅ with ⟨h₅, h₆⟩
      simp [bindAttr] at h₂
      cases h₇: (TPE.evaluate a.snd preq pes).asValue <;> rw [h₇] at h₂
      case intro.none =>
        simp at h₂
      case intro.some v₂ =>
        simp at h₂
        exists v₂
        simp
        left
        rw [h₅] at h₂
        rw [← h₂]
        simp
    case inr h₅ =>
      rcases h₅ with ⟨h₅, h₆⟩
      have ih := partial_eval_record_key_preservation_4 h₃ h₆
      rcases ih with ⟨v₃, ih⟩
      exists v₃
      simp
      right
      simp [bindAttr] at h₂
      cases h₇: (TPE.evaluate a.snd preq pes).asValue <;> rw [h₇] at h₂
      . simp at h₂
      . simp at h₂
        rw [← h₂]
        simp
        constructor
        . assumption
        .assumption

theorem partial_eval_record_key_preservation {xs : List (Attr × Residual)} {ys : List (Attr × Value)} :
  List.Forall₂ (fun x y => ((fun x => bindAttr x.fst x.snd.asValue) ∘ fun x => (x.fst, TPE.evaluate x.snd preq pes)) x = some y) xs
  ys →
  ys.find? (λ x => x.fst = k) = .some (k, v) →
  ∃ v₂,
  (xs.find? (λ x => x.fst = k) = .some (k, v₂)) ∧
  v = (TPE.evaluate v₂ preq pes).asValue
:= by
  intro h₁ h₂
  cases h₁
  . contradiction
  case cons a₁ b₁ l₁ l₂ h₃ h₄ =>
    simp at h₂
    cases h₂
    case inl h₃ =>
      rename_i h₄
      rename_i h₅
      simp [bindAttr, Residual.asValue] at h₅
      exists a₁.2
      simp
      split at h₅
      . simp at h₅
        rcases h₃ with ⟨h₃, h₆⟩
        rename Value => v₂
        rw [h₆] at h₅
        simp at h₅
        rcases h₅ with ⟨h₅, h₇⟩
        rw [h₅]
        simp
        constructor
        . cases a₁
          rename_i a₁ a₂ h₈
          simp
          simp at h₅
          assumption
        . rename_i h₉
          rw [h₉]
          simp [Residual.asValue]
          rw [h₇]
      . simp at h₅
    case inr h₃ =>
      rcases h₃ with ⟨h₃, h₅⟩
      let ih := partial_eval_record_key_preservation h₄ h₅
      rcases ih with ⟨p₃, h₄, h₅⟩
      exists p₃
      constructor
      . simp
        right
        rw [h₄]
        simp
        cases a₁
        rename_i k₁ v₁
        cases b₁
        rename_i k₂ v₂
        simp
        simp at h₃
        simp at v₂
        rename_i k₃
        unfold bindAttr at h₃
        simp at h₃
        cases h₄ : (TPE.evaluate v₁ preq pes).asValue
        . rw [h₄] at h₃
          simp at h₃
        . rw [h₄] at h₃
          simp at h₃
          rcases h₃ with ⟨h₅, h₆⟩
          rw [h₅]
          assumption
      . exact h₅


theorem find_lifted_type {attr ty₁ ty₂} {m: RecordType} :
  Map.find? m attr = some ty₁ →
  Map.find? m.liftBoolTypes attr = some ty₂ →
  ty₂ = ty₁.liftBoolTypes
:= by
  simp [Map.find?, Map.kvs]
  intro h₁ h₂
  cases h₃: m.1
  . rw [h₃] at h₁
    simp at h₁
  . rename_i hd tl
    rw [h₃] at h₁
    unfold RecordType.liftBoolTypes at h₂
    rw [h₃] at h₂
    simp [CedarType.liftBoolTypesRecord, List.find?] at h₂
    cases h₄ : hd.fst == attr
    case cons.false =>
      rw [h₄] at h₂
      simp at h₂
      simp [List.find?] at h₁
      rw [h₄] at h₁
      simp at h₁
      exact find_lifted_type h₁ h₂
    case cons.true =>
      rw [h₄] at h₂
      simp at h₂
      rw [← h₂]
      simp [List.find?] at h₁
      rw [h₄] at h₁
      simp at h₁
      rw [h₁]
decreasing_by
  have h₅ : sizeOf m.1 < sizeOf m := by {
    simp [sizeOf]
    simp [Map._sizeOf_1]
    sorry
  }
  rename_i hd tail h₆ h₇
  have h₈: sizeOf (Map.mk tail) < sizeOf m.1 := by {
    sorry
  }
  omega


theorem ext_well_typed_after_map {xfn args ty env f} :
  ExtResidualWellTyped xfn args ty →
  (∀ arg, arg ∈ args → Residual.WellTyped env arg → Residual.WellTyped env (f arg)) →
  (∀ arg, arg ∈ args → (f arg).typeOf = arg.typeOf) →
  (∀ x, x.asValue.isSome → f x = x) →
  ExtResidualWellTyped xfn (args.map f) ty
:= by
  intro h₁ h₂ h₃ h₄
  cases h₅: h₁
  -- String-based constructors: decimal, ip, datetime, duration
  case decimal s d h₆ | ip s ip₁ h₆ | datetime s d h₆ | duration s d h₆ =>
    simp
    specialize h₄ (Residual.val (Value.prim (Prim.string s)) CedarType.string)
    simp [Residual.asValue] at h₄
    rw [h₄]
    exact h₁
  -- Binary comparison operators
  case lessThan x₁ x₂ h₆ h₇ | lessThanOrEqual x₁ x₂ h₆ h₇ | greaterThan x₁ x₂ h₆ h₇ | greaterThanOrEqual x₁ x₂ h₆ h₇ =>
    first
    | apply ExtResidualWellTyped.lessThan
    | apply ExtResidualWellTyped.lessThanOrEqual
    | apply ExtResidualWellTyped.greaterThan
    | apply ExtResidualWellTyped.greaterThanOrEqual
    . rw [h₃ x₁]
      rw [h₆]
      simp
    . rw [h₃ x₂]
      rw [h₇]
      simp
  -- Unary IP address predicates
  case isIpv4 x₁ h₆ | isIpv6 x₁ h₆ | isLoopback x₁ h₆ | isMulticast x₁ h₆ =>
    simp
    first
    | apply ExtResidualWellTyped.isIpv4
    | apply ExtResidualWellTyped.isIpv6
    | apply ExtResidualWellTyped.isLoopback
    | apply ExtResidualWellTyped.isMulticast
    rw [h₃ x₁]
    rw [h₆]
    simp
  -- Binary operations: isInRange, offset, durationSince
  case isInRange x₁ x₂ h₆ h₇ | offset x₁ x₂ h₆ h₇ | durationSince x₁ x₂ h₆ h₇ =>
    simp
    first
    | apply ExtResidualWellTyped.isInRange
    | apply ExtResidualWellTyped.offset
    | apply ExtResidualWellTyped.durationSince
    . rw [h₃ x₁]
      rw [h₆]
      simp
    . rw [h₃ x₂]
      rw [h₇]
      simp
  -- Unary datetime/duration conversions
  case toDate x₁ h₆ | toTime x₁ h₆ | toMilliseconds x₁ h₆ | toSeconds x₁ h₆ | toMinutes x₁ h₆ | toHours x₁ h₆ | toDays x₁ h₆ =>
    simp
    first
    | apply ExtResidualWellTyped.toDate
    | apply ExtResidualWellTyped.toTime
    | apply ExtResidualWellTyped.toMilliseconds
    | apply ExtResidualWellTyped.toSeconds
    | apply ExtResidualWellTyped.toMinutes
    | apply ExtResidualWellTyped.toHours
    | apply ExtResidualWellTyped.toDays
    rw [h₃ x₁]
    rw [h₆]
    simp







/--
Theorem: Partial evaluation preserves well-typedness of residuals.

If a residual is well-typed in some type environment, then partially evaluating it
with a partial request and partial entities produces another well-typed residual
in the same type environment.

This is a fundamental property ensuring that the partial evaluation process
maintains type safety throughout the computation.
-/
theorem partial_eval_preserves_well_typed
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  Residual.WellTyped env (TPE.evaluate res preq pes) := by
  intro h_wf h_ref h_wt
  unfold RequestAndEntitiesRefine at h_ref
  rcases h_ref with ⟨h_rref, h_eref⟩
  have h_ref : RequestAndEntitiesRefine req es preq pes := ⟨h_rref, h_eref⟩

  cases hᵣ : res <;> rw [hᵣ] at h_wt
  case val v ty =>
    exact partial_eval_well_typed_val h_wf h_ref h_wt
  case var v ty =>
    exact partial_eval_well_typed_var h_wf h_ref h_wt
  case and a b ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | and h_a h_b h_ty_a h_ty_b =>
      have ih_a : Residual.WellTyped env (TPE.evaluate a preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_a
      have ih_b : Residual.WellTyped env (TPE.evaluate b preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_b
      exact partial_eval_well_typed_and ih_a ih_b h_wf h_ref h_wt
  case or a b ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | or h_a h_b h_ty_a h_ty_b =>
      have ih_a : Residual.WellTyped env (TPE.evaluate a preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_a
      have ih_b : Residual.WellTyped env (TPE.evaluate b preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_b
      exact partial_eval_well_typed_or ih_a ih_b h_wf h_ref h_wt
  case ite c t e ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | ite h_c h_t h_e h_ty_c h_ty_t =>
      have ih_c : Residual.WellTyped env (TPE.evaluate c preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_c
      have ih_t : Residual.WellTyped env (TPE.evaluate t preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_t
      have ih_e : Residual.WellTyped env (TPE.evaluate e preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_e
      exact partial_eval_well_typed_ite ih_c ih_t ih_e h_wf h_ref h_wt
  case unaryApp op expr ty =>
    let h_wt₂ := h_wt
    cases h_wt₂ with
    | unaryApp h_expr h_op =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr
      exact partial_eval_well_typed_unaryApp ih_expr h_wf h_ref h_wt
  case binaryApp op expr1 expr2 ty =>
    simp [TPE.evaluate]
    have h_wt₂ := h_wt
    cases h_wt with
    | binaryApp h_expr1 h_expr2 h_op =>
      have ih1 : Residual.WellTyped env (TPE.evaluate expr1 preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr1
      have ih2 : Residual.WellTyped env (TPE.evaluate expr2 preq pes) := partial_eval_preserves_well_typed h_wf h_ref h_expr2

      apply partial_eval_well_typed_app₂ ih1 ih2 h_wf h_ref h_wt₂
  case error ty =>
    exact partial_eval_well_typed_error h_wf h_ref h_wt
  case set ls ty =>
    let h_wt₂ := h_wt
    cases h_wt₂
    rename_i ty₁ h₀ h₁ h₂
    have ih_ls : ∀ r ∈ ls, Residual.WellTyped env (TPE.evaluate r preq pes) := by
      intros r h_mem
      specialize h₀ r h_mem
      exact partial_eval_preserves_well_typed h_wf h_ref h₀
    exact partial_eval_well_typed_set ih_ls h_wf h_ref h_wt
  case record ls ty =>
    cases h_wt
    rename_i ty₁ h₀ h₁
    simp [TPE.evaluate, TPE.set]
    unfold List.map₁ List.attach List.attachWith
    rw [List.map_pmap_subtype (fun x => (x.fst, TPE.evaluate x.snd preq pes)) ls]
    simp [record]
    split
    . rename_i x xs h₃
      apply Residual.WellTyped.val
      apply InstanceOfType.instance_of_record
      . intro k h₄
        rw [Map.contains_iff_some_find?] at h₄
        rcases h₄ with ⟨v, h₄⟩

        have h₅ := Map.make_find?_implies_list_find? h₄
        rw [Map.contains_iff_some_find?]
        rw [List.mapM_some_iff_forall₂] at h₃
        have h₈ := partial_eval_record_key_preservation h₃ h₅
        rcases h₈ with ⟨v₂, h₈, h₉⟩
        have h₉ := partial_eval_record_key_preservation_3 h₈
        subst ty₁
        rcases h₉ with ⟨v₃, h₉⟩
        have h₁₀ := Map.list_find?_implies_make_find? h₉
        exists v₃
      . intro k v qty h₄ h₅
        rw [h₁] at h₅
        have h₆ := Map.make_find?_implies_list_find? h₄
        have h₇ := Map.make_find?_implies_list_find? h₅
        rw [List.mapM_some_iff_forall₂] at h₃
        have h₈ := partial_eval_record_key_preservation h₃ h₆
        rcases h₈ with ⟨v₂, h₈, h₉⟩
        have h₉ := partial_eval_record_key_preservation_2 h₇
        rcases h₉ with ⟨v₃, h₉, h₁₀⟩
        rw [h₉]
        have h₁₁ := h₀
        have h₁₂ := List.mem_of_find?_eq_some h₈
        specialize h₁₁ k v₂ h₁₂
        rw [h₁₀] at h₈
        injection h₈
        rename_i h₁₃
        simp at h₁₃
        rw [h₁₃]
        rename_i h₁₄
        simp [Residual.asValue] at h₁₄
        split at h₁₄
        case h_2 => contradiction
        rename_i v₄ ty h₁₅
        injection h₁₄
        rename_i h₁₅
        rw [h₁₅]
        simp [Qualified.getType]
        rename_i h₁₆
        have h₁₇ := partial_eval_preserves_typeof h_wf h_ref h₁₁
        rw [h₁₆] at h₁₇
        rw [←h₁₇]
        simp [Residual.typeOf]
        have termination₁ : sizeOf v₂ < sizeOf ls := by {
          have term₂ := List.sizeOf_lt_of_mem h₁₂
          simp [sizeOf, Prod._sizeOf_1] at term₂
          simp [sizeOf]
          omega
        }
        have termination₂ : sizeOf ls < sizeOf res := by {
          rw [hᵣ]
          simp [sizeOf, Residual._sizeOf_1]
          sorry -- TODO why can't we simplify further?
        }

        let ih := partial_eval_preserves_well_typed h_wf h_ref h₁₁
        rw [h₁₆] at ih
        cases ih
        assumption
      . intro k qty h₄ h₅
        subst ty₁
        have h₄ := Map.make_find?_implies_list_find? h₄
        have h₆ := partial_eval_record_key_preservation_2 h₄
        rcases h₆ with ⟨v₂, h₆, h₇⟩
        rw [List.mapM_some_iff_forall₂] at h₃
        have h₈ := partial_eval_record_key_preservation_4 h₃ h₇
        rw [Map.contains_iff_some_find?]
        rcases h₈ with ⟨v₃, h₈⟩
        exists v₃
        exact Map.list_find?_implies_make_find? h₈
    case h_2 x h₂ =>
      split
      . apply Residual.WellTyped.error
      . rename_i h₃
        apply Residual.WellTyped.record
        . intros k v h₄
          have h₅ := List.mem_of_map_implies_exists_unmapped h₄
          rcases h₅ with ⟨p, h₅, h₆⟩
          cases p ; rename_i k₂ v₂
          simp at h₆
          rcases h₆ with ⟨h₆, h₇⟩
          rw [← h₆] at h₅
          specialize h₀ k v₂ h₅
          have termination₁ : sizeOf v₂ < sizeOf res := by {
            sorry
          }
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₀
          rw [h₇]
          assumption
        . rw [h₁]
          simp
          unfold Function.comp
          simp
          congr 1
          apply List.map_func_ext
          intro x h₄
          congr 2

          cases x
          rename_i k v
          specialize h₀ k v h₄
          simp
          let h₅ := partial_eval_preserves_typeof h_wf h_ref h₀
          rw [h₅]
  case getAttr expr attr ty =>
    simp [TPE.evaluate, TPE.getAttr, TPE.attrsOf]
    split
    case h_1 =>
      apply Residual.WellTyped.error
    case h_2 r₁ h₁ =>
      split
      case h_1 x m h₂ =>
        split at h₂
        case h_1 r₂ m₂ ty₂ h₃ =>
          injection h₂; rename_i h₂
          rw [h₂] at h₃
          cases h_wt
          case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
            have ih := partial_eval_preserves_well_typed h_wf h_ref h₅
            rw [h₃] at ih
            cases ih
            rename_i h₇
            cases h₇
            rename_i rty₂ h₈ h₉ h₁₀
            cases h₁₂ : m.find? attr
            . simp [someOrError]
              apply Residual.WellTyped.error
            . rename_i v
              simp [someOrError]
              apply Residual.WellTyped.val
              have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₅
              rw [h₃] at h₁₁
              rw [h₆] at h₁₁
              simp [Residual.typeOf] at h₁₁
          case getAttr_record rty h₄ h₅ h₆ =>
            have ih := partial_eval_preserves_well_typed h_wf h_ref h₄
            rw [h₃] at ih
            cases ih
            rename_i h₇
            cases h₇
            rename_i rty₂ h₈ h₉ h₁₀
            cases h₁₂ : m.find? attr
            . simp [someOrError]
              apply Residual.WellTyped.error
            . rename_i v
              simp [someOrError]
              apply Residual.WellTyped.val
              have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₄
              rw [h₃] at h₁₁
              rw [h₅] at h₁₁
              simp [Residual.typeOf] at h₁₁
              cases h₁₃ : (Map.find? rty attr) <;> rw [h₁₃] at h₆
              . simp at h₆
              rename_i qty
              simp at h₆
              rw [h₁₁] at h₉
              specialize h₉ attr v qty h₁₂ h₁₃
              rw [h₆] at h₉
              exact h₉
        case h_2 r₂ uid ty₂ h₃ =>
          cases h_wt
          case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
            have ih := partial_eval_preserves_well_typed h_wf h_ref h₅
            rw [h₃] at ih
            cases ih
            rename_i h₇
            cases h₇
            rename_i ety₂ h₈
            cases h₁₂ : m.find? attr
            . simp [someOrError]
              apply Residual.WellTyped.error
            . rename_i v
              simp [someOrError]
              apply Residual.WellTyped.val
              have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₅
              rw [h₃] at h₁₁
              rw [h₆] at h₁₁
              simp [Residual.typeOf] at h₁₁
              unfold EntitiesRefine at h_eref
              unfold PartialEntities.attrs PartialEntities.get at h₂
              cases h₁₃ : (Map.find? pes uid) <;> rw [h₁₃] at h₂
              . simp at h₂
              . rename_i e
                specialize h_eref uid e h₁₃
                cases h_eref
                . rename_i h₁₄
                  rcases h₁₄ with ⟨h₁₅, h₁₆⟩
                  rw [h₁₅] at h₂
                  simp [PartialEntityData.attrs] at h₂
                  rw [← h₂] at h₁₂
                  simp [Map.empty, Map.find?, Map.kvs, List.find?] at h₁₂
                . rename_i h₁₄
                  rcases h₁₄ with ⟨e₂, h₁₄, h₁₅, h₁₆, h₁₇⟩
                  simp [Option.bind] at h₂
                  rw [h₂] at h₁₅
                  cases h₁₅
                  rename_i h₁₈
                  rw [h₁₈] at h₁₂
                  have h_wf2 := h_wf
                  unfold InstanceOfWellFormedEnvironment at h_wf2
                  rcases h_wf2 with ⟨h₁₉, h₂₀, h₂₁⟩
                  unfold InstanceOfSchema at h₂₁
                  rcases h₂₁ with ⟨h₂₁, h₂₂⟩
                  specialize h₂₁ uid e₂ h₁₄
                  unfold InstanceOfSchemaEntry at h₂₁
                  cases h₂₁
                  . rename_i h₂₃
                    unfold InstanceOfEntitySchemaEntry at h₂₃
                    rcases h₂₃ with ⟨e₃, h₂₃, h₂₄, h₂₅, h₂₆, h₂₇⟩
                    unfold InstanceOfEntityType at h₈
                    rcases h₈ with ⟨h₈, h₂₈⟩
                    rw [← h₈] at h₂₃
                    cases h₂₅
                    rename_i h₂₉ h₃₀ h₃₁
                    specialize h₃₀ attr v
                    simp [EntitySchema.attrs?] at h₄
                    rcases h₄ with ⟨e₄, h₃₂, h₃₃⟩
                    rw [h₁₁] at h₂₃
                    rw [h₂₃] at h₃₂
                    injection h₃₂; rename_i h₃₂
                    rw [← h₃₂] at h₃₃
                    rw [← h₃₃] at h₇
                    cases h₃₄ : (Map.find? e₃.attrs attr)
                    . specialize h₂₉ attr
                      simp [Map.contains] at h₂₉
                      rw [h₁₂] at h₂₉
                      simp at h₂₉
                      rw [h₃₄] at h₂₉
                      simp at h₂₉
                    . rename_i ty₃
                      cases h₃₅ : (Map.find? e₃.attrs.liftBoolTypes attr)
                      . rw [h₃₅] at h₇
                        simp at h₇
                      . have h₃₆ := find_lifted_type h₃₄ h₃₅
                        rename_i v₃
                        rw [h₃₅] at h₇

                        specialize h₃₀ ty₃ h₁₂ h₃₄
                        simp at h₇
                        rw [← h₇]
                        rw [h₃₆]
                        have h₃₇ := type_lifting_preserves_instance_of_type h₃₀
                        cases ty₃
                        all_goals
                          rename_i ty₃
                          simp [Qualified.getType] at h₃₇
                          simp [QualifiedType.liftBoolTypes, Qualified.getType]
                          exact h₃₇
                  . rename_i h₂₃
                    unfold InstanceOfActionSchemaEntry at h₂₃
                    rcases h₂₃ with ⟨e₃, h₂₃, h₂₄, h₂₅⟩
                    rw [e₃] at h₁₂
                    simp [Map.empty, Map.find?, Map.kvs] at h₁₂
          case getAttr_record rty h₄ h₅ h₆ =>
            have h₇ := partial_eval_preserves_typeof h_wf h_ref h₄
            rw [h₃] at h₇
            rw [h₅] at h₇
            simp [Residual.typeOf] at h₇
            have h₈ := partial_eval_preserves_well_typed h_wf h_ref h₄
            rw [h₃] at h₈
            cases h₈
            rename_i h₈
            rw [h₇] at h₈
            cases h₈ -- contradiction
        case h_3 =>
          contradiction
      case h_2 x h₂ =>
        cases h_wt
        case getAttr_entity ety rty h₅ h₆ h₇ h₈ =>
          apply Residual.WellTyped.getAttr_entity
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₆
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
            rw [h₁₀]
            rw [h₇]
          case h₃ =>
            rw [h₅]
          case h₄ =>
            exact h₈
        case getAttr_record rty h₆ h₇ h₈ =>
          apply Residual.WellTyped.getAttr_record
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₆
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
            rw [h₁₀]
            rw [h₇]
          case h₃ =>
            rw [h₈]
  case hasAttr expr attr ty =>
    simp [TPE.evaluate, TPE.hasAttr, TPE.attrsOf]
    split
    case h_1 =>
      apply Residual.WellTyped.error
    case h_2 r₁ h₁ =>
      split
      case h_1 x m h₂ =>
        apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool
        unfold InstanceOfBoolType
        simp
      case h_2 x h₂ =>
        cases h_wt
        case hasAttr_entity ety  h₅ h₆ =>
          apply Residual.WellTyped.hasAttr_entity
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₅
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₅
            rw [h₁₀]
            rw [h₆]
        case hasAttr_record rty h₆ h₇ =>
          apply Residual.WellTyped.hasAttr_record
          case h₁ =>
            exact partial_eval_preserves_well_typed h_wf h_ref h₆
          case h₂ =>
            have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
            rw [h₁₀]
            rw [h₇]
  case call xfn args ty =>
    simp [TPE.evaluate, TPE.call]
    simp [List.map₁, List.attach, List.attachWith]
    unfold Function.comp
    simp
    unfold List.unattach
    rw [List.map_pmap_subtype (fun x => x)]
    simp [List.mapM_then_map_combiner]
    rw [List.map_pmap_subtype (fun x => TPE.evaluate x preq pes)]
    split
    case h_1 x xs h₁ =>
      cases h_wt
      rename_i h₂ h₃

      unfold Spec.call
      split
      case h_1 | h_6 | h_7 | h_8 | h_9 | h_10 | h_12 | h_13 | h_16 =>
        rename ExtFun => xf
        rename List Value => vs
        try unfold Cedar.Spec.res
        first
          | unfold Ext.Decimal.decimal
          | unfold Ext.IPAddr.ip
          | unfold Ext.IPAddr.IPNet.isV4
          | unfold Ext.IPAddr.IPNet.isV6
          | unfold Ext.IPAddr.IPNet.isLoopback
          | unfold Ext.IPAddr.IPNet.isMulticast
          | skip
        split
        case h_1 x₂ v =>
          simp [someOrError, Except.toOption]
          apply Residual.WellTyped.val
          rw [List.mapM_some_iff_forall₂, List.forall₂_singleton_right_iff] at h₁
          rcases h₁ with ⟨x₃, h₁, h₅⟩
          unfold Residual.asValue at h₁
          split at h₁
          case h_2 => contradiction
          rename_i x₄ v₂ ty₂ h₆
          have h₇ : x₃ ∈ args := by {
            simp [Membership.mem]
            rw [h₅]
            apply List.Mem.head
          }
          injection h₁ ; rename_i h₁
          specialize h₂ x₃ h₇
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₂
          rw [h₆] at ih
          rw [h₁] at ih
          cases ih ; rename_i ih
          cases ih
          cases h₃
          first
          | apply InstanceOfType.instance_of_ext
            simp [InstanceOfExtType]
          | apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
        case h_2 x₂ h₄ =>
          simp [someOrError, Except.toOption]
          first
          | apply Residual.WellTyped.error
          | apply Residual.WellTyped.val
            cases h₃
            apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
      case h_2 | h_3 | h_4 | h_5 =>
        rename_i xf vs d₁ d₂
        simp [someOrError, Except.toOption]
        cases h₃
        apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
      case h_11 | h_14 | h_15 =>
        rename ExtFun => xf
        rename List Value => vs
        try unfold Cedar.Spec.res

        first
          | unfold Ext.IPAddr.IPNet.inRange
          | unfold Ext.Datetime.offset
          | skip

        split
        case h_1 x₂ v =>
          simp [someOrError, Except.toOption]
          apply Residual.WellTyped.val
          rw [List.mapM_some_iff_forall₂, List.forall₂_pair_right_iff] at h₁
          rcases h₁ with ⟨x₃, x₄, h₁, h₅, h₆⟩

          unfold Residual.asValue at h₁
          split at h₁
          case h_2 => contradiction
          rename_i x₄ v₂ ty₂ h₇
          have h₈ : x₃ ∈ args := by {
            simp [Membership.mem]
            rw [h₆]
            apply List.Mem.head
          }
          injection h₁ ; rename_i h₁
          specialize h₂ x₃ h₈
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₂
          rw [h₇] at ih
          rw [h₁] at ih
          cases ih ; rename_i ih
          cases ih
          cases h₃
          first
          | apply InstanceOfType.instance_of_ext
            simp [InstanceOfExtType]
          | apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
        case h_2 x₂ h₄ =>
          simp [someOrError, Except.toOption]
          first
          | apply Residual.WellTyped.error
          | apply Residual.WellTyped.val
            cases h₃
            apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
        try case h_3 x₂ v =>
          simp [someOrError, Except.toOption]
          cases h₃
          apply Residual.WellTyped.val
          apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
      case h_17 | h_18 | h_19 | h_20 | h_21 | h_22 =>
        simp [someOrError, Except.toOption, Ext.Datetime.toTime, Ext.Datetime.Duration.toMilliseconds]
        rw [List.mapM_some_iff_forall₂, List.forall₂_singleton_right_iff] at h₁
        rcases h₁ with ⟨x₃, h₁, h₅⟩
        unfold Residual.asValue at h₁
        split at h₁
        case h_2 => contradiction
        rename_i x₄ v₂ ty₂ h₆
        have h₇ : x₃ ∈ args := by {
          simp [Membership.mem]
          rw [h₅]
          apply List.Mem.head
        }
        injection h₁ ; rename_i h₁
        specialize h₂ x₃ h₇

        have ih := partial_eval_preserves_well_typed h_wf h_ref h₂
        rw [h₆] at ih
        rw [h₁] at ih
        cases ih ; rename_i ih
        cases ih
        cases h₃
        apply Residual.WellTyped.val
        first
        | apply InstanceOfType.instance_of_ext
          simp [InstanceOfExtType]
        | apply InstanceOfType.instance_of_int
      case h_23 =>
        simp [someOrError, Except.toOption]
        apply Residual.WellTyped.error
    case h_2 x h₂ =>
      split
      case isTrue =>
        apply Residual.WellTyped.error
      case isFalse =>
        cases h_wt
        rename_i h₁ h₂
        apply Residual.WellTyped.call
        case call.h₁ =>
          intro r h₃
          have h₄ := List.mem_of_map_implies_exists_unmapped h₃
          rcases h₄ with ⟨r₂, h₄, h₅⟩
          specialize h₁ r₂ h₄
          have ih := partial_eval_preserves_well_typed h_wf h_ref h₁
          rw [h₅]
          exact ih
        case call.h₂ =>
          apply ext_well_typed_after_map h₂
          case a =>
            intro x h₄
            apply partial_eval_preserves_well_typed h_wf h_ref
          case a =>
            intro x h₄
            specialize h₁ x h₄
            apply partial_eval_preserves_typeof h_wf h_ref h₁
          case a =>
            intro x h₄
            cases x
            . rename_i v ty
              simp [TPE.evaluate]
            all_goals {
              simp [Residual.asValue] at h₄
            }
termination_by (sizeOf res)


end Cedar.Thm
