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
    let h_wt₂ := h_wt
    cases h_wt₂
    rename_i ty₁ h₀ h₁
    have ih_ls : ∀ k v, (k, v) ∈ ls → Residual.WellTyped env (TPE.evaluate v preq pes) := by
      intros k v h_mem
      specialize h₀ k v h_mem
      have termination : sizeOf v < sizeOf res := by {
        sorry
      }
      exact partial_eval_preserves_well_typed h_wf h_ref h₀
    exact partial_eval_well_typed_record ih_ls h_wf h_ref h_wt
  case getAttr expr attr ty =>
    let h_wt₂ := h_wt
    cases h_wt₂
    case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h₅
      exact partial_eval_well_typed_getAttr ih_expr h_wf h_ref h_wt
    case getAttr_record rty h₄ h₅ h₆ =>
      have ih_expr : Residual.WellTyped env (TPE.evaluate expr preq pes) := partial_eval_preserves_well_typed h_wf h_ref h₄
      exact partial_eval_well_typed_getAttr ih_expr h_wf h_ref h_wt
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
