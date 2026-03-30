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
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

import Cedar.Thm.TPE.WellTyped.Basic

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

-- Helper theorems for record key preservation and type lifting
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
  case decimal s d _ | ip s ip₁ _ | datetime s d _ | duration s d _ =>
    simp only [List.map]
    specialize h₄ (Residual.val (Value.prim (Prim.string s)) CedarType.string)
    simp only [Residual.asValue, Option.isSome_some, forall_const] at h₄
    rw [h₄]
    exact h₁
  -- Binary comparison operators
  case lessThan x₁ x₂ h₆ h₇ | lessThanOrEqual x₁ x₂ h₆ h₇ | greaterThan x₁ x₂ h₆ h₇ | greaterThanOrEqual x₁ x₂ h₆ h₇ =>
    first
    | apply ExtResidualWellTyped.lessThan
    | apply ExtResidualWellTyped.lessThanOrEqual
    | apply ExtResidualWellTyped.greaterThan
    | apply ExtResidualWellTyped.greaterThanOrEqual
    . rw [h₃ x₁ (by simp), h₆]
    . rw [h₃ x₂ (by simp), h₇]
  -- Unary IP address predicates
  case isIpv4 x₁ h₆ | isIpv6 x₁ h₆ | isLoopback x₁ h₆ | isMulticast x₁ h₆ =>
    simp only [List.map]
    first
    | apply ExtResidualWellTyped.isIpv4
    | apply ExtResidualWellTyped.isIpv6
    | apply ExtResidualWellTyped.isLoopback
    | apply ExtResidualWellTyped.isMulticast
    rw [h₃ x₁ (by simp), h₆]
  -- Binary operations: isInRange, offset, durationSince
  case isInRange x₁ x₂ h₆ h₇ | offset x₁ x₂ h₆ h₇ | durationSince x₁ x₂ h₆ h₇ =>
    simp only [List.map_cons, List.map_nil]
    first
    | apply ExtResidualWellTyped.isInRange
    | apply ExtResidualWellTyped.offset
    | apply ExtResidualWellTyped.durationSince
    . rw [h₃ x₁ (by simp), h₆]
    . rw [h₃ x₂ (by simp), h₇]
  -- Unary datetime/duration conversions
  case toDate x₁ h₆ | toTime x₁ h₆ | toMilliseconds x₁ h₆ | toSeconds x₁ h₆ | toMinutes x₁ h₆ | toHours x₁ h₆ | toDays x₁ h₆ =>
    simp only [List.map_cons, List.map_nil]
    first
    | apply ExtResidualWellTyped.toDate
    | apply ExtResidualWellTyped.toTime
    | apply ExtResidualWellTyped.toMilliseconds
    | apply ExtResidualWellTyped.toSeconds
    | apply ExtResidualWellTyped.toMinutes
    | apply ExtResidualWellTyped.toHours
    | apply ExtResidualWellTyped.toDays
    rw [h₃ x₁ (List.mem_singleton.mpr rfl), h₆]

theorem partial_eval_well_typed_call {env : TypeEnv} {xfn : ExtFun} {args : List Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  (∀ r ∈ args, Residual.WellTyped env (TPE.evaluate r preq pes)) →
  PEWellTyped env (Residual.call xfn args ty) (TPE.evaluate (Residual.call xfn args ty) preq pes) req preq es pes
:= by
  intros h_args_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.call, List.any_eq_true]
  simp only [List.map₁, List.attach, List.attachWith, List.map_subtype, List.mapM_map, List.mem_map, List.mem_unattach, List.mem_pmap, Subtype.mk.injEq, exists_prop, exists_eq_right, and_self]
  unfold Function.comp
  simp only [List.map_subtype, List.mem_map, List.mem_unattach, List.mem_pmap, Subtype.mk.injEq, exists_prop, exists_eq_right, and_self]
  unfold List.unattach
  rw [List.map_pmap_subtype (fun x => x)]
  simp only [List.map_id_fun', id_eq, List.map_subtype, List.mem_map, List.mem_unattach, List.mem_pmap, Subtype.mk.injEq, exists_prop, exists_eq_right, and_self]
  simp only [List.map_pmap_subtype (fun x => TPE.evaluate x preq pes)]
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
        simp only [someOrError, Except.toOption]
        rw [List.mapM_some_iff_forall₂, List.forall₂_singleton_right_iff] at h₁
        rcases h₁ with ⟨x₃, h₁, h₅⟩
        unfold Residual.asValue at h₁
        split at h₁
        case h_2 => contradiction
        rename_i x₄ v₂ ty₂ h₆
        have h₇ : x₃ ∈ args := by {
          simp only [Membership.mem]
          rw [h₅]
          apply List.Mem.head
        }
        injection h₁ ; rename_i h₁
        specialize h₂ x₃ h₇
        have ih := h_args_wt x₃ h₇
        rw [h₆] at ih
        rw [h₁] at ih
        cases ih ; rename_i ih
        cases ih
        cases h₃
        first
        | apply Residual.WellTyped.val
          apply InstanceOfType.instance_of_ext
          simp [InstanceOfExtType]
        | exact well_typed_bool
      case h_2 x₂ h₄ =>
        simp only [someOrError, Except.toOption]
        first
        | apply Residual.WellTyped.error
        | cases h₃
          exact well_typed_bool
    case h_2 | h_3 | h_4 | h_5 =>
      rename_i xf vs d₁ d₂
      simp only [someOrError, Except.toOption]
      cases h₃
      exact well_typed_bool
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
        simp only [someOrError, Except.toOption]
        rw [List.mapM_some_iff_forall₂, List.forall₂_pair_right_iff] at h₁
        rcases h₁ with ⟨x₃, x₄, h₁, h₅, h₆⟩

        unfold Residual.asValue at h₁
        split at h₁
        case h_2 => contradiction
        rename_i x₄ v₂ ty₂ h₇
        have h₈ : x₃ ∈ args := by {
          simp only [Membership.mem]
          rw [h₆]
          apply List.Mem.head
        }
        injection h₁ ; rename_i h₁
        specialize h₂ x₃ h₈
        have ih := h_args_wt x₃ h₈
        rw [h₇] at ih
        rw [h₁] at ih
        cases ih ; rename_i ih
        cases ih
        cases h₃
        first
        | apply Residual.WellTyped.val
          apply InstanceOfType.instance_of_ext
          simp [InstanceOfExtType]
        | exact well_typed_bool
      case h_2 x₂ h₄ =>
        simp only [someOrError, Except.toOption]
        first
        | apply Residual.WellTyped.error
        | cases h₃
          exact well_typed_bool
      try case h_3 x₂ v =>
        simp only [someOrError, Except.toOption]
        cases h₃
        exact well_typed_bool
    case h_17 | h_18 | h_19 | h_20 | h_21 | h_22 =>
      simp only [someOrError, Except.toOption, Ext.Datetime.toTime, ge_iff_le, beq_iff_eq]
      rw [List.mapM_some_iff_forall₂, List.forall₂_singleton_right_iff] at h₁
      rcases h₁ with ⟨x₃, h₁, h₅⟩
      unfold Residual.asValue at h₁
      split at h₁
      case h_2 => contradiction
      rename_i x₄ v₂ ty₂ h₆
      have h₇ : x₃ ∈ args := by {
        simp only [Membership.mem]
        rw [h₅]
        apply List.Mem.head
      }
      injection h₁ ; rename_i h₁
      specialize h₂ x₃ h₇

      have ih := h_args_wt x₃ h₇
      rw [h₆] at ih
      rw [h₁] at ih
      cases ih ; rename_i ih
      cases ih
      cases h₃
      first
      | apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_ext
        simp [InstanceOfExtType]
      | exact well_typed_int
    case h_23 =>
      simp only [someOrError, Except.toOption]
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
        have ih := h_args_wt r₂ h₄
        rw [h₅]
        exact ih
      case call.h₂ =>
        apply ext_well_typed_after_map h₂
        case a =>
          intro x h₄ h₅
          apply h_args_wt
          exact h₄
        case a =>
          intro x h₄
          specialize h₁ x h₄
          apply partial_eval_preserves_typeof _ h₁
        case a =>
          intro x h₄
          cases x
          . rename_i v ty
            simp [TPE.evaluate]
          all_goals {
            simp [Residual.asValue] at h₄
          }
