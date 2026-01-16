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
import Cedar.Thm.WellTyped
import Cedar.Thm.TPE.Input

namespace Cedar.Spec

inductive BinaryOp.CanOverflow : BinaryOp → Prop where
  | add : BinaryOp.CanOverflow .add
  | sub : BinaryOp.CanOverflow .sub
  | mul : BinaryOp.CanOverflow .mul
  | getTag : BinaryOp.CanOverflow .getTag

inductive UnaryOp.CanOverflow : UnaryOp → Prop where
  | neg : UnaryOp.CanOverflow .neg

inductive Residual.ErrorFree : Residual → Prop where
  | val : Residual.ErrorFree (.val v ty)
  | var : Residual.ErrorFree (.var v ty)
  | unary : ¬ op.CanOverflow → Residual.ErrorFree x₁ → Residual.ErrorFree (.unaryApp op x₁ ty)
  | binary : ¬ op.CanOverflow → Residual.ErrorFree x₁ → Residual.ErrorFree x₂ → Residual.ErrorFree (.binaryApp op x₁ x₂ ty)
  | and : Residual.ErrorFree x₁ → Residual.ErrorFree x₂ → Residual.ErrorFree (.and x₁ x₂ ty)
  | or : Residual.ErrorFree x₁ → Residual.ErrorFree x₂ → Residual.ErrorFree (.or x₁ x₂ ty)
  | ite : Residual.ErrorFree x₁ → Residual.ErrorFree x₂ → Residual.ErrorFree x₃ → Residual.ErrorFree (.ite x₁ x₂ x₃ ty)
  | hasAttr : Residual.ErrorFree x₁ → Residual.ErrorFree (.hasAttr x₁ attr ty)
  | set : (∀ r ∈ rs, Residual.ErrorFree r) → Residual.ErrorFree (.set rs ty)
  | record : (∀ ax ∈ axs, Residual.ErrorFree ax.snd) → Residual.ErrorFree (.record axs ty)
  -- TODO: Can extend to accept everything that doesn't do arithmetic,
  -- attribute/tag/hierarchy access, or an extension call.

end Cedar.Spec

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation

theorem BinaryOp.can_overflow_spec (op : BinaryOp) : op.canOverflow = true ↔ op.CanOverflow := by
  unfold BinaryOp.canOverflow
  split
  case h_1 | h_2 | h_3 | h_4 =>
    simp only [true_iff]
    constructor
  case h_5 =>
    simp only [Bool.false_eq_true, false_iff]
    intro h
    cases h <;> simp at *

theorem UnaryOp.can_overflow_spec (op : UnaryOp) : op.canOverflow = true ↔ op.CanOverflow := by
  unfold UnaryOp.canOverflow
  split
  case h_1 =>
    simp only [true_iff]
    constructor
  case h_2 =>
    simp only [Bool.false_eq_true, false_iff]
    intro h
    cases h
    simp at *

theorem error_free_spec (r : Residual) : r.errorFree = true ↔ r.ErrorFree := by
  cases r
  any_goals
    simp only [Residual.errorFree, Bool.false_eq_true, false_iff]
    intro hc
    cases hc
  case val =>
    simp only [Residual.errorFree, true_iff]
    constructor
  case var =>
    simp only [Residual.errorFree, true_iff]
    constructor
  case binaryApp op x₁ x₂ _ =>
    simp only [Residual.errorFree, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    have hop : op.canOverflow = false ↔ ¬ op.CanOverflow := by
      grind [BinaryOp.can_overflow_spec]
    rw [hop, error_free_spec x₁, error_free_spec x₂]
    constructor
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      constructor <;> assumption
    · intro h
      cases h
      and_intros <;> assumption
  case unaryApp op x₁ _ =>
    simp only [Residual.errorFree, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
    have hop : op.canOverflow = false ↔ ¬ op.CanOverflow := by
      grind [UnaryOp.can_overflow_spec]
    rw [hop, error_free_spec x₁]
    constructor
    · intro ⟨h₁, h₂⟩
      constructor <;> assumption
    · intro h
      cases h
      and_intros <;> assumption
  case and x₁ x₂ _ =>
    simp only [Residual.errorFree, Bool.and_eq_true]
    rw [error_free_spec x₁, error_free_spec x₂]
    constructor
    · intro ⟨h₁, h₂⟩
      exact .and h₁ h₂
    · intro h
      cases h
      rename_i h₁ h₂
      exact .intro h₁ h₂
  case or x₁ x₂ _ =>
    simp only [Residual.errorFree, Bool.and_eq_true]
    rw [error_free_spec x₁, error_free_spec x₂]
    constructor
    · intro ⟨h₁, h₂⟩
      exact .or h₁ h₂
    · intro h
      cases h
      rename_i h₁ h₂
      exact .intro h₁ h₂
  case ite x₁ x₂ x₃ _ =>
    simp only [Residual.errorFree, Bool.and_eq_true]
    rw [error_free_spec x₁, error_free_spec x₂, error_free_spec x₃]
    constructor
    · intro ⟨⟨h₁, h₂⟩, h₃⟩
      exact .ite h₁ h₂ h₃
    · intro h
      cases h
      rename_i h₁ h₂ h₃
      exact ⟨⟨h₁, h₂⟩, h₃⟩
  case hasAttr x₁ _ _ =>
    simp only [Residual.errorFree]
    rw [error_free_spec x₁]
    constructor
    · intro h₁
      exact .hasAttr h₁
    · intro h
      cases h
      assumption
  case set rs ty =>
    simp [Residual.errorFree]
    have ih : ∀ r ∈ rs, r.errorFree = true ↔ r.ErrorFree := by
      intro r hr
      have : sizeOf r  < sizeOf (Residual.set rs ty) :=  by
        have := List.sizeOf_lt_of_mem hr
        simp only [Residual.set.sizeOf_spec, gt_iff_lt]
        omega
      exact error_free_spec r
    constructor
    · intro h
      exact .set λ r hr => (ih r hr).mp (h r hr)
    · intro h r hr
      rw [ih r hr]
      cases h
      rename_i h
      exact h r hr
  case record axs ty =>
    simp [Residual.errorFree]
    have ih : ∀ ax ∈ axs, ax.snd.errorFree = true ↔ ax.snd.ErrorFree := by
      intro ax hax
      have : sizeOf ax.snd  < sizeOf (Residual.record axs ty) :=  by
        have := List.sizeOf_snd_lt_sizeOf_list hax
        simp only [Residual.record.sizeOf_spec, gt_iff_lt]
        omega
      exact error_free_spec ax.snd
    constructor
    · intro h
      constructor
      intro ax hax
      specialize ih ax hax
      rw [←ih]
      exact h ax.fst ax.snd (by simp [List.sizeOf_snd_lt_sizeOf_list hax]) (by grind [List.attach₂])
    · intro h₁ a x hax h₂
      specialize ih (a, x) (by grind [List.attach₂])
      rw [ih]
      cases h₁
      rename_i h₁
      exact h₁ (a, x) (by grind [List.attach₂])
termination_by r
decreasing_by
  all_goals
    simp [*] at *
    try omega

theorem error_free_evaluate_ok {r : Residual} :
  InstanceOfWellFormedEnvironment req es env →
  Residual.WellTyped env r →
  r.ErrorFree →
  (r.evaluate req es).isOk
:= by
  intro hwf hwt h₂
  cases h₂
  case val => simp [Residual.evaluate, Except.isOk_iff_exists]
  case var =>
    rename_i v _
    cases v <;>
    simp [Residual.evaluate, Except.isOk_iff_exists]
  case unary =>
    rename_i op _ _ _
    simp only [Residual.evaluate]
    rename_i x₁ _ he₁
    cases hwt
    rename_i hwt₁ hwt
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    rw [Except.isOk_iff_exists] at ih₁
    rw [ih₁.choose_spec]
    simp only [apply₁, Except.bind_ok]
    cases op
    case neg =>
      rename_i hop
      exact False.elim (hop (by constructor))
    case not | isEmpty | like pattern | is ty =>
      split <;> try trivial
      rename_i h_not_bool h_not_int h_not_set h_not_string h_not_entity
      cases hwt
      rename_i hty₁
      have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁.choose_spec
      rw [hty₁] at hty₁'
      first
        | have ⟨_, h_val⟩ := instance_of_anyBool_is_bool hty₁'
          simp [h_val] at h_not_bool
        | have ⟨_, h_val⟩ := instance_of_set_type_is_set hty₁'
          simp [h_val] at h_not_set
        | have ⟨_, h_val⟩ := instance_of_string_is_string hty₁'
          simp [h_val] at h_not_string
        | have ⟨_, h_val⟩ := instance_of_entity_type_is_entity hty₁'
          simp [h_val] at h_not_entity
  case binary =>
    rename_i op _ _ _ _
    simp only [Residual.evaluate]
    rw [Except.isOk_iff_exists]
    rename_i he₁ he₂
    cases hwt
    rename_i hwt₁ hwt₂ hwt
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
    rw [Except.isOk_iff_exists] at ih₁ ih₂
    rw [ih₁.choose_spec, ih₂.choose_spec]
    simp only [Except.bind_ok]
    cases hwt
    case mul | add | sub | getTag =>
      rename_i hop _ _
      exact False.elim (hop (by constructor))
    case memₛ hety₁ hety₂ =>
      have hty₁ := residual_well_typed_is_sound hwf hwt₁ ih₁.choose_spec
      have hty₂ := residual_well_typed_is_sound hwf hwt₂ ih₂.choose_spec
      rw [hety₁] at hty₁
      replace ⟨_, hty₁⟩ := instance_of_entity_type_is_entity hty₁
      rw [hety₂] at hty₂
      replace ⟨_, hty₂, htys⟩ := instance_of_set_type_is_set hty₂
      rw [hty₂]
      replace ⟨hty₁, hty₁'⟩ := hty₁
      rw [ hty₁']
      simp only [apply₂, inₛ]
      rename_i vs
      cases h_euids : Data.Set.mapOrErr Value.asEntityUID vs Error.typeError
      · have h_elem_euid : ∀ v ∈ vs, ∃ v', v.asEntityUID = .ok v' := by
          intro v hv
          replace ⟨_, h_ety⟩ := instance_of_entity_type_is_entity $ htys v hv
          simp [h_ety, Value.asEntityUID]
        unfold Data.Set.mapOrErr at h_euids
        split at h_euids <;> try contradiction
        rename_i h_err
        replace ⟨x, h_err⟩ := List.mapM_error_implies_exists_error h_err
        specialize h_elem_euid x h_err.left
        simp [h_err.right] at h_elem_euid
      · simp
    case eq | eq_val | eq_entity =>
      simp [apply₂]
    case contains hty₁ =>
      have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁.choose_spec
      rw [hty₁] at hty₁'
      have ⟨_, h_val₁⟩ := instance_of_set_type_is_set hty₁'
      simp [apply₂, h_val₁]
    all_goals
      rename_i hty₁ hty₂
      have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁.choose_spec
      rw [hty₁] at hty₁'
      first
        | have ⟨_, h_val₁⟩ := instance_of_set_type_is_set hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_string_is_string hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_entity_type_is_entity hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_decimal_type_is_decimal hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_datetime_type_is_datetime hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_duration_type_is_duration hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_int_is_int hty₁'
      have hty₂' := residual_well_typed_is_sound hwf hwt₂ ih₂.choose_spec
      rw [hty₂] at hty₂'
      first
        | have ⟨_, h_val₂⟩ := instance_of_set_type_is_set hty₂'
        | have ⟨_, h_val₂⟩ := instance_of_string_is_string hty₂'
        | have ⟨_, h_val₂⟩ := instance_of_entity_type_is_entity hty₂'
        | have ⟨_, h_val₂⟩ := instance_of_decimal_type_is_decimal hty₂'
        | have ⟨_, h_val₂⟩ := instance_of_datetime_type_is_datetime hty₂'
        | have ⟨_, h_val₂⟩ := instance_of_duration_type_is_duration hty₂'
        | have ⟨_, h_val₂⟩ := instance_of_int_is_int hty₂'
      simp [apply₂, hasTag, h_val₁, h_val₂]
  case and | or =>
    simp [Residual.evaluate]
    rw [Except.isOk_iff_exists]
    rename_i x₁ x₂ _ he₁ he₂
    cases hwt
    rename_i hwt₁ hty₁ hwt₂ hty₂
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
    rw [Except.isOk_iff_exists] at ih₁ ih₂
    rw [ih₁.choose_spec, ih₂.choose_spec]
    have hwts₁ := residual_well_typed_is_sound hwf hwt₁ ih₁.choose_spec
    rw [hty₁] at hwts₁
    have ⟨_, hb₁⟩ := instance_of_anyBool_is_bool hwts₁
    have hwts₂ := residual_well_typed_is_sound hwf hwt₂ ih₂.choose_spec
    rw [hty₂] at hwts₂
    have ⟨_, hb₂⟩ := instance_of_anyBool_is_bool hwts₂
    simp only [hb₁, hb₂, Result.as, Coe.coe, Value.asBool, Except.bind_ok]
    split <;> simp
  case ite =>
    unfold Residual.evaluate
    rw [Except.isOk_iff_exists]
    rename_i x₁ x₂ x₃ _ he₁ he₂ he₃
    cases hwt
    rename_i hwt₁ hty₁ hwt₂ hwt₃ hty₂₃
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
    have ih₃ := error_free_evaluate_ok hwf hwt₃ he₃
    rw [Except.isOk_iff_exists] at ih₁ ih₂ ih₃
    have hwts₁ := residual_well_typed_is_sound hwf hwt₁ ih₁.choose_spec
    rw [hty₁] at hwts₁
    replace hty₁ := instance_of_anyBool_is_bool hwts₁
    rw [ih₁.choose_spec, hty₁.choose_spec, ih₂.choose_spec, ih₃.choose_spec]
    cases hty₁.choose <;> simp [Value.asBool]
  case set =>
    simp only [Residual.evaluate]
    rw [Except.isOk_iff_exists]
    rename_i rs ty hrs₁
    cases hwt
    rename_i ty hwt _ _
    cases hrs₂ : rs.mapM₁ fun x => x.val.evaluate req es <;>
      simp [Except.bind_err, Except.bind_ok, reduceCtorEq, exists_const, Except.ok.injEq, exists_eq']
    replace ⟨_, ⟨_, hrs₂⟩⟩ := List.mapM_error_implies_exists_error hrs₂
    rename_i r _
    specialize hrs₁ r.val r.property
    specialize hwt r.val r.property
    have : sizeOf r.val  < sizeOf (Residual.set rs ty) :=  by
      have := List.sizeOf_lt_of_mem r.property
      simp only [Residual.set.sizeOf_spec, gt_iff_lt]
      omega
    have ih := error_free_evaluate_ok hwf hwt hrs₁
    rw [Except.isOk_iff_exists] at ih
    simp [hrs₂] at ih
  case hasAttr =>
    simp only [Residual.evaluate]
    rename_i x₁ a _ he₁
    have hwt₁ : Residual.WellTyped env x₁ := by
      cases hwt <;> assumption
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    rw [Except.isOk_iff_exists] at ih₁
    rw [ih₁.choose_spec]
    simp only [hasAttr, attrsOf, Except.bind_ok]
    have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁.choose_spec
    cases hwt
    all_goals
      rename_i hty₁
      rw [hty₁] at hty₁'
      first
        | have h_val₁ := instance_of_entity_type_is_entity hty₁'
          rw [h_val₁.choose_spec.right]
        | have h_val₁ := instance_of_record_type_is_record hty₁'
          rw [h_val₁.choose_spec]
      simp [Except.isOk, Except.toBool]
  case record =>
    rename_i axs ty haxs₁
    cases hwt
    rename_i rty hwt hrty
    rw [Except.isOk_iff_exists]
    simp only [Residual.evaluate]
    cases haxs₂ : axs.mapM₂ fun x => bindAttr x.1.fst (x.1.snd.evaluate req es) <;> simp
    replace ⟨_, ⟨_, haxs₂⟩⟩ := List.mapM_error_implies_exists_error haxs₂
    rename_i ax hax
    replace hax : ax.val ∈ axs := by grind [List.attach₂]
    specialize haxs₁ ax.val hax
    specialize hwt ax.val.fst ax.val.snd hax
    have : sizeOf ax.val.snd < sizeOf (Residual.record axs (.record rty)) := by
      have := List.sizeOf_snd_lt_sizeOf_list hax
      simp only [Residual.record.sizeOf_spec, gt_iff_lt]
      omega
    have ih := error_free_evaluate_ok hwf hwt haxs₁
    rw [Except.isOk_iff_exists] at ih
    rw [ih.choose_spec] at haxs₂
    simp [bindAttr] at haxs₂
termination_by r
decreasing_by
  all_goals
    simp [*] at *
    omega

end Cedar.Thm
