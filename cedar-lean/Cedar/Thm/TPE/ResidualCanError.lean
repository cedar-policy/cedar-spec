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
  | set : (∀ r ∈ rs, Residual.ErrorFree r) → Residual.ErrorFree (.set rs ty)
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
  case set rs _ =>
    simp [Residual.errorFree]
    have ih : ∀ r ∈ rs, r.errorFree = true ↔ r.ErrorFree := by
      intro r hr
      exact error_free_spec r
    constructor
    · intro h
      exact .set λ r hr => (ih r hr).mp (h r hr)
    · intro h r hr
      rw [ih r hr]
      cases h
      rename_i h
      exact h r hr

-- I don't need this theorem atm. Leaving not in case I think I need it again
-- later.
--
-- NOTE: This theorem isn't quite correct. There's a bit of a hang up with
-- optional attributes and tags. The `WellTyped` property of a residual doesn't
-- have enough information to conclude that these expression never error (it
-- doesn't say anything about the capabilities tracked during typechecking).
--
-- We probably could bake capabilities into the residual but TBH that doesn't
-- sound fun. Instead I'm hoping we can ignore this case because `getTag` and
-- `.` are both possibly erroring operations regardless of capabilities due to
-- the possibility of a missing entity. I'm not sure how `hasTag` and `has` fit
-- into this. They never error under any circumstance, so I can probably ignore
-- them entirely.
-- theorem well_typed_residual_eval {r : Residual} :
--   InstanceOfWellFormedEnvironment req es env →
--   Residual.WellTyped env r →
--   (r.evaluate req es) = .error .entityDoesNotExist ∨
--   (r.evaluate req es) = .error .extensionError ∨
--   (r.evaluate req es) = .error .arithBoundsError ∨
--   ∃ v, (r.evaluate req es) = .ok v
-- := by sorry -- by typechecker soundness

theorem error_free_evaluate_ok {r : Residual} :
  InstanceOfWellFormedEnvironment req es env →
  Residual.WellTyped env r →
  r.ErrorFree →
  (r.evaluate req es).isOk
:= by
  intro hwf hwt h₂
  cases h₂
  case val => simp [Residual.evaluate, Except.isOk, Except.toBool]
  case var =>
    rename_i v _
    cases v <;>
    simp [Residual.evaluate, Except.isOk, Except.toBool]
  case unary =>
    rename_i op _ _ _
    cases op
    case neg =>
      rename_i hop
      exact False.elim (hop (by constructor))
    case not | isEmpty | like pattern | is ty =>
      simp [Residual.evaluate, Except.isOk, Except.toBool]
      rename_i x₁ _ he₁ _
      cases hwt
      rename_i hwt₁ hwt
      have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
      simp [Except.isOk, Except.toBool] at ih₁
      split at ih₁ <;> try contradiction
      clear ih₁ ; rename_i ih₁
      simp [ih₁, apply₁]
      split <;> try rfl

      rename_i heval'
      split at heval' <;> try contradiction
      rename_i h_not_bool h_not_int h_not_set h_not_string h_not_entity
      injections heval'
      subst heval'

      cases hwt
      rename_i hty₁
      have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁
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
    simp [Residual.evaluate, Except.isOk, Except.toBool]
    rename_i he₁ he₂
    cases hwt
    rename_i hwt₁ hwt₂ hwt
    have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
    have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
    simp only [Except.isOk, Except.toBool] at ih₁ ih₂
    split at ih₁ <;> try contradiction
    clear ih₁ ; rename_i ih₁
    split at ih₂ <;> try contradiction
    clear ih₂ ; rename_i ih₂
    simp [ih₁, ih₂]
    cases hwt
    case mul | add | sub | getTag =>
      rename_i hop _ _
      exact False.elim (hop (by constructor))
    case memₛ hety₁ hety₂ =>
      have hty₁ := residual_well_typed_is_sound hwf hwt₁ ih₁
      have hty₂ := residual_well_typed_is_sound hwf hwt₂ ih₂
      rw [hety₁] at hty₁
      replace ⟨_, hty₁⟩ := instance_of_entity_type_is_entity hty₁
      rw [hety₂] at hty₂
      replace ⟨_, hty₂, htys⟩ := instance_of_set_type_is_set hty₂
      subst hty₂
      replace ⟨hty₁, hty₁'⟩ := hty₁
      subst hty₁ hty₁'
      simp only [apply₂, inₛ]
      split <;> try rfl
      rename_i vs _ _ heval
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
      · simp [h_euids] at heval
    case eq | eq_val | eq_entity =>
      simp [apply₂]
    case contains hty₁ =>
      have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁
      rw [hty₁] at hty₁'
      have ⟨_, h_val₁⟩ := instance_of_set_type_is_set hty₁'
      simp [apply₂, h_val₁]
    all_goals
      rename_i hty₁ hty₂
      have hty₁' := residual_well_typed_is_sound hwf hwt₁ ih₁
      rw [hty₁] at hty₁'
      first
        | have ⟨_, h_val₁⟩ := instance_of_set_type_is_set hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_string_is_string hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_entity_type_is_entity hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_decimal_type_is_decimal hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_datetime_type_is_datetime hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_duration_type_is_duration hty₁'
        | have ⟨_, h_val₁⟩ := instance_of_int_is_int hty₁'
      have hty₂' := residual_well_typed_is_sound hwf hwt₂ ih₂
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
  case and =>
    simp [Residual.evaluate, Except.isOk, Except.toBool]
    rename_i x₁ x₂ _ he₁ he₂
    cases hwt with
    | and hwt₁ hwt₂ hty₁ hty₂ =>
      have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
      have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
      simp [Except.isOk, Except.toBool] at ih₁ ih₂
      split at ih₁ <;> try contradiction
      clear ih₁ ; rename_i ih₁
      split at ih₂ <;> try contradiction
      clear ih₂ ; rename_i ih₂
      simp [ih₁, ih₂, Result.as, Coe.coe, Value.asBool]
      split <;> try rfl
      rename_i heval'
      split at heval'
      · simp at heval'
        split at heval'
        · contradiction
        · have hwts₂ := residual_well_typed_is_sound hwf hwt₂ ih₂
          rw [hty₂] at hwts₂
          have ⟨_, hb⟩ := instance_of_anyBool_is_bool hwts₂
          subst hb
          simp at heval'
      · have hwts₁ := residual_well_typed_is_sound hwf hwt₁ ih₁
        rw [hty₁] at hwts₁
        have ⟨_, hb⟩ := instance_of_anyBool_is_bool hwts₁
        subst hb
        rename_i h_not_bool
        simp at h_not_bool
  case or =>
    simp [Residual.evaluate, Except.isOk, Except.toBool]
    rename_i x₁ x₂ _ he₁ he₂
    cases hwt with
    | or hwt₁ hwt₂ hty₁ hty₂ =>
      have ih₁ := error_free_evaluate_ok hwf hwt₁ he₁
      have ih₂ := error_free_evaluate_ok hwf hwt₂ he₂
      simp [Except.isOk, Except.toBool] at ih₁ ih₂
      split at ih₁ <;> try contradiction
      clear ih₁ ; rename_i ih₁
      split at ih₂ <;> try contradiction
      clear ih₂ ; rename_i ih₂
      simp [ih₁, ih₂, Result.as, Coe.coe, Value.asBool]
      split <;> try rfl
      rename_i heval'
      split at heval'
      · simp at heval'
        have hwts₂ := residual_well_typed_is_sound hwf hwt₂ ih₂
        rw [hty₂] at hwts₂
        have ⟨_, hb⟩ := instance_of_anyBool_is_bool hwts₂
        subst hb
        simp only [Except.map_ok] at heval'
        split at heval' <;> contradiction
      · have hwts₁ := residual_well_typed_is_sound hwf hwt₁ ih₁
        rw [hty₁] at hwts₁
        have ⟨_, hb⟩ := instance_of_anyBool_is_bool hwts₁
        subst hb
        rename_i h_not_bool
        simp at h_not_bool
  case set =>
    rename_i rs ty hrs₁
    cases hwt
    rename_i ty hwt _ _
    simp [Residual.evaluate, Except.isOk, Except.toBool]
    split <;> try rfl
    rename_i herr
    cases hrs₂ : rs.mapM₁ fun x => x.val.evaluate req es  <;> simp [hrs₂] at herr
    subst herr
    replace ⟨_, ⟨_, hrs₂⟩⟩ := List.mapM_error_implies_exists_error hrs₂
    rename_i r _
    specialize hrs₁ r.val r.property
    specialize hwt r.val r.property
    have : sizeOf r.val  < sizeOf (Residual.set rs ty) :=  by
      have := List.sizeOf_lt_of_mem r.property
      simp only [Residual.set.sizeOf_spec, gt_iff_lt]
      omega
    have ih := error_free_evaluate_ok hwf hwt hrs₁
    rw [hrs₂] at ih
    simp [Except.isOk, Except.toBool] at ih
termination_by r
decreasing_by
  all_goals
    simp [*] at *
    omega

end Cedar.Thm
