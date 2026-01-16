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
import Cedar.Thm.Validation.WellTyped.ResidualDefinition
import Cedar.Thm.Data.List
import Cedar.Thm.Data.Map

namespace Cedar.Thm

open Cedar.Thm
open Cedar.Data
open Cedar.Spec
open Cedar.Validation
open Cedar.TPE

abbrev PEPreservesTypeOf (env : TypeEnv)
  (res : Residual)
  (req : Request)
  (preq : PartialRequest)
  (es : Entities)
  (pes : PartialEntities) : Prop :=
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  (TPE.evaluate res preq pes).typeOf = res.typeOf

private theorem partial_eval_preserves_typeof_and {env : TypeEnv} {a b : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities}
  (ih_a : PEPreservesTypeOf env a req preq es pes)
  (ih_b : PEPreservesTypeOf env b req preq es pes) :
  PEPreservesTypeOf env (Residual.and a b ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [Residual.typeOf, TPE.evaluate]
  cases h_wt with
  | and h₁ h₂ h₃ h₄ =>
    split
    all_goals
      rename Residual => x
      rename CedarType => ty
      rename_i heq
      unfold TPE.and at heq
    all_goals
      split at heq
    any_goals
      split at heq

    any_goals
      contradiction

    any_goals
      have h₅ := ih_a h_wf h_ref h₁
      rw [h₃] at h₅
      rw [heq] at h₅
      simp only [Residual.typeOf] at h₅
      exact h₅
    any_goals
      have h₅ := ih_b h_wf h_ref h₂
      rw [heq] at h₅
      rw [h₄] at h₅
      simp only [Residual.typeOf] at h₅
      exact h₅

    case h_2 =>
      injection heq with h₅ h₆
      rw [h₆]
    case h_5.isTrue =>
      injection heq with h₅ h₆
      rw [h₆]
    case h_5.isFalse =>
      injection heq with h₅ h₆ h₇
      rw [h₇]
    case h_3 =>
      injection heq with h₅
      rw [h₅]
    case h_6 =>
      injection heq with h₅ h₆ h₇
      rw [h₇]

private theorem partial_eval_preserves_typeof_or {env : TypeEnv} {a b : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities}
  (ih_a : PEPreservesTypeOf env a req preq es pes)
  (ih_b : PEPreservesTypeOf env b req preq es pes) :
  PEPreservesTypeOf env (Residual.or a b ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [Residual.typeOf, TPE.evaluate]
  cases h_wt with
  | or h₁ h₂ h₃ h₄ =>
    split
    all_goals
      rename Residual => x
      rename CedarType => ty
      rename_i heq
      unfold TPE.or at heq
    all_goals
      split at heq
    any_goals
      split at heq

    any_goals
      contradiction

    any_goals
      have h₅ := ih_a h_wf h_ref h₁
      rw [h₃] at h₅
      rw [heq] at h₅
      simp only [Residual.typeOf] at h₅
      exact h₅
    any_goals
      have h₅ := ih_b h_wf h_ref h₂
      rw [heq] at h₅
      rw [h₄] at h₅
      simp only [Residual.typeOf] at h₅
      exact h₅

    case h_1 =>
      injection heq with h₅ h₆
      rw [h₆]
    case h_5.isTrue =>
      injection heq with h₅ h₆
      rw [h₆]
    case h_5.isFalse =>
      injection heq with h₅ h₆ h₇
      rw [h₇]
    case h_3 =>
      injection heq with h₅
      rw [h₅]
    case h_6 =>
      injection heq with h₅ h₆ h₇
      rw [h₇]

private theorem partial_eval_preserves_typeof_ite {env : TypeEnv} {c t e : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities}
  (ih_t : PEPreservesTypeOf env t req preq es pes)
  (ih_e : PEPreservesTypeOf env e req preq es pes) :
  PEPreservesTypeOf env (Residual.ite c t e ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [Residual.typeOf, TPE.evaluate]
  cases h_wt with
  | ite h_c h_t h_e h_ty_c h_ty_t =>
    split
    all_goals
      rename Residual => x
      rename CedarType => result_ty
      rename_i heq
      unfold TPE.ite at heq
      split at heq
      try split at heq

    any_goals contradiction
    any_goals
      have h_t_type := ih_t h_wf h_ref h_t
      rw [heq] at h_t_type
      simp only [Residual.typeOf] at h_t_type
      exact h_t_type

    any_goals
      have h_e_type := ih_e h_wf h_ref h_e
      rw [heq] at h_e_type
      rw [h_ty_t]
      rw [← h_e_type]
      simp [Residual.typeOf]

    case h_2 =>
      injection heq with h₁
      rw [h₁]

    case h_3 =>
      have heq' := congr_arg (·.typeOf) heq
      simp only [Residual.typeOf] at heq'
      unfold Residual.typeOf
      rw [heq']

private theorem partial_eval_preserves_typeof_unaryApp {env : TypeEnv} {op : UnaryOp} {e : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEPreservesTypeOf env (Residual.unaryApp op e ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.apply₁]
  split
  . simp [Residual.typeOf]
  . rename CedarType => ty₂
    rename Residual => r
    rename_i h₁
    split
    . rename Option Value => x
      rename Value => v
      rename_i h₂
      unfold Spec.apply₁
      split
      any_goals simp only [Residual.typeOf, someOrError, Except.toOption]
      case h_2 =>
        rename Int64 => i
        cases h₃ : i.neg?

        all_goals
          simp [intOrErr]
    . simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_binaryApp {env : TypeEnv} {op : BinaryOp} {e1 e2 : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities}
  (ih_e1 : PEPreservesTypeOf env e1 req preq es pes) :
  PEPreservesTypeOf env (Residual.binaryApp op e1 e2 ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.apply₂, Option.pure_def, Option.bind_eq_bind]
  split
  case h_1 =>
    split
    any_goals simp only [Residual.typeOf, someOrError]
    case h_8 =>
      rename_i i j h₁ h₂
      cases i.add? j
      all_goals simp
    case h_9 =>
      rename_i i j h₁ h₂
      cases i.sub? j
      all_goals simp
    case h_10 =>
      rename_i i j h₁ h₂
      cases i.mul? j
      all_goals simp
    case h_14 =>
      rename_i v₁ v₂ uid₁ uid₂ h₁ h₂
      cases (TPE.inₑ uid₁ uid₂ pes)
      any_goals simp [someOrSelf, apply₂.self]
    case h_15 =>
      rename_i uid₁ uid₂ vs h₃
      cases (TPE.inₛ uid₁ uid₂ pes)
      any_goals (simp [someOrSelf, apply₂.self])
    case h_16 =>
      rename_i uid₁ tag h₃ h₄
      cases (TPE.hasTag uid₁ tag pes)
      any_goals (simp [someOrSelf, apply₂.self])
    case h_17 uid₁ tag _ _ =>
      cases h_wt with
      | binaryApp h₆ h₇ h₈ =>
      have ih := ih_e1 h_wf h_ref h₆
      unfold TPE.getTag
      cases pes.tags uid₁
      case binaryApp.none =>
        simp
      case binaryApp.some v =>
        simp only [someOrError]
        cases v.find? tag <;> simp
  case h_2 =>
    split
    all_goals simp only [Residual.typeOf]
    split
    all_goals
      rename_i h₂
      simp [apply₂.self] at h₂
    case h_7 =>
      rcases h₂ with ⟨_, ⟨_, ⟨_, h₃⟩⟩⟩
      rw [h₃]

private theorem partial_eval_preserves_typeof_call {env : TypeEnv} {xfn : ExtFun} {args : List Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEPreservesTypeOf env (Residual.call xfn args ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  unfold TPE.evaluate
  simp only [Residual.typeOf]
  split <;> rename_i h₁

  all_goals
    simp only [TPE.call, List.any_eq_true] at h₁
    split at h₁
    . simp only [someOrError] at h₁
      split at h₁
      all_goals
        have h₂ := congr_arg (·.typeOf) h₁
        simp only [Residual.typeOf] at h₂
        rw [h₂]
    . split at h₁
      all_goals
        have h₂ := congr_arg (·.typeOf) h₁
        simp only [Residual.typeOf] at h₂
        rw [h₂]

private theorem partial_eval_preserves_typeof_getAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEPreservesTypeOf env (Residual.getAttr expr attr ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.getAttr]
  split
  . simp [Residual.typeOf]
  . split
    . unfold someOrError
      split
      . simp [Residual.typeOf]
      . simp [Residual.typeOf]
    . simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_hasAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEPreservesTypeOf env (Residual.hasAttr expr attr ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.hasAttr]
  split
  . simp [Residual.typeOf]
  . split
    . cases h_wt
      . simp [Residual.typeOf]
      . simp [Residual.typeOf]
    . simp [Residual.typeOf]

private theorem partial_eval_preserves_typeof_set {env : TypeEnv} {ls : List Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEPreservesTypeOf env (Residual.set ls ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [Residual.typeOf, TPE.evaluate]
  split
  all_goals
    rename_i h₁
    unfold TPE.set at h₁
    split at h₁
    case h_2 =>
      split at h₁
      all_goals
        have h₂ := congr_arg (·.typeOf) h₁
        simp only [Residual.typeOf] at h₂
        rw [h₂]
    all_goals
      have h₂ := congr_arg (·.typeOf) h₁
      simp only [Residual.typeOf] at h₂
      rw [h₂]

private theorem partial_eval_preserves_typeof_record {env : TypeEnv} {ls : List (Attr × Residual)} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEPreservesTypeOf env (Residual.record ls ty) req preq es pes
:= by
  unfold PEPreservesTypeOf
  intros h_wf h_ref h_wt
  simp only [Residual.typeOf, TPE.evaluate]
  split
  all_goals
    rename_i h₁
    unfold record at h₁
    have h₂ := congr_arg (·.typeOf) h₁

  case h_1 =>
    split at h₁
    . simp only [Residual.val.injEq] at h₁
      rcases h₁ with ⟨_, h₂⟩
      rw [h₂]
    . split at h₁
      all_goals
        have h₃ := congr_arg (·.typeOf) h₁
        simp only [Residual.typeOf] at h₃
        rw [h₃]

  all_goals
    split at h₁
    . simp at h₁
    . split at h₁
      all_goals
        have h₃ := congr_arg (·.typeOf) h₁
        simp only [Residual.typeOf] at h₃
        rw [h₃]

/--
Theorem: TPE.evaluate preserves the typeOf property.

If a residual has a certain type, then partially evaluating it produces
a residual with the same type.
-/
theorem partial_eval_preserves_typeof
  {env : TypeEnv}
  {res : Residual}
  {req : Request}
  {preq : PartialRequest}
  {es : Entities}
  {pes : PartialEntities} :
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env res →
  (TPE.evaluate res preq pes).typeOf = res.typeOf
:= by
  intro h_wf h_ref h_wt
  have h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩
  cases h₁: res with
  | val v ty =>
    simp [TPE.evaluate, Residual.typeOf]
  | var v ty =>
    simp only [Residual.typeOf, TPE.evaluate]
    unfold varₚ
    simp only [varₚ.varₒ, someOrSelf]
    cases v with
    | principal =>
      cases h: preq.principal.asEntityUID <;> simp
    | resource | action =>
      cases h: preq.resource.asEntityUID <;> simp
    | context =>
      cases h: preq.context <;> simp
  | error ty =>
    simp [TPE.evaluate, Residual.typeOf]
  | and a b ty =>
    apply partial_eval_preserves_typeof_and
    · exact fun h_wf h_ref h_wt => partial_eval_preserves_typeof h_wf h_ref h_wt
    · exact fun h_wf h_ref h_wt => partial_eval_preserves_typeof h_wf h_ref h_wt
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | or a b ty =>
    apply partial_eval_preserves_typeof_or
    · exact fun h_wf h_ref h_wt => partial_eval_preserves_typeof h_wf h_ref h_wt
    · exact fun h_wf h_ref h_wt => partial_eval_preserves_typeof h_wf h_ref h_wt
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | ite c t e ty =>
    apply partial_eval_preserves_typeof_ite
    · exact fun h_wf h_ref h_wt => partial_eval_preserves_typeof h_wf h_ref h_wt
    · exact fun h_wf h_ref h_wt => partial_eval_preserves_typeof h_wf h_ref h_wt
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | unaryApp op e ty =>
    apply partial_eval_preserves_typeof_unaryApp
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | binaryApp op e1 e2 ty =>
    apply partial_eval_preserves_typeof_binaryApp
    · exact fun h_wf h_ref h_wt => partial_eval_preserves_typeof h_wf h_ref h_wt
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | call xfn args ty =>
    apply partial_eval_preserves_typeof_call
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | getAttr expr attr ty =>
    apply partial_eval_preserves_typeof_getAttr
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | hasAttr expr attr ty =>
    apply partial_eval_preserves_typeof_hasAttr
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | set ls ty =>
    apply partial_eval_preserves_typeof_set
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
  | record ls ty =>
    apply partial_eval_preserves_typeof_record
    · exact h_wf
    · exact h_ref
    · rw [← h₁]
      exact h_wt
termination_by sizeOf res
