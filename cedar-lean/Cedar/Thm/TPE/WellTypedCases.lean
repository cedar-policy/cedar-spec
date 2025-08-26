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



abbrev PEWellTyped (env : TypeEnv)
  (r₁ r₂ : Residual)
  (req : Request)
  (preq : PartialRequest)
  (es : Entities)
  (pes : PartialEntities) : Prop :=
  InstanceOfWellFormedEnvironment req es env →
  RequestAndEntitiesRefine req es preq pes →
  Residual.WellTyped env r₁ →
  Residual.WellTyped env r₂

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

theorem find_lifted_type {attr ty₁ ty₂} {m: RecordType} :
  Map.find? m attr = some ty₁ →
  Map.find? m.liftBoolTypes attr = some ty₂ →
  ty₂ = ty₁.liftBoolTypes
:= by
  simp only [Map.find?, Map.kvs]
  intro h₁ h₂
  cases h₃: m.1
  case nil =>
    rw [h₃] at h₁
    simp at h₁
  case cons hd tl =>
    rw [h₃] at h₁
    unfold RecordType.liftBoolTypes at h₂
    rw [h₃] at h₂
    simp only [CedarType.liftBoolTypesRecord, List.find?] at h₂
    cases h₄ : hd.fst == attr
    case false =>
      simp only [List.find?] at h₁
      rw [h₄] at h₁ h₂
      exact find_lifted_type h₁ h₂
    case true =>
      simp only [List.find?] at h₁
      rw [h₄] at h₁ h₂
      simp only [Option.some.injEq] at h₁ h₂
      rw [← h₂, h₁]
decreasing_by
  rename_i hd tail _ _
  have h₈: sizeOf (Map.mk tail) < sizeOf m := by {
    simp only [sizeOf, Map._sizeOf_1, Nat.add_lt_add_iff_left]
    have h₉ : m.1 = hd :: tail := h₃
    rw [h₉]
    simp only [List._sizeOf_1, Nat.lt_add_left_iff_pos, gt_iff_lt]
    omega
  }
  exact h₈


/--
Helper theorem: Partial evaluation preserves well-typedness for value residuals.
-/
theorem partial_eval_well_typed_val {env : TypeEnv} {v : Value} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEWellTyped env (Residual.val v ty) (TPE.evaluate (Residual.val v ty) preq pes) req preq es pes := by
  unfold PEWellTyped
  intros h_wf h_ref h_wt
  simp only [TPE.evaluate]
  exact h_wt

/--
Helper theorem: Partial evaluation preserves well-typedness for variable residuals.
-/
theorem partial_eval_well_typed_var {env : TypeEnv} {v : Var} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEWellTyped env (Residual.var v ty) (TPE.evaluate (Residual.var v ty) preq pes) req preq es pes := by
  unfold PEWellTyped
  intro h_wf h_ref h_wt
  rcases h_ref with ⟨h_rref, h_eref⟩
  simp only [TPE.evaluate]
  unfold varₚ
  cases v
  case principal =>
    simp only [Option.pure_def, Option.bind_eq_bind]
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, _⟩
    cases h : preq.principal.asEntityUID
    case intro.none =>
      assumption
    case intro.some =>
      simp only [Option.bind_some, varₚ.varₒ, someOrSelf]
      rw [h] at h_pv
      apply Residual.WellTyped.val
      cases h_pv with | some _ h₃ =>
      cases h_wt with | var h₄ =>
      cases h₄ with | principal =>

      rw [h₃]
      apply InstanceOfType.instance_of_entity req.principal env.reqty.principal

      rcases h_wf with ⟨_, ⟨h_principal, _, _, _⟩, _⟩
      exact h_principal
  case resource =>
    simp only [Option.pure_def, Option.bind_eq_bind]
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨_, ⟨_, h_rv, _⟩⟩
    cases h : preq.resource.asEntityUID
    . dsimp only [Option.bind_none, varₚ.varₒ, someOrSelf]
      exact h_wt
    . dsimp only [Option.bind_some, varₚ.varₒ, someOrSelf]
      rw [h] at h_rv
      apply Residual.WellTyped.val
      cases h_rv with | some _ h₃ =>
      rw [h₃]
      cases h_wt with | var h₄ =>
      cases h₄ with | resource =>

      apply InstanceOfType.instance_of_entity req.resource env.reqty.resource
      rcases h_wf with ⟨_, ⟨_, _, h_resource, _⟩, _⟩
      exact h_resource
  case action =>
    simp only
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    -- Action is always concrete in partial requests
    simp only [varₚ.varₒ, someOrSelf]
    apply Residual.WellTyped.val
    cases h_wt with | var h₄ =>
    cases h₄ with | action =>

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
  case context =>
    simp only
    unfold RequestRefines at h_rref
    rcases h_rref with ⟨h_pv, h_rest⟩
    rcases h_rest with ⟨h_av, h_rv, h_cv⟩
    cases h : preq.context
    . simp only [Option.map_none, varₚ.varₒ, someOrSelf]
      exact h_wt
    . simp only [Option.map_some, varₚ.varₒ, someOrSelf]
      rw [h] at h_cv
      apply Residual.WellTyped.val
      cases h_cv with | some _ h₃ =>
      rw [h₃]
      cases h_wt with | var h₄ =>
      cases h₄ with | context =>

      rcases h_wf with ⟨_, ⟨_, _, _, h_context⟩, _⟩
      exact type_lifting_preserves_instance_of_type h_context

/--
Helper theorem: Partial evaluation preserves well-typedness for error residuals.
-/
theorem partial_eval_well_typed_error {env : TypeEnv} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  PEWellTyped env (Residual.error ty) (TPE.evaluate (Residual.error ty) preq pes) req preq es pes := by
  unfold PEWellTyped
  intros h_wf h_ref h_wt
  simp only [TPE.evaluate]
  exact h_wt

/--
Helper theorem: Partial evaluation preserves well-typedness for and residuals.
-/
theorem partial_eval_well_typed_and {env : TypeEnv} {a b : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate a preq pes) →
  Residual.WellTyped env (TPE.evaluate b preq pes) →
  PEWellTyped env (Residual.and a b ty) (TPE.evaluate (Residual.and a b ty) preq pes) req preq es pes := by
  intros h_a_wt h_b_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | and h_a h_b h_ty_a h_ty_b =>
    unfold TPE.and
    split
    . exact h_b_wt
    . apply Residual.WellTyped.val
      apply InstanceOfType.instance_of_bool false BoolType.anyBool
      simp [InstanceOfBoolType]
    . apply Residual.WellTyped.error
    . exact h_a_wt
    . apply Residual.WellTyped.and
      · exact h_a_wt
      · exact h_b_wt
      · rw [partial_eval_preserves_typeof h_wf h_ref h_a]
        exact h_ty_a
      · rw [partial_eval_preserves_typeof h_wf h_ref h_b]
        exact h_ty_b

/--
Helper theorem: Partial evaluation preserves well-typedness for or residuals.
-/
theorem partial_eval_well_typed_or {env : TypeEnv} {a b : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate a preq pes) →
  Residual.WellTyped env (TPE.evaluate b preq pes) →
  PEWellTyped env (Residual.or a b ty) (TPE.evaluate (Residual.or a b ty) preq pes) req preq es pes := by
  intros h_a_wt h_b_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | or h_a h_b h_ty_a h_ty_b =>
    unfold TPE.or
    split
    . apply Residual.WellTyped.val
      apply InstanceOfType.instance_of_bool true BoolType.anyBool
      simp [InstanceOfBoolType]
    . exact h_b_wt
    . apply Residual.WellTyped.error
    . exact h_a_wt
    . apply Residual.WellTyped.or
      · exact h_a_wt
      · exact h_b_wt
      · rw [partial_eval_preserves_typeof h_wf h_ref h_a]
        exact h_ty_a
      · rw [partial_eval_preserves_typeof h_wf h_ref h_b]
        exact h_ty_b

/--
Helper theorem: Partial evaluation preserves well-typedness for ite (if-then-else) residuals.
-/
theorem partial_eval_well_typed_ite {env : TypeEnv} {c t e : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate c preq pes) →
  Residual.WellTyped env (TPE.evaluate t preq pes) →
  Residual.WellTyped env (TPE.evaluate e preq pes) →
  PEWellTyped env (Residual.ite c t e ty) (TPE.evaluate (Residual.ite c t e ty) preq pes) req preq es pes := by
  intros h_c_wt h_t_wt h_e_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | ite h_c h_t h_e h_ty_c h_ty_t =>
    unfold TPE.ite
    split
    . split
      · exact h_t_wt
      · exact h_e_wt
    . apply Residual.WellTyped.error
    . have h_t_type_eq : t.typeOf = (TPE.evaluate t preq pes).typeOf := (partial_eval_preserves_typeof h_wf h_ref h_t).symm
      rw [h_t_type_eq]
      apply Residual.WellTyped.ite
      · exact h_c_wt
      · exact h_t_wt
      · exact h_e_wt
      · rw [partial_eval_preserves_typeof h_wf h_ref h_c]
        exact h_ty_c
      · rw [partial_eval_preserves_typeof h_wf h_ref h_t]
        rw [partial_eval_preserves_typeof h_wf h_ref h_e]
        exact h_ty_t

/--
Helper theorem: Partial evaluation preserves well-typedness for unary application residuals.
-/
theorem partial_eval_well_typed_unaryApp {env : TypeEnv} {op : UnaryOp} {expr : Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.unaryApp op expr ty) (TPE.evaluate (Residual.unaryApp op expr ty) preq pes) req preq es pes := by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate]
  cases h_wt with
  | unaryApp h_expr h_op =>
    let expr_eval := TPE.evaluate expr preq pes
    unfold TPE.apply₁
    split
    case h_1 => apply Residual.WellTyped.error
    case h_2 =>
      cases h : expr_eval.asValue with
      | some v =>
        simp only [someOrError]
        split
        case h_2 =>
          apply Residual.WellTyped.error
        case h_1 v ty ox x v₂ heq =>
          apply Residual.WellTyped.val
          unfold Spec.apply₁ at heq
          split at heq
          any_goals
            cases h_op
            simp only [Except.toOption, Option.some.injEq] at heq
            rw [← heq]
            apply InstanceOfType.instance_of_bool
            simp [InstanceOfBoolType]
          case h_2 =>
            simp only [Except.toOption, intOrErr] at heq
            rename Int64 => i
            cases h₂: i.neg?
            . rw [h₂] at heq
              simp at heq
            . rw [h₂] at heq
              simp only [Option.some.injEq] at heq
              rw [← heq]
              cases h_op
              apply InstanceOfType.instance_of_int
          case h_6 =>
           contradiction
      | none =>
        apply Residual.WellTyped.unaryApp
        case none.h₁ =>
          exact h_expr_wt
        case none.h₂ =>
          cases h_op
          all_goals
            first
            | apply UnaryResidualWellTyped.not
            | apply UnaryResidualWellTyped.neg
            | apply UnaryResidualWellTyped.isEmpty
            | apply UnaryResidualWellTyped.like
            | apply UnaryResidualWellTyped.is
            rw [partial_eval_preserves_typeof h_wf h_ref h_expr]
            assumption

/--
Helper theorem: Partial evaluation preserves well-typedness for set residuals.
-/
theorem partial_eval_well_typed_set {env : TypeEnv} {ls : List Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  (∀ r ∈ ls, Residual.WellTyped env (TPE.evaluate r preq pes)) →
  PEWellTyped env (Residual.set ls ty) (TPE.evaluate (Residual.set ls ty) preq pes) req preq es pes := by
  intros h_ls_wt h_wf h_ref h_wt
  cases h_wt
  rename_i ty₁ h₀ h₁ h₂
  simp only [TPE.evaluate, TPE.set, List.any_eq_true]
  split
  case h_1 x xs h₃ =>
    apply Residual.WellTyped.val
    apply InstanceOfType.instance_of_set
    intro v h₄
    unfold List.map₁ List.attach List.attachWith at h₃
    rw [List.map_pmap_subtype (fun x => TPE.evaluate x preq pes)] at h₃
    rw [List.mapM_map_combiner_option] at h₃
    rw [← Set.make_mem] at h₄
    have h₅ := List.mem_mapM_some_implies_exists_unmapped h₃ h₄
    rcases h₅ with ⟨y, h₆, h₇⟩
    specialize h₀ y h₆
    let h₈ := partial_eval_preserves_typeof h_wf h_ref h₀
    unfold Residual.asValue at h₇
    split at h₇
    case h_2 =>
      contradiction
    case h_1 x₂ v₂ ty₂ h₉ =>
      injection h₇
      rename_i h₇
      rw [h₇] at h₉
      let ih := h_ls_wt y h₆
      rw [h₉] at ih
      cases ih
      case val h₁₀ =>
      specialize h₁ y h₆
      rw [h₁] at h₈
      rw [h₉] at h₈
      simp only [Residual.typeOf] at h₈
      rw [← h₈]
      exact h₁₀
  case h_2 x h₃ =>
    split
    . apply Residual.WellTyped.error
    case isFalse _ =>
      apply Residual.WellTyped.set
      . intro x h₅
        simp only [List.map₁, List.attach, List.map_subtype, List.unattach_attachWith, List.mem_map] at h₅
        rcases h₅ with ⟨x₂, h₆, h₇⟩
        specialize h₀ x₂ h₆
        let ih := h_ls_wt x₂ h₆
        rw [← h₇]
        exact ih
      . intro x h₅
        simp only [List.map₁, List.attach, List.map_subtype, List.unattach_attachWith, List.mem_map] at h₅
        rcases h₅ with ⟨x₂, h₆, h₇⟩
        specialize h₀ x₂ h₆
        let h₆ := partial_eval_preserves_typeof h_wf h_ref h₀
        rw [h₇] at h₆
        rename_i h₈
        specialize h₁ x₂ h₈
        rw [← h₁]
        exact h₆
      . simp only [List.map₁, List.map_subtype, List.unattach_attach, bne_iff_ne, ne_eq, List.map_eq_nil_iff]
        simp only [bne_iff_ne, ne_eq] at h₂
        exact h₂

/--
Helper theorem: Partial evaluation preserves well-typedness for record residuals.
-/
theorem partial_eval_well_typed_record {env : TypeEnv} {ls : List (Attr × Residual)} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  (∀ k v, (k, v) ∈ ls → Residual.WellTyped env (TPE.evaluate v preq pes)) →
  PEWellTyped env (Residual.record ls ty) (TPE.evaluate (Residual.record ls ty) preq pes) req preq es pes := by
  intros h_ls_wt h_wf h_ref h_wt
  cases h_wt
  rename_i ty₁ h₀ h₁
  simp only [TPE.evaluate]
  unfold List.map₁ List.attach List.attachWith
  rw [List.map_pmap_subtype (fun x => (x.fst, TPE.evaluate x.snd preq pes)) ls]
  simp only [record, List.mapM_map, List.any_map, List.any_eq_true, Function.comp_apply, Prod.exists]
  let m := Map.mk ls
  split
  . rename_i x xs h₃
    apply Residual.WellTyped.val
    apply InstanceOfType.instance_of_record
    . intro k h₄
      rw [Map.contains_iff_some_find?] at h₄
      rcases h₄ with ⟨v, h₄⟩

      rw [← Map.list_find?_iff_make_find?] at h₄
      rw [Map.contains_iff_some_find?]
      unfold Function.comp at h₃
      simp [bindAttr] at h₃

      have h₈ := Map.list_find?_mapM_implies_exists_unmapped (λ x => (TPE.evaluate x preq pes).asValue) h₃ h₄
      rcases h₈ with ⟨v₂, h₈, h₉⟩
      simp at h₈

      rw [Map.list_find?_some_iff_map_find?_some] at h₉
      replace h₉ := Map.find?_mapOnValues_some (λ x => Qualified.required x.typeOf) h₉

      subst ty₁
      simp [Map.mapOnValues] at h₉
      exists (Qualified.required v₂.typeOf)
      rw [← Map.list_find?_iff_make_find?]
      rw [← Map.list_find?_iff_mk_find?] at h₉
      exact h₉
    . intro k v qty h₄ h₅
      rw [h₁] at h₅
      have h₆ := h₄
      rw [← Map.list_find?_iff_make_find?] at h₆
      have h₇ := h₅
      rw [← Map.list_find?_iff_make_find?] at h₇
      unfold Function.comp at h₃
      simp [bindAttr] at h₃
      have h₈ := Map.list_find?_mapM_implies_exists_unmapped (λ x => (TPE.evaluate x preq pes).asValue) h₃ h₆
      rcases h₈ with ⟨v₂, _, h₈⟩


      have h₇_new : ((Map.mk ls).mapOnValues (λ x => Qualified.required x.typeOf)).find? k = some qty := by
        unfold Map.mapOnValues
        simp [Map.kvs]
        simp [Map.find?]
        rw [h₇]

      have h₉_new := Map.find?_mapOnValues_some' (fun x: Residual => Qualified.required x.typeOf) h₇_new
      rcases h₉_new with ⟨v₃, h₁₀, h₉⟩
      rw [h₉]
      have h₁₁ := h₀
      have h₁₂ := List.mem_of_find?_eq_some h₈
      specialize h₁₁ k v₂ h₁₂
      rw [← Map.list_find?_iff_mk_find?] at h₁₀
      rw [h₁₀] at h₈
      injection h₈
      rename_i h₁₃
      simp only [Prod.mk.injEq, true_and] at h₁₃
      rw [h₁₃]
      rename_i h₁₄
      simp only [Residual.asValue] at h₁₄
      split at h₁₄
      case h_2 => contradiction
      rename_i v₄ ty h₁₅
      injection h₁₄; rename_i h₁₅
      simp only [Qualified.getType]
      rename_i h₁₆
      have h₁₇ := partial_eval_preserves_typeof h_wf h_ref h₁₁
      rw [h₁₆] at h₁₇
      rw [←h₁₇]
      simp only [Residual.typeOf]
      let ih := h_ls_wt k v₂ h₁₂
      rw [h₁₆] at ih
      cases ih
      rw [← h₁₅]
      assumption
    . intro k qty h₄ h₅
      subst ty₁
      replace h₄ : ((Map.mk ls).mapOnValues (λ x => Qualified.required x.typeOf)).find? k = some qty := by
        unfold Map.mapOnValues
        simp [Map.kvs]
        simp [Map.find?]
        rw [← Map.list_find?_iff_make_find?] at h₄
        rw [h₄]
      have h₅ := Map.find?_mapOnValues_some' (α := Attr) (fun x: Residual => Qualified.required x.typeOf) h₄

      rcases h₅ with ⟨v₂, h₅, _⟩
      rw [← Map.list_find?_iff_mk_find?] at h₅

      unfold Function.comp at h₃
      simp [bindAttr] at h₃
      have h₆ := Map.list_find?_mapM_implies_exists_mapped (λ x => (TPE.evaluate x preq pes).asValue) h₃ h₅

      rw [Map.contains_iff_some_find?]
      rcases h₆ with ⟨v₃, _, h₆⟩
      exists v₃
      rw [← Map.list_find?_iff_make_find?]
      exact h₆
  case h_2 x h₂ =>
    split
    . apply Residual.WellTyped.error
    case isFalse h₃ =>
      apply Residual.WellTyped.record
      . intros k v h₄
        have h₅ := List.mem_of_map_implies_exists_unmapped h₄
        rcases h₅ with ⟨p, h₅, h₆⟩
        cases p ; rename_i k₂ v₂
        simp only [Prod.mk.injEq] at h₆
        rcases h₆ with ⟨h₆, h₇⟩
        rw [← h₆] at h₅
        specialize h₀ k v₂ h₅
        have ih := h_ls_wt k v₂ h₅
        rw [h₇]
        assumption
      . rw [h₁]
        simp only [List.map_map]
        unfold Function.comp
        simp only
        congr 1
        apply List.map_func_ext
        intro x h₄
        congr 2

        cases x
        rename_i k v
        specialize h₀ k v h₄
        simp only
        let h₅ := partial_eval_preserves_typeof h_wf h_ref h₀
        rw [h₅]

/--
Helper theorem: Partial evaluation preserves well-typedness for getAttr residuals.
-/
theorem partial_eval_well_typed_getAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.getAttr expr attr ty) (TPE.evaluate (Residual.getAttr expr attr ty) preq pes) req preq es pes := by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.getAttr, TPE.attrsOf]
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
          have ih := h_expr_wt
          rw [h₃] at ih
          cases ih
          rename_i h_wt_val
          cases h_wt_val
          rename_i rty₂ h₈ h₉ _
          cases h₁₂ : m.find? attr
          . simp only [someOrError]
            apply Residual.WellTyped.error
          . simp only [someOrError]
            apply Residual.WellTyped.val
            have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₅
            rw [h₃, h₆] at h₁₁
            simp [Residual.typeOf] at h₁₁
        case getAttr_record rty h₄ h₅ h₆ =>
          have ih := h_expr_wt
          rw [h₃] at ih
          cases ih
          rename_i h_wt_rec
          cases h_wt_rec
          rename_i rty₂ h₈ h₉ _
          cases h₁₂ : m.find? attr
          . simp only [someOrError]
            apply Residual.WellTyped.error
          . rename_i v
            simp only [someOrError]
            apply Residual.WellTyped.val
            have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₄
            rw [h₃] at h₁₁
            rw [h₅] at h₁₁
            simp only [Residual.typeOf, CedarType.record.injEq] at h₁₁
            cases h₁₃ : (Map.find? rty attr) <;> rw [h₁₃] at h₆
            . simp only [Option.map_none, reduceCtorEq] at h₆
            rename_i qty
            simp only [Option.map_some, Option.some.injEq] at h₆
            rw [h₁₁] at h₉
            specialize h₉ attr v qty h₁₂ h₁₃
            rw [h₆] at h₉
            exact h₉
      case h_2 r₂ uid ty₂ h₃ =>
        cases h_wt
        case getAttr_entity ety rty h₄ h₅ h₆ h₇ =>
          have ih := h_expr_wt
          rw [h₃] at ih
          cases ih
          rename_i h_wt_ent
          cases h_wt_ent
          rename_i ety₂ h₈
          cases h₁₂ : m.find? attr
          . simp only [someOrError]
            apply Residual.WellTyped.error
          . rename_i v
            simp only [someOrError]
            apply Residual.WellTyped.val
            have h₁₁ := partial_eval_preserves_typeof h_wf h_ref h₅
            rw [h₃, h₆] at h₁₁
            simp only [Residual.typeOf, CedarType.entity.injEq] at h₁₁
            unfold RequestAndEntitiesRefine at h_ref
            rcases h_ref with ⟨h_rref, h_eref⟩
            unfold EntitiesRefine at h_eref
            unfold PartialEntities.attrs PartialEntities.get at h₂
            cases h₁₃ : (Map.find? pes uid) <;> rw [h₁₃] at h₂
            . simp at h₂
            . rename_i e
              specialize h_eref uid e h₁₃
              cases h_eref
              . rename_i h₁₄
                rcases h₁₄ with ⟨h₁₅, _⟩
                rw [h₁₅] at h₂
                simp only [Option.bind_some, PartialEntityData.attrs, Option.some.injEq] at h₂
                rw [← h₂] at h₁₂
                simp [Map.empty, Map.find?, Map.kvs, List.find?] at h₁₂
              . rename_i h₁₄
                rcases h₁₄ with ⟨e₂, h₁₄, h₁₅, _, h₁₇⟩
                simp only [Option.bind] at h₂
                rw [h₂] at h₁₅
                cases h₁₅
                rename_i h₁₈
                rw [h₁₈] at h₁₂
                have h_wf2 := h_wf
                unfold InstanceOfWellFormedEnvironment at h_wf2
                rcases h_wf2 with ⟨h₁₉, _, h₂₁⟩
                unfold InstanceOfSchema at h₂₁
                rcases h₂₁ with ⟨h₂₁, h₂₂⟩
                specialize h₂₁ uid e₂ h₁₄
                unfold InstanceOfSchemaEntry at h₂₁
                cases h₂₁
                . rename_i h₂₃
                  unfold InstanceOfEntitySchemaEntry at h₂₃
                  rcases h₂₃ with ⟨e₃, h₂₃, _, h₂₅, _, _⟩
                  unfold InstanceOfEntityType at h₈
                  rcases h₈ with ⟨h₈, _⟩
                  rw [← h₈] at h₂₃
                  cases h₂₅
                  rename_i h₂₉ h₃₀ h₃₁
                  specialize h₃₀ attr v
                  simp only [EntitySchema.attrs?, Option.map_map, Option.map_eq_some_iff, Function.comp_apply] at h₄
                  rcases h₄ with ⟨e₄, h₃₂, h₃₃⟩
                  rw [h₁₁] at h₂₃
                  rw [h₂₃] at h₃₂
                  injection h₃₂; rename_i h₃₂
                  rw [← h₃₂] at h₃₃
                  rw [← h₃₃] at h₇
                  cases h₃₄ : (Map.find? e₃.attrs attr)
                  . specialize h₂₉ attr
                    simp only [Map.contains] at h₂₉
                    rw [h₁₂] at h₂₉
                    simp only [Option.isSome_some, forall_const] at h₂₉
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
                      simp only [Option.map_some, Option.some.injEq] at h₇
                      rw [← h₇]
                      rw [h₃₆]
                      have h₃₇ := type_lifting_preserves_instance_of_type h₃₀
                      cases ty₃
                      all_goals
                        rename_i ty₃
                        simp only [Qualified.getType] at h₃₇
                        simp only [Qualified.getType, QualifiedType.liftBoolTypes]
                        exact h₃₇
                . rename_i h₂₃
                  unfold InstanceOfActionSchemaEntry at h₂₃
                  rcases h₂₃ with ⟨e₃, h₂₃, _, _⟩
                  rw [e₃] at h₁₂
                  simp [Map.empty, Map.find?, Map.kvs] at h₁₂
        case getAttr_record rty h₄ h₅ h₆ =>
          have h₇ := partial_eval_preserves_typeof h_wf h_ref h₄
          rw [h₃] at h₇
          rw [h₅] at h₇
          simp only [Residual.typeOf] at h₇
          have h₈ := h_expr_wt
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
          exact h_expr_wt
        case h₂ =>
          have h₈ := partial_eval_preserves_typeof h_wf h_ref h₆
          rw [h₈]
          rw [h₇]
        case h₃ =>
          rw [h₅]
        case h₄ =>
          exact h₈
      case getAttr_record rty h₆ h₇ h₈ =>
        apply Residual.WellTyped.getAttr_record
        case h₁ =>
          exact h_expr_wt
        case h₂ =>
          have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
          rw [h₁₀]
          rw [h₇]
        case h₃ =>
          rw [h₈]

/--
Helper theorem: Partial evaluation preserves well-typedness for call residuals.
-/
theorem partial_eval_well_typed_call {env : TypeEnv} {xfn : ExtFun} {args : List Residual} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  (∀ r ∈ args, Residual.WellTyped env (TPE.evaluate r preq pes)) →
  PEWellTyped env (Residual.call xfn args ty) (TPE.evaluate (Residual.call xfn args ty) preq pes) req preq es pes := by
  intros h_args_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.call, List.any_eq_true]
  simp only [List.map₁, List.attach, List.attachWith, List.map_subtype, List.mapM_map, List.mem_map, List.mem_unattach, List.mem_pmap, Subtype.mk.injEq, exists_prop, exists_eq_right, and_self]
  unfold Function.comp
  simp only [List.map_subtype, List.mem_map, List.mem_unattach, List.mem_pmap, Subtype.mk.injEq, exists_prop, exists_eq_right, and_self]
  unfold List.unattach
  rw [List.map_pmap_subtype (fun x => x)]
  simp only [List.map_id_fun', id_eq, List.map_subtype, List.mem_map, List.mem_unattach, List.mem_pmap, Subtype.mk.injEq, exists_prop, exists_eq_right, and_self]
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
        simp only [someOrError, Except.toOption]
        apply Residual.WellTyped.val
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
        | apply InstanceOfType.instance_of_ext
          simp [InstanceOfExtType]
        | apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
      case h_2 x₂ h₄ =>
        simp only [someOrError, Except.toOption]
        first
        | apply Residual.WellTyped.error
        | apply Residual.WellTyped.val
          cases h₃
          apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
    case h_2 | h_3 | h_4 | h_5 =>
      rename_i xf vs d₁ d₂
      simp only [someOrError, Except.toOption]
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
        simp only [someOrError, Except.toOption]
        apply Residual.WellTyped.val
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
        | apply InstanceOfType.instance_of_ext
          simp [InstanceOfExtType]
        | apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
      case h_2 x₂ h₄ =>
        simp only [someOrError, Except.toOption]
        first
        | apply Residual.WellTyped.error
        | apply Residual.WellTyped.val
          cases h₃
          apply InstanceOfType.instance_of_bool
          simp [InstanceOfBoolType]
      try case h_3 x₂ v =>
        simp only [someOrError, Except.toOption]
        cases h₃
        apply Residual.WellTyped.val
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
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
      apply Residual.WellTyped.val
      first
      | apply InstanceOfType.instance_of_ext
        simp [InstanceOfExtType]
      | apply InstanceOfType.instance_of_int
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
          apply partial_eval_preserves_typeof h_wf h_ref h₁
        case a =>
          intro x h₄
          cases x
          . rename_i v ty
            simp [TPE.evaluate]
          all_goals {
            simp [Residual.asValue] at h₄
          }

/--
Helper theorem: Partial evaluation preserves well-typedness for hasAttr residuals.
-/
theorem partial_eval_well_typed_hasAttr {env : TypeEnv} {expr : Residual} {attr : Attr} {ty : CedarType} {req : Request} {preq : PartialRequest} {es : Entities} {pes : PartialEntities} :
  Residual.WellTyped env (TPE.evaluate expr preq pes) →
  PEWellTyped env (Residual.hasAttr expr attr ty) (TPE.evaluate (Residual.hasAttr expr attr ty) preq pes) req preq es pes := by
  intros h_expr_wt h_wf h_ref h_wt
  simp only [TPE.evaluate, TPE.hasAttr, TPE.attrsOf]
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
          exact h_expr_wt
        case h₂ =>
          have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₅
          rw [h₁₀]
          rw [h₆]
      case hasAttr_record rty h₆ h₇ =>
        apply Residual.WellTyped.hasAttr_record
        case h₁ =>
          exact h_expr_wt
        case h₂ =>
          have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h₆
          rw [h₁₀]
          rw [h₇]

theorem partial_eval_well_typed_app₂_values_hasTag :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = some (Value.prim (Prim.entityUID id₁)) →
  (TPE.evaluate expr2 preq pes).asValue = some (Value.prim (Prim.string id₂)) →
  PEWellTyped env (Residual.binaryApp BinaryOp.hasTag expr1 expr2 ty)
    (someOrSelf ((TPE.hasTag id1 id2 pes).bind fun a => some (Value.prim (Prim.bool a))) ty
    (Residual.binaryApp BinaryOp.hasTag (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) ty)) req preq es pes
   := by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt
  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  cases TPE.hasTag id1 id2 pes
  . simp only [someOrSelf, Option.bind_none]
    unfold Residual.asValue at h₁
    unfold Residual.asValue at h₂
    split at h₁
    . split at h₂
      . injection h₁
        injection h₂
        rename_i x v ty₁ h₃ h₄ h₅ ty₂ h₇ h₈ h₉
        rw [h₃]
        rw [h₇]
        apply Residual.WellTyped.binaryApp
        . apply Residual.WellTyped.val
          rw [h₃] at ih₁
          rw [h₇] at ih₂
          cases ih₁
          rename_i h₈
          exact h₈
        . apply Residual.WellTyped.val
          rw [h₃] at ih₁
          rw [h₇] at ih₂
          cases ih₂
          rename_i h₈
          exact h₈
        . rw [h₈]
          rw [h₉]
          cases h_op
          . apply BinaryResidualWellTyped.hasTag
            . simp only [Residual.typeOf]
              rename_i ety₂ eq₁ eq₂
              have hᵣ : (ty₁ = CedarType.entity ety₂) := by {
                have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr1
                rw [← h₁₀] at eq₁
                rw [h₃] at eq₁
                simp only [Residual.typeOf] at eq₁
                exact eq₁
              }
              exact hᵣ
            . simp only [Residual.typeOf]
              rename_i ety₂ eq₁ eq₂
              have hᵣ : (ty₂ = CedarType.string) := by {
                have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr2
                rw [← h₁₀] at eq₂
                rw [h₇] at eq₂
                simp [Residual.typeOf] at eq₂

                exact eq₂
              }
              exact hᵣ
      . contradiction
    . contradiction
  . simp only [someOrSelf, Option.bind_some]
    apply Residual.WellTyped.val
    cases h_op
    . apply InstanceOfType.instance_of_bool
      simp [InstanceOfBoolType]


theorem partial_eval_well_typed_app₂_values_getTag :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = some (Value.prim (Prim.entityUID id₁)) →
  (TPE.evaluate expr2 preq pes).asValue = some (Value.prim (Prim.string id₂)) →
  PEWellTyped env (Residual.binaryApp BinaryOp.getTag expr1 expr2 ty) (TPE.getTag id₁ id₂ pes ty) req preq es pes
   := by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt
  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>


  unfold TPE.getTag
  split
  . unfold someOrError
    split
    . apply Residual.WellTyped.val
      rename Option (Data.Map Tag Value) => x
      rename_i tags heq x₁ x₂ x₃ v h₃
      cases h_op
      rename_i ety ty h₄ h₅ h₆
      unfold EntitiesRefine at h_eref
      unfold Data.Map.find? at h₃
      split at h₃
      case h_2 =>  contradiction
      dsimp only [PartialEntities.tags, PartialEntities.get] at heq
      rename Value => v₂
      cases h₇: (Data.Map.find? pes id₁)
      case h_1.none =>
        rw [h₇] at heq
        simp at heq

      rename Value => v₃
      rename PartialEntityData => pv
      specialize h_eref id₁ pv h₇
      rw [h₇] at heq
      simp only [Option.bind_some] at heq
      cases h_eref
      case h_1.some.inl =>
        rename_i heq₂ h₈
        rcases h₈ with ⟨h₉, _⟩
        unfold PartialEntityData.tags at heq
        rw [h₉] at heq
        simp only [Option.some.injEq] at heq
        rw [← heq] at heq₂
        simp only [Map.kvs] at heq₂
        unfold Data.Map.empty at heq₂
        dsimp only [List.find?_nil] at heq₂
        contradiction
      rename_i h₈
      rcases h₈ with ⟨e, h₈, h₉, h₁₀, h₁₁⟩
      rw [heq] at h₁₁
      cases h₁₁
      rename_i h₁₂
      rename_i h₁₃
      rw [h₁₂] at h₁₃
      let h_wf₂ := h_wf
      unfold InstanceOfWellFormedEnvironment at h_wf₂
      rcases h_wf₂ with ⟨h₁₄, _, h₁₆⟩
      unfold InstanceOfSchema at h₁₆
      rcases h₁₆ with ⟨h₁₆, h₁₇⟩
      specialize h₁₆ id₁ e h₈
      unfold InstanceOfSchemaEntry at h₁₆
      cases h₁₆
      . rename_i h₁₆
        unfold InstanceOfEntitySchemaEntry at h₁₆
        rcases h₁₆ with ⟨_, _, _, _, _, h₁₇⟩
        unfold InstanceOfEntityTags at h₁₇
        rename EntitySchemaEntry => w
        cases h₁₈: w.tags? <;> rw [h₁₈] at h₁₇ <;> simp only at h₁₇
        . rw [h₁₇] at h₁₃
          simp [Data.Map.empty, Data.Map.mk, Data.Map.kvs] at h₁₃
        . have h₁₈ : v₃ ∈ e.tags.values := by {
            -- Use h₁₃
            -- use lemma find?_mem_toList
            have h₁₉ := List.find?_some_is_mem h₁₃
            have h₂₀ := Map.in_list_in_values h₁₉
            exact h₂₀
          }
          specialize h₁₇ v₃ h₁₈
          rename CedarType => ty
          rename_i h₁₉
          rename CedarType => ty₂
          injection h₃
          rename_i h₃
          rw [← h₃]
          -- h₄ is finally useful
          rename Data.Map.find? env.ets id₁.ty = some w => h₂₁
          unfold EntitySchema.tags? at h₄
          have h_ety_eq : ety = id₁.ty := by {
            have h₂₁ := partial_eval_preserves_typeof h_wf h_ref h_expr1
            rw [← h₂₁] at h₅
            unfold Residual.asValue at h₁
            cases h₂₂: TPE.evaluate expr1 preq pes
            . rw [h₂₂] at h₁
              rename Value => v₄
              simp only [Option.some.injEq] at h₁
              rw [h₁] at h₂₂
              rw [h₂₂] at h₅
              rw [h₂₂] at h₂₁
              rename  expr1.typeOf = CedarType.entity ety => h₂₃
              rw [h₂₃] at h₂₁
              simp only [Residual.typeOf] at h₂₁
              rename CedarType => ty₃
              rw [h₂₂] at ih₁
              cases ih₁
              rename_i h₂₃
              rw [h₂₁] at h₂₃
              cases h₂₃
              rename_i h₂₄
              unfold InstanceOfEntityType at h₂₄
              rcases h₂₄ with ⟨h₂₄, _⟩
              exact h₂₄
            all_goals {
              rw [h₂₂] at h₁
              simp at h₁
            }
          }
          rw [h_ety_eq] at h₄
          rw [h₂₁] at h₄
          simp only [Option.map_some, Option.some.injEq] at h₄
          rw [h₁₉] at h₄
          simp only [Option.some.injEq] at h₄
          rw [h₄] at h₁₇
          exact type_lifting_preserves_instance_of_type h₁₇
      . rename_i h₁₆
        unfold InstanceOfActionSchemaEntry at h₁₆
        rcases h₁₆ with ⟨_, h₁₇, _, _, _⟩
        rw [h₁₇] at h₁₃
        simp [Data.Map.empty, Data.Map.kvs] at h₁₃
    . apply Residual.WellTyped.error
  . apply Residual.WellTyped.binaryApp
    . unfold Residual.asValue at h₁
      cases h₃: TPE.evaluate expr1 preq pes
      all_goals (rw [h₃] at h₁
                 simp at h₁)
      rename_i x heq v ty
      rw [h₃] at ih₁
      rw [h₁] at ih₁
      have h_ety_eq : ty = (CedarType.entity id₁.ty) := by {
            have h₄ := partial_eval_preserves_typeof h_wf h_ref h_expr1
            cases ih₁
            rename_i h₅
            cases h₅
            rename EntityType => ty₂
            rename_i h₅
            unfold InstanceOfEntityType at h₅
            rcases h₅ with ⟨h₅, _⟩
            rw [h₅]
          }
      rw [h_ety_eq] at ih₁
      exact ih₁
    . apply Residual.WellTyped.val
      apply InstanceOfType.instance_of_string
    . cases h_op with
      | getTag h₃ h₄ h₅ =>
      apply BinaryResidualWellTyped.getTag
      . simp only [Residual.typeOf, CedarType.entity.injEq]
        rfl
      . simp [Residual.typeOf]
      . rename_i ety ty
        have h₄ : ety = id₁.ty := by
          have h₄ := partial_eval_preserves_typeof h_wf h_ref h_expr1
          simp only [Residual.asValue] at h₁
          split at h₁
          case h_2 =>
            contradiction
          rename_i x v ty h₅
          rw [h₅] at ih₁
          cases ih₁
          rename_i h₆
          injection h₁ with h₇
          rw [h₇] at h₆
          rw [h₅, h₃, h₇] at h₄
          simp only [Residual.typeOf] at h₄
          cases h₆
          rename_i ety₂ h₈
          injection h₄ with h₄
          unfold InstanceOfEntityType at h₈
          rcases h₈ with ⟨h₉, _⟩
          rw [h₉] at h₄
          rw [h₄]
        rw [h₄] at h₅
        exact h₅


theorem partial_eval_well_typed_app₂_values_mem :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = .some v₁ →
  (TPE.evaluate expr2 preq pes).asValue = .some v₂ →
  PEWellTyped env (Residual.binaryApp BinaryOp.mem expr1 expr2 ty) (Residual.binaryApp BinaryOp.mem (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) ty) req preq es pes
   := by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt
  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  unfold Residual.asValue at h₁
  unfold Residual.asValue at h₂
  split at h₁
  case h_1 x v ty₁ h₃ =>
    split at h₂
    case h_1 x₂ v₃ ty₂ h₇ =>
      -- both expr1 and expr2 are values
      injection h₁
      injection h₂
      rename_i h₈ h₉
      
      rw [h₃, h₇]
      rw [h₃] at ih₁
      rw [h₇] at ih₂
      rw [h₉]
      apply Residual.WellTyped.binaryApp
      . apply Residual.WellTyped.val
        cases ih₁
        rename_i h₈
        exact h₈
      . apply Residual.WellTyped.val
        cases ih₂
        rename_i h₈
        rw [h₉] at h₈
        exact h₈
      . rw [h₈]
        cases h_op
        . apply BinaryResidualWellTyped.memₑ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₁ = CedarType.entity ety₁) := by {
              have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr1
              rw [← h₁₀] at eq₁
              rw [h₃] at eq₁
              simp only [Residual.typeOf] at eq₁
              exact eq₁
            }
            exact hᵣ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₂ = CedarType.entity ety₂) := by {
              have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr2
              rw [← h₁₀] at eq₂
              rw [h₇] at eq₂
              simp only [Residual.typeOf] at eq₂
              exact eq₂
            }
            exact hᵣ
        . apply BinaryResidualWellTyped.memₛ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₁ = CedarType.entity ety₁) := by {
              have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr1
              rw [← h₁₀] at eq₁
              rw [h₃] at eq₁
              simp only [Residual.typeOf] at eq₁
              exact eq₁
            }
            exact hᵣ
          . simp only [Residual.typeOf]
            rename_i ety₁ ety₂ eq₁ eq₂
            have hᵣ : (ty₂ = (CedarType.entity ety₂).set) := by {
              have h₁₀ := partial_eval_preserves_typeof h_wf h_ref h_expr2
              rw [← h₁₀] at eq₂
              rw [h₇] at eq₂
              simp only [Residual.typeOf] at eq₂
              exact eq₂
            }
            exact hᵣ
    . contradiction
  . contradiction

theorem partial_eval_well_typed_app₂_values :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = .some v₁ →
  (TPE.evaluate expr2 preq pes).asValue = .some v₂ →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes := by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt

  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>

  simp only [TPE.apply₂]
  rw [h₁, h₂]
  simp only
  split

  any_goals
    apply Residual.WellTyped.val
    cases h_op
    all_goals
      apply InstanceOfType.instance_of_bool
      unfold InstanceOfBoolType
      split <;> try simp only
      contradiction
  case h_8 | h_9 | h_10 =>
    simp [Option.bind]
    split
    case h_1 =>
      apply Residual.WellTyped.error
    case h_2 =>
      apply Residual.WellTyped.val
      cases h_op
      all_goals {
        apply InstanceOfType.instance_of_int
      }
  -- mem and mem set
  case h_14 | h_15 =>
    rename_i v1 v2 id1 id2
    simp [Option.bind]
    split
    case h_1 =>
      simp only [someOrSelf, TPE.apply₂.self]
      apply partial_eval_well_typed_app₂_values_mem ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt₂
    case h_2 =>
      simp only [someOrSelf]
      apply Residual.WellTyped.val
      cases h_op
      all_goals
        apply InstanceOfType.instance_of_bool
        simp [InstanceOfBoolType]
  case h_16 v1 v2 id1 id2 =>
    simp [apply₂.self]
    apply partial_eval_well_typed_app₂_values_hasTag ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt₂
  case h_17 v₁ v₂ id₁ id₂ =>
    apply partial_eval_well_typed_app₂_values_getTag ih₁ ih₂ h₁ h₂ h_wf h_ref h_wt₂
  case h_18 =>
    apply Residual.WellTyped.error

theorem partial_eval_well_typed_app₂_nonvalues :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  (TPE.evaluate expr1 preq pes).asValue = .none ∨ (TPE.evaluate expr2 preq pes).asValue = .none →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes := by
  unfold PEWellTyped
  intros ih₁ ih₂ h₁ h_wf h_ref h_wt

  let h_ref₂ := h_ref
  unfold RequestAndEntitiesRefine at h_ref₂
  rcases h_ref₂ with ⟨h_rref, h_eref⟩

  let h_wt₂ := h_wt
  cases h_wt with
  | binaryApp h_expr1 h_expr2 h_op =>


  simp only [TPE.apply₂]
  split
  case h_1 h₂ h₃ =>
    cases h₁
    case inl h₁ =>
      rw [h₁] at h₂
      contradiction
    case inr h₁ =>
      rw [h₁] at h₃
      contradiction
  case h_2 _ _ =>
    let h₁ := partial_eval_preserves_typeof h_wf h_ref h_expr1
    have h₂ := partial_eval_preserves_typeof h_wf h_ref h_expr2
    split
    case h_1 =>
      apply Residual.WellTyped.error
    case h_2 =>
      apply Residual.WellTyped.error

    case h_3 =>
    rename_i h₁ r₁ r₂ h₃ h₄
    unfold apply₂.self
    apply Residual.WellTyped.binaryApp
    cases op
    any_goals (exact ih₁)
    any_goals (exact ih₂)
    case h₃ =>
    cases op
    case eq =>
      cases h₅: h_op
      case eq_val =>
        cases h_wt₂
        rename_i h₆
        simp only [TPE.evaluate]
        exact h₆
      case eq_entity =>
        apply BinaryResidualWellTyped.eq_entity
        case h₁ h₉ _ =>
          rw [h₁, h₉]
        case h₂ h₇ h₈ =>
          rw [h₂, h₈]
      case eq h₉ =>
        apply BinaryResidualWellTyped.eq
        rw [h₁, h₂, h₉]
    case mem =>
      cases h_op <;> rename_i ety₁ ety₂ h₅ h₆
      . apply BinaryResidualWellTyped.memₑ
        . rw [h₁, h₅]
        . rw [h₂, h₆]
      . apply BinaryResidualWellTyped.memₛ
        . rw [h₁, h₅]
        . rw [h₂, h₆]
    case hasTag =>
      cases h_op
      apply BinaryResidualWellTyped.hasTag <;> rename_i ety h₅ h₆
      . rw [h₁, h₅]
        congr
        have h₈ : ety = ety := by simp only
        exact h₈
      . rw [h₂, h₆]
    case getTag =>
      cases h_op ; rename_i ty h₅ h₆
      apply BinaryResidualWellTyped.getTag
      . rw [h₁, h₅]
      . rw [h₂, h₆]
      . rw [ty]
    case less =>
      cases h_op <;> rename_i h₃ h₄
      case less_int =>
        apply BinaryResidualWellTyped.less_int
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case less_datetime =>
        apply BinaryResidualWellTyped.less_datetime
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case less_duration =>
        apply BinaryResidualWellTyped.less_duration
        . rw [h₁, h₃]
        . rw [h₂, h₄]
    case lessEq =>
      cases h_op <;> rename_i h₃ h₄
      case lessEq_int =>
        apply BinaryResidualWellTyped.lessEq_int
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case lessEq_datetime =>
        apply BinaryResidualWellTyped.lessEq_datetime
        . rw [h₁, h₃]
        . rw [h₂, h₄]
      case lessEq_duration =>
        apply BinaryResidualWellTyped.lessEq_duration
        . rw [h₁, h₃]
        . rw [h₂, h₄]
    case mul | sub | add =>
      cases h_op <;> rename_i h₃ h₄
      first
      | apply BinaryResidualWellTyped.mul
      | apply BinaryResidualWellTyped.sub
      | apply BinaryResidualWellTyped.add
      . rw [h₁, h₃]
      . rw [h₂, h₄]
    case contains =>
      cases h_op <;> rename_i h₃
      apply BinaryResidualWellTyped.contains
      rw [h₁, h₂]
      exact h₃
    case containsAll | containsAny =>
      cases h_op <;> rename_i ty h₃ h₄
      first
      | apply BinaryResidualWellTyped.containsAll
      | apply BinaryResidualWellTyped.containsAny
      rw [h₁, h₃]
      rw [h₂, h₄]



theorem partial_eval_well_typed_app₂ :
  Residual.WellTyped env (TPE.evaluate expr1 preq pes) →
  Residual.WellTyped env (TPE.evaluate expr2 preq pes) →
  PEWellTyped env (Residual.binaryApp op expr1 expr2 ty) (TPE.apply₂ op (TPE.evaluate expr1 preq pes) (TPE.evaluate expr2 preq pes) pes ty) req preq es pes := by
  intro ih₁ ih₂ h₁
  cases h₂ : (TPE.evaluate expr1 preq pes).asValue
  case none =>
    apply partial_eval_well_typed_app₂_nonvalues ih₁ ih₂
    . left
      exact h₂
    . exact h₁
  case some v₁ =>
    cases h₃ : (TPE.evaluate expr2 preq pes).asValue
    case none =>
      apply partial_eval_well_typed_app₂_nonvalues ih₁ ih₂
      . right
        exact h₃
      . exact h₁
    case some v₂ =>
      apply partial_eval_well_typed_app₂_values ih₁ ih₂ h₂ h₃
      . exact h₁
