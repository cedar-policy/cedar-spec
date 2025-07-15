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

import Cedar.Spec
import Cedar.Spec.Authorizer
import Cedar.Thm.Authorization.Evaluator
import Cedar.Thm.Data
import Cedar.Thm.Validation.Typechecker.BinaryApp -- mapM'_asEntityUID_eq_entities

/-!
This file contains useful lemmas about the `Authorizer` functions.
-/

namespace Cedar.Thm

open Cedar.Spec Cedar.Data

theorem determiningPolicies_wf {policies : Policies} {request : Request} {entities : Entities} :
  (isAuthorized request entities policies).determiningPolicies.WellFormed
:= by
  simp only [Set.WellFormed, isAuthorized, Set.toList, Bool.and_eq_true, Bool.not_eq_true']
  cases (satisfiedPolicies .forbid policies request entities).isEmpty <;>
  cases (satisfiedPolicies .permit policies request entities).isEmpty <;>
  simp only [and_true, and_false, and_self, ite_true, ite_false, reduceCtorEq]
  all_goals {
    unfold satisfiedPolicies
    simp only [Set.make_make_eqv]
    apply List.Equiv.symm
    exact Set.elts_make_equiv
  }

theorem if_hasError_then_exists_error {policy : Policy} {request : Request} {entities : Entities} :
  hasError policy request entities →
  ∃ err, evaluate policy.toExpr request entities = .error err
:= by
  intro h₁
  unfold hasError at h₁
  split at h₁
  · simp at h₁
  · rename_i err _ ; exists err

theorem if_satisfied_then_satisfiedPolicies_non_empty {effect : Effect} {policies : Policies} {request : Request} {entities : Entities} :
  (∃ policy,
    policy ∈ policies ∧
    policy.effect = effect ∧
    satisfied policy request entities) →
  (satisfiedPolicies effect policies request entities).isEmpty = false
:= by
  intro h₀
  replace ⟨policy, h₀⟩ := h₀
  unfold satisfiedPolicies
  rw [←Set.make_non_empty]
  apply @List.ne_nil_of_mem _ policy.id
  rw [List.mem_filterMap]
  exists policy
  unfold satisfiedWithEffect
  simp [h₀]

theorem if_satisfiedPolicies_non_empty_then_satisfied {effect : Effect} {policies : Policies} {request : Request} {entities : Entities} :
  (satisfiedPolicies effect policies request entities).isEmpty = false →
  ∃ policy,
    policy ∈ policies ∧
    policy.effect = effect ∧
    satisfied policy request entities
:= by
  unfold satisfiedPolicies
  intro h₀
  rw [←Set.make_non_empty] at h₀
  have ⟨pid, h₁⟩ := List.exists_mem_of_ne_nil _ h₀
  rw [List.mem_filterMap] at h₁
  replace ⟨policy, h₁, h₂⟩ := h₁
  unfold satisfiedWithEffect at h₂
  exists policy
  simp [h₁]
  cases h₃ : (policy.effect == effect) <;> simp at h₃
  case false => simp [h₃] at h₂
  case true =>
    simp [h₃]
    cases h₄ : (satisfied policy request entities) with
    | true => rfl
    | false => simp [h₃, h₄] at h₂

theorem satisfiedPolicies_order_and_dup_independent {policies₁ policies₂ : Policies} (effect : Effect) (request : Request) (entities : Entities) :
  policies₁ ≡ policies₂ →
  satisfiedPolicies effect policies₁ request entities = satisfiedPolicies effect policies₂ request entities
:= by
  intro h₁
  unfold satisfiedPolicies
  rw [Set.make_make_eqv]
  exact List.filterMap_equiv (satisfiedWithEffect effect · request entities) policies₁ policies₂ h₁

theorem errorPolicies_order_and_dup_independent {policies₁ policies₂ : Policies} (request : Request) (entities : Entities) :
  policies₁ ≡ policies₂ →
  errorPolicies policies₁ request entities = errorPolicies policies₂ request entities
:= by
  intro h₁
  unfold errorPolicies
  rw [Set.make_make_eqv]
  exact List.filterMap_equiv (errored · request entities) policies₁ policies₂ h₁

theorem satisfied_policies_congr_evaluate {ps : Policies} {r₁ r₂ : Request} {es₁ es₂ : Entities} (effect : Effect)
  (heq : ∀ p ∈ ps, evaluate p.toExpr r₁ es₁ = evaluate p.toExpr r₂ es₂) :
  satisfiedPolicies effect ps r₁ es₁ = satisfiedPolicies effect ps r₂ es₂
:= by
  simp only [satisfiedPolicies]
  replace heq : ∀ p ∈ ps, satisfiedWithEffect effect p r₁ es₁ = satisfiedWithEffect effect p r₂ es₂ := by
    intro p hp
    specialize heq p hp
    simp only [heq, satisfiedWithEffect, satisfied]
  rw [List.filterMap_congr heq]

theorem error_policies_congr_evaluate {ps : Policies} {r₁ r₂ : Request} {es₁ es₂ : Entities}
  (heq : ∀ p ∈ ps, evaluate p.toExpr r₁ es₁ = evaluate p.toExpr r₂ es₂) :
  errorPolicies ps r₁ es₁ = errorPolicies ps r₂ es₂
:= by
  simp only [errorPolicies]
  replace heq : ∀ p ∈ ps, errored p r₁ es₁ = errored p r₂ es₂ := by
    intro p hp
    specialize heq p hp
    simp [heq, errored, hasError]
  rw [List.filterMap_congr heq]

theorem is_authorized_congr_evaluate {ps : Policies} {r₁ r₂ : Request} {es₁ es₂ : Entities}
  (heq : ∀ p ∈ ps, evaluate p.toExpr r₁ es₁ = evaluate p.toExpr r₂ es₂) :
  isAuthorized r₁ es₁ ps = isAuthorized r₂ es₂ ps
:= by
  simp only [isAuthorized]
  rw [
    satisfied_policies_congr_evaluate .permit heq,
    satisfied_policies_congr_evaluate .forbid heq,
    error_policies_congr_evaluate heq
  ]

/--
  an alternate, proved-equivalent, definition of errorPolicies that's easier to prove things about
-/
def alternateErrorPolicies (policies : Policies) (request : Request) (entities : Entities) : Set PolicyID :=
  Set.make (List.map Policy.id (policies.filter (hasError · request entities)))

theorem alternate_errorPolicies_equiv_errorPolicies (policies : Policies) (request : Request) (entities : Entities) :
  errorPolicies policies request entities = alternateErrorPolicies policies request entities
:= by
  unfold errorPolicies alternateErrorPolicies
  rw [Set.make_make_eqv]
  simp [List.Equiv, List.subset_def]
  apply And.intro
  case left =>
    intro pid p h₁ h₂
    exists p
    unfold errored hasError at h₂
    split at h₂ <;>
    simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, Option.some.injEq] at h₂ <;>
    rename_i h₃
    unfold hasError
    apply And.intro _ h₂
    simp only [h₁, h₃, and_self]
  case right =>
    intro pid p h₁ h₂ h₃
    exists p
    simp only [h₁, errored, h₂, reduceIte, h₃, and_self]

theorem principal_eval_ok_means_principal_in_uid {policy : Policy} {request : Request} {entities : Entities} {uid: EntityUID} :
  evaluate policy.principalScope.toExpr request entities = .ok true →
  policy.principalScope.scope.bound = .some uid →
  inₑ request.principal uid entities = true
:= by
  intro h₁ h₂
  simp [PrincipalScope.toExpr, Scope.toExpr] at h₁
  simp [Scope.bound, PrincipalScope.scope] at h₂
  generalize h₃ : policy.principalScope.1 = x
  rw [h₃] at h₁ h₂
  cases x <;> simp at h₁ h₂ <;>
  rw [h₂] at h₁
  case eq =>
    simp [evaluate, Var.eqEntityUID, apply₂] at h₁
    simp [inₑ, h₁]
  case mem =>
    simp [evaluate, Var.inEntityUID, apply₂] at h₁
    exact h₁
  case isMem =>
    replace h₁ := and_true_implies_right_true h₁
    simp [evaluate, Var.inEntityUID, apply₂] at h₁
    exact h₁

theorem resource_eval_ok_means_resource_in_uid {policy : Policy} {request : Request} {entities : Entities} {uid : EntityUID} :
  evaluate policy.resourceScope.toExpr request entities = .ok true →
  policy.resourceScope.scope.bound = .some uid →
  inₑ request.resource uid entities = true
:= by
  intro h₁ h₂
  simp [ResourceScope.toExpr, Scope.toExpr] at h₁
  simp [Scope.bound, ResourceScope.scope] at h₂
  generalize h₃ : policy.resourceScope.1 = x
  rw [h₃] at h₁ h₂
  cases x <;> simp at h₁ h₂ <;>
  rw [h₂] at h₁
  case eq =>
    simp [evaluate, Var.eqEntityUID, apply₂] at h₁
    simp [inₑ, h₁]
  case mem =>
    simp [evaluate, Var.inEntityUID, apply₂] at h₁
    exact h₁
  case isMem =>
    replace h₁ := and_true_implies_right_true h₁
    simp [evaluate, Var.inEntityUID, apply₂] at h₁
    exact h₁

theorem satisfied_implies_principal_scope {policy : Policy} {request : Request} {entities : Entities} {uid : EntityUID} :
  satisfied policy request entities = true →
  policy.principalScope.scope.bound = .some uid →
  inₑ request.principal uid entities = true
:= by
  intro h₁ h₂
  simp [satisfied, Policy.toExpr] at h₁
  replace h₁ := and_true_implies_left_true h₁
  exact principal_eval_ok_means_principal_in_uid h₁ h₂

theorem satisfied_implies_resource_scope {policy : Policy} {request : Request} {entities : Entities} {uid : EntityUID} :
  satisfied policy request entities = true →
  policy.resourceScope.scope.bound = .some uid →
  inₑ request.resource uid entities = true
:= by
  intro h₁ h₂
  simp [satisfied, Policy.toExpr] at h₁
  replace h₁ :=
    and_true_implies_left_true
      (and_true_implies_right_true
        (and_true_implies_right_true h₁))
  exact resource_eval_ok_means_resource_in_uid h₁ h₂

theorem mapM_evaluate_uids_produces_uids (list : List EntityUID) (request : Request) (entities : Entities) :
  List.mapM (evaluate · request entities) (list.map fun uid => Expr.lit (.entityUID uid)) =
  .ok (list.map (Value.prim ∘ Prim.entityUID))
:= by
  rw [List.mapM_map]
  unfold evaluate
  exact List.mapM_pure

theorem asEntityUID_of_uid (uid : EntityUID) :
  Value.asEntityUID (.prim (.entityUID uid)) = .ok uid
:= by
  unfold Value.asEntityUID
  split <;> simp
  case h_1 uid' h => simp at h; simp [h]

theorem mapM_asEntityUID_of_uid (uids : List EntityUID) :
  List.mapM Value.asEntityUID (uids.map (Value.prim ∘ Prim.entityUID)) = .ok uids
:= by
  induction uids
  case nil =>
    rw [List.map_nil, List.mapM_nil]
    simp [pure, Except.pure]
  case cons x xs ih =>
    rw [List.map_cons, List.mapM_cons]
    simp [pure, Except.pure, asEntityUID_of_uid, ih]

/--
  Batteries has `Option.isSome_iff_exists`, but not this analogue for `Except`
-/
theorem Except.isOk_iff_exists {x : Except ε α} :
  Except.isOk x ↔ ∃ a, x = .ok a
:= by
  cases x <;> simp [Except.isOk, Except.toBool]

theorem if_mapM_doesn't_fail_on_list_then_doesn't_fail_on_set [LT α] [DecidableLT α] [StrictLT α] {f : α → Except ε β} {as : List α} :
  Except.isOk (as.mapM f) →
  Except.isOk ((Set.elts (Set.make as)).mapM f)
:= by
  intro h₁
  replace ⟨bs, h₁⟩ := Except.isOk_iff_exists.mp h₁
  replace h₁ := List.mapM_ok_implies_all_ok h₁
  cases as <;> simp at h₁
  case nil => simp [Set.elts_make_nil, pure, Except.pure, Except.isOk, Except.toBool]
  case cons ahd atl =>
    replace ⟨⟨b, _, h₁⟩, h₂⟩ := h₁
    apply Except.isOk_iff_exists.mpr
    apply List.all_ok_implies_mapM_ok
    intro a h₃
    rw [Set.in_list_iff_in_set] at h₃
    rw [← Set.make_mem] at h₃
    rcases List.mem_cons.mp h₃ with h₃ | h₃
    case a.inl => subst h₃ ; exists b
    case a.inr =>
      replace ⟨b, _, h₄⟩ := h₂ a h₃
      exists b

theorem mapM_asEntityUID_on_set_uids_produces_ok (uids : List EntityUID) :
  Except.isOk (List.mapM
    Value.asEntityUID
    (Set.elts (Set.make (uids.map (Value.prim ∘ Prim.entityUID)))))
:= by
  apply if_mapM_doesn't_fail_on_list_then_doesn't_fail_on_set
  unfold Except.isOk Except.toBool
  split <;> simp only [Bool.false_eq_true]
  case h_2 e h => simp only [mapM_asEntityUID_of_uid, reduceCtorEq] at h

theorem mapOrErr_value_asEntityUID_on_uids_produces_set (list : List EntityUID) (err : Error) :
  Set.mapOrErr Value.asEntityUID (Set.make (list.map (Value.prim ∘ Prim.entityUID))) err =
  .ok (Set.make list)
:= by
  unfold Set.mapOrErr
  split <;> simp
  case h_1 list' h =>
    -- in this case, mapping Value.asEntityUID over the set returns .ok
    rw [← List.mapM'_eq_mapM] at h
    replace h := mapM'_asEntityUID_eq_entities h
    have ⟨h₁, h₂⟩ := Set.elts_make_is_id_then_equiv h; clear h
    rw [Set.make_make_eqv]
    unfold List.Equiv at *
    repeat rw [List.subset_def] at *
    constructor <;> intro a h₃ <;>
    replace h₃ := @List.mem_map_of_mem _ _ _ _ (Value.prim ∘ Prim.entityUID) h₃
    · specialize h₁ h₃
      simp at h₁
      exact h₁
    · specialize h₂ h₃
      simp at h₂
      exact h₂
  case h_2 err h =>
    -- in this case, mapping Value.asEntityUID over the set returns .error
    have h₁ := mapM_asEntityUID_on_set_uids_produces_ok list
    simp [h, Except.isOk, Except.toBool] at h₁

theorem action_in_set_of_euids_produces_boolean (list : List EntityUID) (request : Request) (entities : Entities) :
  producesBool
    (Expr.binaryApp
      BinaryOp.mem
      (Expr.var .action)
      (Expr.set (list.map fun uid => Expr.lit (.entityUID uid))))
    request
    entities
:= by
  unfold producesBool
  split <;> simp
  case h_2 _ h =>
    simp only [evaluate, apply₂, inₛ, bind_assoc, Except.bind_ok, imp_false, Bool.forall_bool] at h
    rw [List.mapM₁_eq_mapM (evaluate · request entities)] at h
    simp only [mapM_evaluate_uids_produces_uids] at h
    simp [mapOrErr_value_asEntityUID_on_uids_produces_set] at h

/--
  Lemma: evaluating the principalScope of any policy produces a boolean (and does not error)
-/
theorem principal_scope_produces_boolean (policy : Policy) (request : Request) (entities : Entities) :
  producesBool policy.principalScope.toExpr request entities
:= by
  simp [producesBool, evaluate, PrincipalScope.toExpr, Scope.toExpr]
  cases policy.principalScope.1 <;>
  simp [evaluate, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType, apply₁, apply₂]
  case isMem ety uid =>
    simp only [Result.as, Coe.coe, Value.asBool, pure, Except.pure, Except.bind_ok,
      beq_eq_false_iff_ne, ne_eq, ite_not]
    generalize (inₑ request.principal uid entities) = b₁
    generalize (ety == request.principal.ty) = b₂
    split <;> rename_i h
    · trivial
    · split at h <;> simp at h

/--
  Lemma: evaluating the actionScope of any policy produces a boolean (and does not error)
-/
theorem action_scope_produces_boolean (policy : Policy) (request : Request) (entities : Entities) :
  producesBool policy.actionScope.toExpr request entities
:= by
  simp [producesBool, evaluate, ActionScope.toExpr, Scope.toExpr]
  cases policy.actionScope
  case actionInAny list =>
    split
    case h_1 => trivial
    case h_2 res h =>
      simp at h
      have h₁ := action_in_set_of_euids_produces_boolean list request entities
      unfold producesBool at h₁
      split at h₁ <;> rename_i h₂
      · simp [h₂] at h
      · simp at h₁
  case actionScope scope =>
    simp [evaluate, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType, apply₁, apply₂]
    cases scope <;> simp [evaluate, apply₁, apply₂, Result.as]
    case isMem ety uid =>
      simp only [Coe.coe, Value.asBool, pure, Except.pure, Except.bind_ok, beq_eq_false_iff_ne,
        ne_eq, ite_not]
      generalize (inₑ request.action uid entities) = b₁
      generalize (ety == request.action.ty) = b₂
      split <;> rename_i h
      · trivial
      · split at h <;> simp at h

/--
  Lemma: evaluating the resourceScope of any policy produces a boolean (and does not error)
-/
theorem resource_scope_produces_boolean (policy : Policy) (request : Request) (entities : Entities) :
  producesBool policy.resourceScope.toExpr request entities
:= by
  simp [producesBool, evaluate, ResourceScope.toExpr, Scope.toExpr]
  cases policy.resourceScope.1 <;>
  simp [evaluate, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType, apply₁, apply₂]
  case isMem ety uid =>
    simp only [Result.as, Coe.coe, Value.asBool, pure, Except.pure, Except.bind_ok,
      beq_eq_false_iff_ne, ne_eq, ite_not]
    generalize (inₑ request.resource uid entities) = b₁
    generalize (ety == request.resource.ty) = b₂
    split <;> rename_i h
    · trivial
    · split at h <;> simp at h

/--
  Lemma: if something produces a boolean, it does not produce a non-boolean
-/
theorem produces_boolean_means_not_non_boolean {e : Expr} {request : Request} {entities : Entities} :
  producesBool e request entities → ¬ producesNonBool e request entities
:= by
  intro h₁
  by_contra h₂
  unfold producesBool at h₁
  unfold producesNonBool at h₂
  generalize (evaluate e request entities) = res at h₁ h₂
  split at h₁
  · simp at h₂
  · split at h₂ <;> simp at h₁

theorem principal_scope_does_not_throw (policy : Policy) (request : Request) (entities : Entities) (err : Error) :
  ¬ (evaluate policy.principalScope.toExpr request entities = .error err)
:= by
  by_contra h
  have h₁ := principal_scope_produces_boolean policy request entities
  simp [producesBool, h] at h₁

theorem action_scope_does_not_throw (policy : Policy) (request : Request) (entities : Entities) (err : Error) :
  ¬ (evaluate policy.actionScope.toExpr request entities = .error err)
:= by
  by_contra h
  have h₁ := action_scope_produces_boolean policy request entities
  simp [producesBool, h] at h₁

theorem resource_scope_does_not_throw (policy : Policy) (request : Request) (entities : Entities) (err : Error) :
  ¬ (evaluate policy.resourceScope.toExpr request entities = .error err)
:= by
  by_contra h
  have h₁ := resource_scope_produces_boolean policy request entities
  simp [producesBool, h] at h₁

/--
  For a policy to throw an error, we must have at least gotten past the scope,
  so the scope constraints must have been satisfied.
-/
theorem error_implies_scope_satisfied {policy : Policy} {request : Request} {entities : Entities} {err : Error} :
  evaluate policy.toExpr request entities = .error err →
  evaluate policy.principalScope.toExpr request entities = .ok true ∧
  evaluate policy.actionScope.toExpr request entities = .ok true ∧
  evaluate policy.resourceScope.toExpr request entities = .ok true
:= by
  intro h₁
  unfold Policy.toExpr at h₁
  rcases (ways_and_can_error h₁) with h₂ | ⟨h₂, h₃⟩ | ⟨_, h₃⟩ | ⟨h₂, _, h₄⟩ <;> clear h₁
  case _ =>
    -- in this case, evaluating principal produced the error
    exfalso; simp only [principal_scope_does_not_throw] at h₂
  case _ =>
    -- in this case, evaluating (action ∧ resource ∧ condition) produced the error
    rcases (ways_and_can_error h₃) with h₄ | ⟨h₄, h₅⟩ | ⟨_, h₅⟩ | ⟨_, _, h₅⟩ <;> clear h₃
    case _ =>
      -- in this case, evaluating action produced the error
      exfalso; simp only [action_scope_does_not_throw] at h₄
    case _ =>
      -- in this case, evaluating (resource ∧ condition) produced the error
      rcases (ways_and_can_error h₅) with h₆ | ⟨h₆, _⟩ | ⟨_, h₇⟩ | ⟨_, h₇, _⟩ <;> clear h₅
      case _ =>
        -- in this case, evaluating resource produced the error
        exfalso; simp only [resource_scope_does_not_throw] at h₆
      case _ =>
        -- in this case, evaluating condition produced the error
        exact And.intro h₂ (And.intro h₄ h₆)
      case _ =>
        -- in this case, evaluating resource produced a non-boolean
        exfalso
        clear h₂
        have h := resource_scope_produces_boolean policy request entities
        apply produces_boolean_means_not_non_boolean (e := policy.resourceScope.toExpr) h h₇
      case _ =>
        -- in this case, evaluating condition produced a non-boolean
        exact And.intro h₂ (And.intro h₄ h₇)
    case _ =>
      -- in this case, evaluating action produced a non-boolean
      exfalso
      have h := action_scope_produces_boolean policy request entities
      apply produces_boolean_means_not_non_boolean (e := policy.actionScope.toExpr) h h₅
    case _ =>
      -- in this case, evaluating (resource ∧ condition) produced a non-boolean
      exfalso
      clear h₂
      unfold producesNonBool at h₅
      have h₄ := and_produces_bool_or_error policy.resourceScope.toExpr policy.condition.toExpr request entities
      split at h₄ <;> simp at h₄
      case _ h₆ => simp [h₆] at h₅
      case _ h₆ => simp [h₆] at h₅
  case _ =>
    -- in this case, evaluating principal produced a non-boolean
    exfalso
    have h := principal_scope_produces_boolean policy request entities
    apply produces_boolean_means_not_non_boolean (e := policy.principalScope.toExpr) h h₃
  case _ =>
    -- in this case, evaluating (action ∧ resource ∧ condition) produced a non-boolean
    exfalso
    unfold producesNonBool at h₄
    generalize (Expr.and policy.resourceScope.toExpr policy.condition.toExpr) = resource_and_condition at h₂ h₄
    have h₅ := and_produces_bool_or_error policy.actionScope.toExpr resource_and_condition request entities
    split at h₅ <;> simp at h₅
    case _ h₆ => simp [h₆] at h₄
    case _ h₆ => simp [h₆] at h₄

/--
  For a policy to throw an error, we must have at least gotten past the scope,
  so the scope constraints must have been satisfied.
-/
theorem error_implies_principal_scope_in {policy : Policy} {request : Request} {entities : Entities} {uid : EntityUID} {err : Error} :
  evaluate policy.toExpr request entities = .error err →
  policy.principalScope.scope.bound = .some uid →
  inₑ request.principal uid entities = true
:= by
  intro h₁ h₂
  have ⟨hₚ, _, _⟩ := error_implies_scope_satisfied h₁
  exact principal_eval_ok_means_principal_in_uid hₚ h₂

/--
  For a policy to throw an error, we must have at least gotten past the scope,
  so the scope constraints must have been satisfied.
-/
theorem error_implies_resource_scope_in {policy : Policy} {request : Request} {entities : Entities} {uid : EntityUID} {err : Error} :
  evaluate policy.toExpr request entities = .error err →
  policy.resourceScope.scope.bound = .some uid →
  inₑ request.resource uid entities = true
:= by
  intro h₁ h₂
  have ⟨_, _, hᵣ⟩ := error_implies_scope_satisfied h₁
  exact resource_eval_ok_means_resource_in_uid hᵣ h₂


end Cedar.Thm
