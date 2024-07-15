/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Data
import Cedar.Validation
import Cedar.Thm.Validation.Typechecker
import Cedar.Thm.Data

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/-- For a single expression, evaluates to a boolean value (or appropriate error) -/
def OneEvaluatesCorrectly (expr : Expr) (request : Request) (entities : Entities) : Prop :=
  ∃ (b : Bool), EvaluatesTo expr request entities b

/-- Every policy as an expression evaluates to a boolean value or appropriate error -/
def AllEvaluateCorrectly (policies : Policies) (request : Request) (entities : Entities) : Prop :=
  ∀ policy ∈ policies, OneEvaluatesCorrectly policy.toExpr request entities

def RequestAndEntitiesMatchSchema (schema : Schema) (request : Request) (entities : Entities) :Prop :=
  ∀ env ∈ schema.toEnvironments,
  RequestAndEntitiesMatchEnvironment env request entities

def EvaluatesSubst (expr : Expr) (request : Request) (entities : Entities) : Prop :=
  evaluate (substituteAction request.action expr) request entities = evaluate expr request entities

theorem evaluates_subst_ite {i t e : Expr} {request : Request} {entities : Entities}
  (ih₁ : EvaluatesSubst i request entities)
  (ih₂ : EvaluatesSubst t request entities)
  (ih₃ : EvaluatesSubst e request entities) :
  evaluate (substituteAction request.action (Expr.ite i t e)) request entities =
  evaluate (Expr.ite i t e) request entities
:= by
  simp only [EvaluatesSubst, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂, ih₃]

theorem evaluates_subst_getAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst e request entities) :
  evaluate (substituteAction request.action (Expr.getAttr e attr)) request entities =
  evaluate (Expr.getAttr e attr) request entities
:= by
  simp only [EvaluatesSubst] at ih₁
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem evaluates_subst_hasAttr {e : Expr} {attr : Attr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst e request entities) :
  evaluate (substituteAction request.action (Expr.hasAttr e attr)) request entities =
  evaluate (Expr.hasAttr e attr) request entities
:= by
  simp only [EvaluatesSubst] at ih₁
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem evaluates_subst_unaryApp {op : UnaryOp} {e : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst e request entities) :
  evaluate (substituteAction request.action (Expr.unaryApp op e)) request entities =
  evaluate (Expr.unaryApp op e) request entities
:= by
  simp only [EvaluatesSubst] at ih₁
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁]

theorem evaluates_subst_binaryApp {op : BinaryOp} {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst a request entities)
(ih₂ : EvaluatesSubst b request entities) :
  evaluate (substituteAction request.action (Expr.binaryApp op a b)) request entities =
  evaluate (Expr.binaryApp op a b) request entities
:= by
  simp only [EvaluatesSubst] at *
  simp only [substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem evaluates_subst_and {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst a request entities)
(ih₂ : EvaluatesSubst b request entities) :
  evaluate (substituteAction request.action (Expr.and a b)) request entities =
  evaluate (Expr.and a b) request entities
:= by
  simp only [EvaluatesSubst, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem evaluates_subst_or {a b : Expr} {request : Request} {entities : Entities}
(ih₁ : EvaluatesSubst a request entities)
(ih₂ : EvaluatesSubst b request entities) :
  evaluate (substituteAction request.action (Expr.or a b)) request entities =
  evaluate (Expr.or a b) request entities
:= by
  simp only [EvaluatesSubst, substituteAction, mapOnVars] at *
  simp only [evaluate, ih₁, ih₂]

theorem substitute_action_nil_set : ∀ (uid : EntityUID),
  substituteAction uid (.set []) = .set []
:= by
  intro uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.pmap, List.map_nil]

theorem substitute_action_cons_set : ∀ (h : Expr) (t : List Expr) (uid : EntityUID),
  substituteAction uid (.set (h :: t)) = .set ((substituteAction uid h) :: t.map (substituteAction uid))
:= by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.map_pmap_subtype, List.map_cons]
  simp only [Expr.set.injEq, List.cons.injEq, true_and]
  unfold substituteAction
  simp only

theorem evaluates_subst_set {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities) :
  evaluate (substituteAction request.action (Expr.set xs)) request entities =
  evaluate (Expr.set xs) request entities
:= by
  cases h₀ : xs with
  | nil =>
    rw [substitute_action_nil_set]
  | cons h t =>
    simp only [EvaluatesSubst] at ih₁
    have h₁ := ih₁ h
    simp only [h₀, List.mem_cons, true_or, true_implies] at h₁
    rw [substitute_action_cons_set]
    simp only [mapOnVars, evaluate, List.mapM₁, List.attach_def, List.mapM_pmap_subtype (fun x => evaluate x request entities)]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    rw [h₁]
    simp [List.mapM_map]
    have h₂ : ∀ (x₁ : Expr), x₁ ∈ t → EvaluatesSubst x₁ request entities :=
    by
      simp [h₀] at ih₁
      obtain ⟨_, h₂⟩ := ih₁
      exact h₂
    simp [List.mapM_congr h₂]

theorem substitute_action_nil_record : ∀ (uid : EntityUID),
  substituteAction uid (.record []) = .record []
:= by
  intro uid
  simp only [substituteAction, mapOnVars, List.attach₂, List.pmap, List.map_nil]

theorem substitute_action_cons_record : ∀ (ax : Attr × Expr) (axs : List (Attr × Expr)) (uid : EntityUID),
  substituteAction uid (.record (ax :: axs)) =
  .record ((ax.fst, substituteAction uid ax.snd) :: axs.map (fun (a, e) => (a, substituteAction uid e)))
:= by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.attach₂, List.map_pmap_subtype_snd, List.map_cons]

theorem evaluates_subst_record {axs : List (Attr × Expr)} {request : Request} {entities : Entities}
(ih₁ : ∀ axᵢ, axᵢ ∈ axs → EvaluatesSubst axᵢ.snd request entities) :
  evaluate (substituteAction request.action (Expr.record axs)) request entities =
  evaluate (Expr.record axs) request entities
:= by
  cases h₀ : axs with
  | nil =>
    rw [substitute_action_nil_record]
  | cons h t =>
    simp only [EvaluatesSubst] at ih₁
    have h₁ := ih₁ h
    simp only [h₀, List.mem_cons, true_or, true_implies] at h₁
    rw [substitute_action_cons_record]
    simp only [mapOnVars, evaluate, List.mapM₂, List.attach₂, List.mapM_pmap_subtype (fun (a, e) => bindAttr a (evaluate e request entities))]
    simp only [bindAttr]
    simp only [List.mapM_cons, bind_assoc, Except.bind_ok, pure_bind]
    rw [h₁]
    simp only [List.mapM_map]
    have h₂ : ∀ x ∈ t,
    (do
      let v ← evaluate (substituteAction request.action x.snd) request entities
      Except.ok (x.fst, v)) =
    (do
      let v ← evaluate x.snd request entities
      Except.ok (x.fst, v))
    := by
      intro x xin
      simp [h₀] at ih₁
      obtain ⟨_, h₂⟩ := ih₁
      simp [h₂ x xin]
    rw [List.mapM_congr h₂]

theorem substitute_action_nil_call : ∀ (uid : EntityUID) (xfn : ExtFun),
  substituteAction uid (.call xfn []) = .call xfn [] :=
by
  intro uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.pmap, List.map_nil, implies_true]


theorem substitute_action_cons_call : ∀ (x : Expr) (xs : List Expr) (uid : EntityUID) (xfn : ExtFun),
  substituteAction uid (.call xfn (x :: xs)) = .call xfn ((substituteAction uid x) :: xs.map (substituteAction uid)) :=
by
  intro h t uid
  simp only [substituteAction, mapOnVars, List.attach_def, List.map_pmap_subtype, List.map_cons]
  simp only [Expr.call.injEq, List.cons.injEq, true_and, forall_const]
  unfold substituteAction
  simp only


theorem evaluates_subst_call {xfn : ExtFun} {xs : List Expr} {request : Request} {entities : Entities}
(ih₁ : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities) :
  evaluate (substituteAction request.action (Expr.call xfn xs)) request entities =
  evaluate (Expr.call xfn xs) request entities
:= by
  cases h₀ : xs with
  | nil =>
    rw [substitute_action_nil_call]
  | cons h t =>
    simp only [EvaluatesSubst] at ih₁
    have h₁ := ih₁ h
    simp only [h₀, List.mem_cons, true_or, true_implies] at h₁
    rw [substitute_action_cons_call]
    simp only [mapOnVars, evaluate, List.mapM₁, List.attach_def, List.mapM_pmap_subtype (fun x => evaluate x request entities)]
    simp only [List.mapM_cons, bind_assoc, pure_bind]
    rw [h₁]
    simp [List.mapM_map]
    have h₂ : ∀ (x₁ : Expr), x₁ ∈ t → EvaluatesSubst x₁ request entities :=
    by
      simp [h₀] at ih₁
      obtain ⟨_, h₂⟩ := ih₁
      exact h₂
    rw [List.mapM_congr h₂]

theorem evaluates_subst (expr : Expr) (request : Request) (entities : Entities) :
  evaluate (substituteAction request.action expr) request entities =
  evaluate expr request entities
:= by
  cases h₀ : expr with
  | lit p => simp only [substituteAction, mapOnVars]
  | var vr =>
    cases vr <;> simp only [substituteAction, mapOnVars] <;> try assumption
    case action =>
      simp [evaluate]
  | ite i t e =>
    have ih₁ := evaluates_subst i request entities
    have ih₂ := evaluates_subst t request entities
    have ih₃ := evaluates_subst e request entities
    exact @evaluates_subst_ite i t e request entities ih₁ ih₂ ih₃
  | and a b =>
    have ih₁ := evaluates_subst a request entities
    have ih₂ := evaluates_subst b request entities
    exact @evaluates_subst_and a b request entities ih₁ ih₂
  | or a b =>
    have ih₁ := evaluates_subst a request entities
    have ih₂ := evaluates_subst b request entities
    exact @evaluates_subst_or a b request entities ih₁ ih₂
  | unaryApp op e =>
    have ih₁ := evaluates_subst e request entities
    exact @evaluates_subst_unaryApp op e request entities ih₁
  | binaryApp op a b =>
    have ih₁ := evaluates_subst a request entities
    have ih₂:= evaluates_subst b request entities
    exact @evaluates_subst_binaryApp op a b request entities ih₁ ih₂
  | getAttr x attr =>
    have ih₁ := evaluates_subst x request entities
    exact @evaluates_subst_getAttr x attr request entities ih₁
  | hasAttr x attr =>
    have ih₁ := evaluates_subst x request entities
    exact @evaluates_subst_hasAttr x attr request entities ih₁
  | set xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities := by
      intro xᵢ _
      exact @evaluates_subst xᵢ request entities
    exact @evaluates_subst_set xs request entities ih
  | record axs =>
    have ih : ∀ axᵢ, axᵢ ∈ axs → EvaluatesSubst axᵢ.snd request entities := by
      intro axᵢ hᵢ
      have _ : sizeOf axᵢ.snd < 1 + sizeOf axs := by
        apply List.sizeOf_snd_lt_sizeOf_list hᵢ
      exact @evaluates_subst axᵢ.snd request entities
    exact @evaluates_subst_record axs request entities ih
  | call xfn xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → EvaluatesSubst xᵢ request entities := by
      intro xᵢ _
      exact @evaluates_subst xᵢ request entities
    exact @evaluates_subst_call xfn xs request entities ih

theorem action_matches_env (env : Environment) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchEnvironment env request entities →
  request.action = env.reqty.action
:= by
  intro h₀
  simp only [RequestAndEntitiesMatchEnvironment, InstanceOfRequestType] at h₀
  obtain ⟨ ⟨ _, h₁, _, _ ⟩ , _ , _⟩ := h₀
  exact h₁

theorem typecheck_policy_is_sound (policy : Policy) (env : Environment) (ty : CedarType) (request : Request) (entities : Entities) :
  RequestAndEntitiesMatchEnvironment env request entities →
  typecheckPolicy policy env = .ok ty →
  ∃ b : Bool, EvaluatesTo policy.toExpr request entities b
:= by
  intro h₁ h₂
  simp only [typecheckPolicy] at h₂
  cases h₃ : typeOf (substituteAction env.reqty.action policy.toExpr) [] env <;>
  simp only [List.empty_eq, h₃] at h₂
  split at h₂ <;> simp only [Except.ok.injEq] at h₂
  rename_i cp ht
  have hc := empty_capabilities_invariant request entities
  have ⟨_, v, h₄, h₅⟩ := type_of_is_sound hc h₁ h₃
  have ⟨b, h₆⟩ := instance_of_type_bool_is_bool v cp.fst h₅ ht
  subst h₆
  exists b
  simp only [EvaluatesTo] at *
  cases h₄ with
  | inl h₁ =>
    left
    rw [← evaluates_subst policy.toExpr request entities]
    rw [action_matches_env]
    repeat assumption
  | inr h₁ => cases h₁ with
    | inl h₂ =>
      right
      left
      rw [← evaluates_subst policy.toExpr request entities]
      rw [action_matches_env]
      repeat assumption
    | inr h₂ => cases h₂ with
      | inl h₃ =>
        right
        right
        left
        rw [← evaluates_subst policy.toExpr request entities]
        rw [action_matches_env]
        repeat assumption
      | inr h₃ =>
        right
        right
        right
        rw [← evaluates_subst policy.toExpr request entities]
        rw [action_matches_env]
        repeat assumption

theorem typecheck_policy_with_environments_is_sound (policy : Policy) (envs : List Environment) (request : Request) (entities : Entities) :
  (∀ env ∈ envs, RequestAndEntitiesMatchEnvironment env request entities) →
  typecheckPolicyWithEnvironments policy envs = .ok () →
  ∃ b : Bool, EvaluatesTo policy.toExpr request entities b
:= by
  intro h₀ h₂
  simp only [typecheckPolicyWithEnvironments] at h₂
  cases h₃ : List.mapM (typecheckPolicy policy) envs with
  | error => simp only [h₃, Except.bind_err] at h₂
  | ok ts =>
    simp only [h₃, Except.bind_ok, ite_eq_right_iff, imp_false, Bool.not_eq_true] at h₂
    cases h₄ : envs with
    | nil =>
      simp only [h₄, List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h₃
      subst h₃
      simp only [allFalse, List.all_nil, Bool.true_eq_false] at h₂
    | cons h t =>
        rw [List.mapM_ok_iff_forall₂] at h₃
        have h₆ : RequestAndEntitiesMatchEnvironment h request entities := by
          have h₇ : h ∈ envs := by simp only [h₄, List.mem_cons, true_or]
          specialize h₀ h
          apply h₀ h₇
        subst h₄
        rw [List.forall₂_cons_left_iff] at h₃
        simp only [exists_and_left] at h₃
        obtain ⟨ b, _, _, _, _ ⟩ := h₃
        apply typecheck_policy_is_sound policy h b
        repeat assumption

end Cedar.Thm
