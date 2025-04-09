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

import Cedar.Thm.Validation.Typechecker.And
import Cedar.Thm.Validation.Typechecker.BinaryApp
import Cedar.Thm.Validation.Typechecker.Call
import Cedar.Thm.Validation.Typechecker.GetAttr
import Cedar.Thm.Validation.Typechecker.HasAttr
import Cedar.Thm.Validation.Typechecker.IfThenElse
import Cedar.Thm.Validation.Typechecker.LitVar
import Cedar.Thm.Validation.Typechecker.Record
import Cedar.Thm.Validation.Typechecker.Set
import Cedar.Thm.Validation.Typechecker.Or
import Cedar.Thm.Validation.Typechecker.UnaryApp

/-!
This file contains useful definitions and lemmas about the `Typechecker` functions.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
If an expression is well-typed according to the typechecker, and the input
environment and capabilities satisfy some invariants, then either (1) evaluation
produces a value of the returned type or (2) it returns an error of type
`entityDoesNotExist`, `extensionError`, or `arithBoundsError`. Both options are
encoded in the `EvaluatesTo` predicate.
-/
theorem type_of_is_sound {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  GuardedCapabilitiesInvariant e c₂ request entities ∧
  ∃ (v : Value), EvaluatesTo e request entities v ∧ InstanceOfType v ty.typeOf
:= by
  intro h₁ h₂ h₃
  match e with
  | .lit l => exact type_of_lit_is_sound h₃
  | .var var => exact type_of_var_is_sound h₂ h₃
  | .ite x₁ x₂ x₃ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    have ih₃ := @type_of_is_sound x₃
    exact type_of_ite_is_sound h₁ h₂ h₃ ih₁ ih₂ ih₃
  | .and x₁ x₂ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    exact type_of_and_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .or x₁ x₂ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    exact type_of_or_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .unaryApp op₁ x₁ =>
    have ih := @type_of_is_sound x₁
    exact type_of_unaryApp_is_sound h₁ h₂ h₃ ih
  | .binaryApp op₂ x₁ x₂ =>
    have ih₁ := @type_of_is_sound x₁
    have ih₂ := @type_of_is_sound x₂
    exact type_of_binaryApp_is_sound h₁ h₂ h₃ ih₁ ih₂
  | .hasAttr x₁ a =>
    have ih := @type_of_is_sound x₁
    exact type_of_hasAttr_is_sound h₁ h₂ h₃ ih
  | .getAttr x₁ a =>
    have ih := @type_of_is_sound x₁
    exact type_of_getAttr_is_sound h₁ h₂ h₃ ih
  | .set xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → TypeOfIsSound xᵢ := by
      intro xᵢ _
      exact @type_of_is_sound xᵢ
    exact type_of_set_is_sound h₁ h₂ h₃ ih
  | .record axs =>
    have ih : ∀ axᵢ, axᵢ ∈ axs → TypeOfIsSound axᵢ.snd := by
      intro axᵢ hᵢ
      have _ : sizeOf axᵢ.snd < 1 + sizeOf axs := by
        apply List.sizeOf_snd_lt_sizeOf_list hᵢ
      exact @type_of_is_sound axᵢ.snd
    exact type_of_record_is_sound h₁ h₂ h₃ ih
  | .call xfn xs =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → TypeOfIsSound xᵢ := by
      intro xᵢ _
      exact @type_of_is_sound xᵢ
    exact type_of_call_is_sound h₁ h₂ h₃ ih
termination_by sizeOf e

theorem type_of_preserves_evaluation_results {e : Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities} :
  CapabilitiesInvariant c₁ request entities →
  RequestAndEntitiesMatchEnvironment env request entities →
  typeOf e c₁ env = .ok (ty, c₂) →
  evaluate e request entities = evaluate ty.toExpr request entities
:= by
  intro h₁ h₂ h₃
  induction e, c₁, env using typeOf.induct generalizing ty c₂
  case _ =>
    simp [typeOf, typeOfLit, ok] at h₃
    split at h₃ <;>
    try (
      simp at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      simp only [TypedExpr.toExpr]
    )
    split at h₃ <;> simp [err] at h₃
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    simp only [TypedExpr.toExpr]
  case _ =>
    simp [typeOf, typeOfVar, ok] at h₃
    split at h₃ <;>
    (
      simp at h₃
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      simp only [TypedExpr.toExpr]
    )
  case _ c₁ env x₁ x₂ x₃ hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [typeOf] at h₃
    generalize hᵢ : typeOf x₁ c₁ env = res₁
    cases res₁
    case ok ty =>
      simp [hᵢ] at h₃
      simp [typeOfIf, ok] at h₃
      specialize hᵢ₁ h₁ h₂ hᵢ
      split at h₃
      case _ heq =>
        simp [do_ok] at h₃
        rcases h₃ with ⟨_, _, h₃₁, h₃₂, h₃₃⟩
        subst h₃₂
        simp [evaluate, TypedExpr.toExpr]
        sorry
      case _ heq =>
        sorry
      case _ heq => sorry
      case _ => simp [err] at h₃
    case error =>
      simp [hᵢ] at h₃
  case _ hᵢ₁ hᵢ₂ =>
    simp [typeOf, do_ok'] at h₃
    rcases h₃ with ⟨_, _, h₃₁, h₃₂⟩
    simp [typeOfAnd] at h₃₂
    split at h₃₂ <;> simp [ok, err] at h₃₂
    case _ heq =>
      rcases h₃₂ with ⟨h₃₂, _⟩
      subst h₃₂
      sorry
    simp [do_ok'] at h₃₂
    rcases h₃₂ with ⟨_, _, _, h₃₂⟩
    --split at h₃₂ <;> simp [err] at h₃₂
    sorry
  case _ =>
    simp [typeOf, do_ok'] at h₃
    rcases h₃ with ⟨_, _, h₃₁, h₃₂⟩
    simp [typeOfOr] at h₃₂
    split at h₃₂ <;> simp [ok, err] at h₃₂
    case _ heq =>
      rcases h₃₂ with ⟨h₃₂, _⟩
      subst h₃₂
      sorry
    sorry
    sorry
  case _ hᵢ =>
    simp [typeOf, do_ok'] at h₃
    rcases h₃ with ⟨_, ⟨_, h₃₁⟩, h₃₂⟩
    simp [typeOfUnaryApp] at h₃₂
    specialize hᵢ h₁ h₂ h₃₁
    split at h₃₂ <;>
    simp [ok, err] at h₃₂ <;>
    try (
      rcases h₃₂ with ⟨h₃₂, _⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
    )
  case _ hᵢ₁ hᵢ₂ =>
    simp [typeOf, do_ok'] at h₃
    rcases h₃ with ⟨_, ⟨_, h₃₁⟩, _, ⟨_, h₃₂⟩, h₃₃⟩
    specialize hᵢ₁ h₁ h₂ h₃₁
    specialize hᵢ₂ h₁ h₂ h₃₂
    simp [typeOfBinaryApp] at h₃₃
    split at h₃₃ <;> try simp [ok, err] at h₃₃
    case _ =>
      simp [typeOfEq] at h₃₃
      split at h₃₃ <;>
      split at h₃₃ <;>
      try (
        simp [ok] at h₃₃
        rcases h₃₃ with ⟨h₃₃, _⟩
        subst h₃₃
        try simp [evaluate] at hᵢ₁
        try simp [evaluate] at hᵢ₂
        simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
      )
      split at h₃₃ <;> simp [ok, err] at h₃₃
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      simp [do_ok] at h₃₃
      rcases h₃₃ with ⟨_, h₃₃₁, h₃₃₂⟩
      subst h₃₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      simp [do_ok] at h₃₃
      rcases h₃₃ with ⟨_, h₃₃₁, h₃₃₂⟩
      subst h₃₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      rcases h₃₃ with ⟨h₃₃, _⟩
      subst h₃₃
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      simp [do_ok] at h₃₃
      rcases h₃₃ with ⟨_, h₃₃₁, h₃₃₂⟩
      subst h₃₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      simp [do_ok] at h₃₃
      rcases h₃₃ with ⟨_, h₃₃₁, h₃₃₂⟩
      subst h₃₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
    case _ =>
      simp [do_ok] at h₃₃
      rcases h₃₃ with ⟨_, h₃₃₁, h₃₃₂⟩
      subst h₃₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ₁, hᵢ₂]
  case _ hᵢ =>
    simp only [typeOf, do_ok', Prod.exists, exists_and_right] at h₃
    rcases h₃ with ⟨ty, ⟨c, h₃₁⟩, h₃₂⟩
    simp only [typeOfHasAttr, List.empty_eq] at h₃₂
    specialize hᵢ h₁ h₂ h₃₁
    split at h₃₂
    case _ =>
      simp only [ok, do_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
    case _ =>
      split at h₃₂ <;>
      try split at h₃₂
      case _ =>
        simp only [ok, do_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
        rcases h₃₂ with ⟨_, _, h₃₂⟩
        subst h₃₂
        simp only [TypedExpr.toExpr, evaluate, hᵢ]
      case _ =>
        simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₃₂
        rcases h₃₂ with ⟨h₃₂, _⟩
        subst h₃₂
        simp only [TypedExpr.toExpr, evaluate, hᵢ]
      simp only [err, reduceCtorEq] at h₃₂
    simp only [err, reduceCtorEq] at h₃₂
  case _ hᵢ =>
    simp only [typeOf, do_ok', Prod.exists, exists_and_right] at h₃
    rcases h₃ with ⟨ty, ⟨c, h₃₁⟩, h₃₂⟩
    simp only [typeOfGetAttr, List.empty_eq] at h₃₂
    specialize hᵢ h₁ h₂ h₃₁
    split at h₃₂
    case _ =>
      simp only [ok, do_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
    case _ =>
      split at h₃₂
      simp only [ok, do_ok, Prod.mk.injEq, Prod.exists, exists_eq_right_right] at h₃₂
      rcases h₃₂ with ⟨_, _, h₃₂⟩
      subst h₃₂
      simp only [TypedExpr.toExpr, evaluate, hᵢ]
      simp only [err, reduceCtorEq] at h₃₂
    simp only [err, reduceCtorEq] at h₃₂
  case _ c₁ env _ hᵢ =>
    simp only [typeOf, do_ok', Prod.exists, exists_and_right] at h₃
    rcases h₃ with ⟨ty, h₃₁, h₃₂⟩
    simp [List.mapM₁_eq_mapM (fun x => justType (typeOf x c₁ env)), List.mapM_ok_iff_forall₂] at h₃₁
    simp [typeOfSet] at h₃₂
    split at h₃₂ <;> simp [err] at h₃₂
    split at h₃₂ <;> simp [ok] at h₃₂
    rcases h₃₂ with ⟨h₃₂, _⟩
    subst h₃₂
    simp only [TypedExpr.toExpr, evaluate, List.map₁_eq_map, List.mapM₁_eq_mapM (fun x => evaluate x request entities), List.mapM_map]
    sorry
  case _ c₁ env axs hᵢ =>
    simp [typeOf, do_ok'] at h₃
    rcases h₃ with ⟨_, h₃₁, h₃₂⟩
    simp [ok] at h₃₂
    rcases h₃₂ with ⟨h₃₂, _⟩
    subst h₃₂
    simp [evaluate, TypedExpr.toExpr]
    sorry
  case _ c₁ env xfn xs hᵢ =>
    simp [typeOf, do_ok'] at h₃
    rcases h₃ with ⟨_, h₃₁, h₃₂⟩
    simp [List.mapM₁_eq_mapM fun x => justType (typeOf x c₁ env)] at h₃₁
    --simp [typeOfCall] at h₃₂
    sorry
