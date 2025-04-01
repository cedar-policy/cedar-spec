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
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.TPE.Input
import Cedar.Thm

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem as_value_some {r : Residual} {v : Value} :
  r.asValue = .some v → (∃ ty, r = .val v ty)
:= by
  intro h
  simp only [Residual.asValue] at h
  split at h <;> simp at h
  subst h
  simp only [Residual.val.injEq, true_and, exists_eq']

theorem partial_evaluate_value_binary_app
  {x₁ x₂ : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment}
  {v : Value}
  {op₂ : BinaryOp}
  {ty ty₁: CedarType}
  (h₀ : RequestAndEntitiesMatchEnvironment env req₁ es₁)
  (h₂ : IsConsistent req₁ es₁ req₂ es₂)
  (hᵢ₁ : TypedExpr.WellTyped env x₁)
  (hᵢ₂ : TypedExpr.WellTyped env x₂)
  (hᵢ₃ : BinaryOp.WellTyped env op₂ x₁ x₂ ty₁)
  (hᵢ₄ : ∀ {v : Value} {ty : CedarType},
    TPE.evaluate x₁ req₂ es₂ = Residual.val v ty → Spec.evaluate x₁.toExpr req₁ es₁ = Except.ok v)
  (hᵢ₅ : ∀ {v : Value} {ty : CedarType},
  TPE.evaluate x₂ req₂ es₂ = Residual.val v ty → Spec.evaluate x₂.toExpr req₁ es₁ = Except.ok v)
  (h₃ : TPE.apply₂ op₂ (TPE.evaluate x₁ req₂ es₂) (TPE.evaluate x₂ req₂ es₂) es₂ ty₁ = Residual.val v ty) :
  Spec.evaluate (Expr.binaryApp op₂ x₁.toExpr x₂.toExpr) req₁ es₁ = Except.ok v
:= by
  generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
  generalize h₂ᵢ : TPE.evaluate x₂ req₂ es₂ = res₂
  simp [h₁ᵢ, h₂ᵢ] at h₃
  unfold TPE.apply₂ at h₃
  split at h₃
  case _ heq₁ heq₂ =>
    split at h₃ <;> try simp at h₃
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂, intOrErr]
      simp [someOrError, Option.bind] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      split at heq₃ <;> simp at heq₃
      rename_i heq₄
      simp [heq₄]
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact heq₃
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂, intOrErr]
      simp [someOrError, Option.bind] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      split at heq₃ <;> simp at heq₃
      rename_i heq₄
      simp [heq₄]
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact heq₃
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂, intOrErr]
      simp [someOrError, Option.bind] at h₃
      split at h₃ <;> simp at h₃
      rename_i heq₃
      split at heq₃ <;> simp at heq₃
      rename_i heq₄
      simp [heq₄]
      rcases h₃ with ⟨h₃, _⟩
      subst h₃
      exact heq₃
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      replace ⟨_, heq₁⟩ := as_value_some heq₁
      replace ⟨_, heq₂⟩ := as_value_some heq₂
      rw [heq₁] at h₁ᵢ
      rw [heq₂] at h₂ᵢ
      specialize hᵢ₄ h₁ᵢ
      specialize hᵢ₅ h₂ᵢ
      simp [Spec.evaluate, hᵢ₄, hᵢ₅, Spec.apply₂]
      exact h₃.left
    case _ =>
      sorry
    case _ =>
      sorry
    case _ =>
      sorry
    case _ =>
      sorry
  case _ => sorry

theorem partial_evaluate_value
  {x : TypedExpr}
  {req₁ : Request}
  {es₁ : Entities}
  {req₂ : PartialRequest}
  {es₂ : PartialEntities}
  {env : Environment}
  {v : Value}
  {op₂ : BinaryOp}
  {ty : CedarType} :
  RequestAndEntitiesMatchEnvironment env req₁ es₁ →
  TypedExpr.WellTyped env x →
  IsConsistent req₁ es₁ req₂ es₂ →
  TPE.evaluate x req₂ es₂ = .val v ty →
  Spec.evaluate x.toExpr req₁ es₁ = .ok v
:= by
  intro h₀ h₁ h₂ h₃
  induction h₁ generalizing v ty <;>
    simp [TypedExpr.toExpr] <;>
    simp [TPE.evaluate] at h₃
  case lit hᵢ₁ =>
    simp [Spec.evaluate]
    exact h₃.left
  case var hᵢ₁ =>
    cases hᵢ₁ <;>
    simp [Spec.evaluate] <;>
    simp [varₚ, varₚ.varₒ, someOrSelf, Option.bind] at h₃
    case action =>
      simp [IsConsistent, RequestIsConsistent] at h₂
      rcases h₂ with ⟨⟨_, h₂, _⟩, _⟩
      rw [h₂]
      exact h₃.left
    case principal =>
      split at h₃ <;>
      rename_i heq <;>
      split at heq <;>
      simp at heq <;>
      simp at h₃
      case _ heq₁ =>
        rcases h₃ with ⟨h₃, _⟩
        simp [IsConsistent, RequestIsConsistent] at h₂
        rcases h₂ with ⟨⟨h₂, _⟩, _⟩
        simp [heq₁] at h₂
        cases h₂
        rename_i heq₃
        simp [heq₃] at heq
        subst h₃
        exact heq
    case resource =>
      split at h₃ <;>
      rename_i heq <;>
      split at heq <;>
      simp at heq <;>
      simp at h₃
      case _ heq₁ =>
        rcases h₃ with ⟨h₃, _⟩
        simp [IsConsistent, RequestIsConsistent] at h₂
        rcases h₂ with ⟨⟨_, _, h₂, _⟩, _⟩
        simp [heq₁] at h₂
        cases h₂
        rename_i heq₃
        simp [heq₃] at heq
        subst h₃
        exact heq
    case context =>
      split at h₃ <;>
      simp at h₃
      case _ heq =>
        simp only [Option.map_eq_some'] at heq
        rcases heq with ⟨_, heq₁, heq₂⟩
        rcases h₃ with ⟨h₃, _⟩
        subst h₃
        simp [IsConsistent, RequestIsConsistent] at h₂
        rcases h₂ with ⟨⟨_, _, _, h₂⟩, _⟩
        simp [heq₁] at h₂
        cases h₂
        rename_i heq₃
        simp [heq₃] at heq₂
        exact heq₂
  case ite x₁ x₂ x₃ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ hᵢ₇ hᵢ₈ =>
    simp [TPE.ite] at h₃
    generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
    split at h₃ <;> try simp at h₃
    rename_i b _ heq
    cases b <;> simp at h₃ <;> simp [Spec.evaluate, hᵢ₆ heq, Result.as, Coe.coe, Value.asBool]
    · exact hᵢ₈ h₃
    · exact hᵢ₇ h₃
  case and x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    simp [TPE.and] at h₃
    generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
    split at h₃ <;> try simp at h₃
    case _ heq =>
      specialize hᵢ₅ heq
      specialize hᵢ₆ h₃
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool, hᵢ₆]
      replace hᵢ₆ := well_typed_is_sound h₀ hᵢ₂ hᵢ₆
      simp [hᵢ₄] at hᵢ₆
      rcases instance_of_anyBool_is_bool hᵢ₆ with ⟨b, hᵢ₆⟩
      simp only [hᵢ₆, Except.map_ok]
    case _ heq =>
      specialize hᵢ₅ heq
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool]
      exact h₃.left
    case _ heq _ _ _ =>
      specialize hᵢ₅ h₃
      have h₄ := well_typed_is_sound h₀ hᵢ₁ hᵢ₅
      simp [hᵢ₃] at h₄
      rcases instance_of_anyBool_is_bool h₄ with ⟨b, h₄⟩
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, h₄, Value.asBool]
      specialize hᵢ₆ heq
      simp only [hᵢ₆, Except.map_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
        Bool.true_eq, imp_self]
  case or x₁ x₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ hᵢ₆ =>
    simp [TPE.or] at h₃
    generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
    split at h₃ <;> try simp at h₃
    case _ heq =>
      specialize hᵢ₅ heq
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool]
      exact h₃.left
    case _ heq =>
      specialize hᵢ₅ heq
      specialize hᵢ₆ h₃
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, Value.asBool, hᵢ₆]
      replace hᵢ₆ := well_typed_is_sound h₀ hᵢ₂ hᵢ₆
      simp [hᵢ₄] at hᵢ₆
      rcases instance_of_anyBool_is_bool hᵢ₆ with ⟨b, hᵢ₆⟩
      simp only [hᵢ₆, Except.map_ok]
    case _ heq _ _ _ =>
      specialize hᵢ₅ h₃
      have h₄ := well_typed_is_sound h₀ hᵢ₁ hᵢ₅
      simp [hᵢ₃] at h₄
      rcases instance_of_anyBool_is_bool h₄ with ⟨b, h₄⟩
      simp [Spec.evaluate, hᵢ₅, Result.as, Coe.coe, h₄, Value.asBool]
      specialize hᵢ₆ heq
      simp only [hᵢ₆, Except.map_ok, Except.ok.injEq, Value.prim.injEq, Prim.bool.injEq,
        Bool.false_eq, imp_self]
  case unaryApp op₁ x₁ _ hᵢ₁ hᵢ₂ hᵢ₃ =>
    simp [TPE.apply₁] at h₃
    generalize h₁ᵢ : TPE.evaluate x₁ req₂ es₂ = res₁
    split at h₃ <;> try simp at h₃
    split at h₃ <;> simp [someOrError] at h₃
    split at h₃ <;> simp at h₃
    simp [Spec.evaluate]
    rename_i heq _ _ _ _ heq₁
    simp [Residual.asValue] at heq
    split at heq <;> simp at heq
    rename_i heq₂
    specialize hᵢ₃ heq₂
    simp [hᵢ₃, heq]
    replace heq₁ := to_option_some heq₁
    rcases h₃ with ⟨h₃, _⟩
    subst h₃
    exact heq₁
  case binaryApp op₂ x₁ x₂ _ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ =>
    exact partial_evaluate_value_binary_app h₀ h₂ hᵢ₁ hᵢ₂ hᵢ₃ hᵢ₄ hᵢ₅ h₃
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry
  case _ => sorry

end Cedar.Thm
