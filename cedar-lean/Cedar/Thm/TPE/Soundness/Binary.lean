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
import Cedar.Thm.TPE.ErrorFree
import Cedar.Thm.TPE.WellTyped
import Cedar.Thm.Validation
import Cedar.Thm.WellTyped
import Cedar.Thm.Data.Control

import Cedar.Thm.TPE.Soundness.Basic

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Validation
open Cedar.TPE
open Cedar.Thm

theorem partial_evaluate_is_sound_binary_app
{op₂ : BinaryOp}
{ty : CedarType}
{x₁ x₂ : Residual}
{req : Request}
{es : Entities}
{preq : PartialRequest}
{pes : PartialEntities}
{env : TypeEnv}
(h₂ : InstanceOfWellFormedEnvironment req es env)
(h₄ : RequestAndEntitiesRefine env req es preq pes)
(hwt : Residual.WellTyped env x₂)
(howt : BinaryResidualWellTyped env op₂ x₁ x₂ ty)
(hᵢ₁ : Except.toOption (x₁.evaluate req es) = Except.toOption ((TPE.evaluate x₁ preq pes).evaluate req es))
(hᵢ₂ : Except.toOption (x₂.evaluate req es) = Except.toOption ((TPE.evaluate x₂ preq pes).evaluate req es)) :
  Except.toOption ((Residual.binaryApp op₂ x₁ x₂ ty).evaluate req es) =
  Except.toOption ((TPE.evaluate (Residual.binaryApp op₂ x₁ x₂ ty) preq pes).evaluate req es)
:= by
  simp [TPE.evaluate, TPE.apply₂]
  split
  case _ heq₁ heq₂ =>
    have heval₁ := asResidualValue_evaluate heq₁ req es
    have heval₂ := asResidualValue_evaluate heq₂ req es
    rw [heval₁] at hᵢ₁; rw [heval₂] at hᵢ₂
    sorry
  /-
        rcases heq₄ with ⟨_, heq₄₁, heq₄₂⟩
        subst heq₄₂
        simp [heq₃] at heq₄₁
        subst heq₄₁
        simp [Residual.evaluate]
      case _ heq₃ _ _ _ heq₄ =>
        simp only [heq₃, Option.bind_some, reduceCtorEq] at heq₄
      case _ heq₃ _ _ _ _ heq₄ =>
        simp only [heq₃, Option.bind_none, reduceCtorEq] at heq₄
      case _ =>
        simp only [Except.toOption, Residual.evaluate]
    case _ uid₁ uid₂ =>
      simp [apply₂.self, someOrSelf]
      split
      case _ heq₃ =>
        simp only [Option.bind_eq_some_iff] at heq₃
        rcases heq₃ with ⟨_, heq₃₁, heq₃₂⟩
        simp only [Option.some.injEq] at heq₃₂
        subst heq₃₂
        simp [Residual.evaluate]
        simp [TPE.inₑ] at heq₃₁
        split at heq₃₁
        case _ heq₄ =>
          simp at heq₃₁
          subst heq₃₁
          simp [Spec.inₑ, heq₄]
        case _ heq₄ =>
          simp [Option.map] at heq₃₁
          split at heq₃₁ <;> cases heq₃₁
          rename_i heq₅
          simp [PartialEntities.ancestors, PartialEntities.get, Option.bind_eq_some_iff] at heq₅
          rcases heq₅ with ⟨data, heq₅₁, heq₅₂⟩
          simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
          rcases h₄ with ⟨_, h₄⟩
          specialize h₄ uid₁ data heq₅₁
          rcases h₄ with ⟨_, h₄₁, _, h₄₂, _⟩
          rw [heq₅₂] at h₄₂
          cases h₄₂
          rename_i h₄₂
          simp [Spec.inₑ, Entities.ancestorsOrEmpty, h₄₁, ←h₄₂]
          have : (uid₁ == uid₂) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, heq₄, not_false_eq_true]
          simp only [this, Bool.false_or]
      case _ heq₃ =>
        rw [asValue_some] at heq₁ heq₂
        rw [heq₁.choose_spec, heq₂.choose_spec]
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ =>
      simp [apply₂.self, someOrSelf]
      split
      case _ uid vs _ _ _ _ _ heq₃ =>
        simp only [Option.bind_eq_some_iff] at heq₃
        rcases heq₃ with ⟨_, heq₃₁, heq₃₂⟩
        simp only [Option.some.injEq] at heq₃₂
        subst heq₃₂
        simp [Spec.inₛ]
        cases howt <;>
        (rename_i h₅; have h₆ := residual_well_typed_is_sound h₂ hwt hᵢ₂; rw [h₅] at h₆; cases h₆)
        rename_i h₆
        simp [Data.Set.mapOrErr]
        generalize h₇ : List.mapM Value.asEntityUID vs.elts = res
        cases res
        case _ =>
          rcases List.mapM_error_implies_exists_error h₇ with ⟨v, h₇₁, h₇₂⟩
          specialize h₆ v h₇₁
          rcases instance_of_entity_type_is_entity h₆ with ⟨_, _, h₆⟩
          simp only [Value.asEntityUID, h₆, reduceCtorEq] at h₇₂
        case _ =>
          simp only [Except.bind_ok, Data.Set.any_make]
          simp [TPE.inₛ, Option.bind_eq_some_iff, Data.Set.toList] at heq₃₁
          rcases heq₃₁ with ⟨vs', heq₃₁, heq₃₂⟩
          rw [List.mapM_some_iff_forall₂] at heq₃₁
          have heq₄ : List.Forall₂ (fun x y => x.asEntityUID = .ok y) vs.elts vs' := by
            have : ∀ x y, (Except.toOption ∘ Value.asEntityUID) x = some y → x.asEntityUID = .ok y := by
              intro x y h
              simp [Except.toOption] at h
              split at h <;> cases h
              rename_i heq
              exact heq
            exact List.Forall₂.imp this heq₃₁
          rw [←List.mapM_ok_iff_forall₂] at heq₄
          simp [heq₄] at h₇
          subst h₇
          simp [Spec.inₑ]
          simp [TPE.inₑ] at heq₃₂
          simp [RequestAndEntitiesRefine] at h₄
          rcases h₄ with ⟨_, h₄⟩
          have : ∀ x b, ((if uid = x then some true else Option.map (fun y => y.contains x) (pes.ancestors uid)) = some b) →
            (uid == x || (es.ancestorsOrEmpty uid).contains x) = b := by
            intro x b' h₁
            split at h₁
            case isTrue heq =>
              simp only [Option.some.injEq, Bool.true_eq] at h₁
              subst h₁
              simp only [heq, beq_self_eq_true, Bool.true_or]
            case isFalse heq =>
              simp [EntitiesRefine] at h₄
              simp at h₁
              rcases h₁ with ⟨ancestors₁, h₂, h₃⟩
              simp [PartialEntities.ancestors, PartialEntities.get, Option.bind] at h₂
              split at h₂ <;> try cases h₂
              rename_i data heq₁
              specialize h₄ uid data heq₁
              rcases h₄ with ⟨e, h₄, _, h₅, _⟩
              rw [h₂] at h₅
              cases h₅
              rename_i heq₂
              rw [heq₂] at h₃
              simp only [Entities.ancestorsOrEmpty, h₄, h₃, Bool.or_eq_right_iff_imp, beq_iff_eq, heq,
                false_implies]
          replace heq₃₂ := List.anyM_some_implies_any (fun x => if uid = x then some true else Option.map (fun y => y.contains x) (pes.ancestors uid))
            (fun x => uid == x || (es.ancestorsOrEmpty uid).contains x) this heq₃₂
          subst heq₃₂
          simp only [Residual.evaluate]
      case _ =>
        rw [asValue_some] at heq₁ heq₂
        rw [heq₁.choose_spec, heq₂.choose_spec]
        simp only [Spec.inₛ, Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ uid _ =>
      simp [someOrSelf, apply₂.self]
      split
      case _ heq =>
        rw [Option.bind_eq_some_iff] at heq
        rcases heq with ⟨_, heq₁, heq₂⟩
        simp at heq₂
        subst heq₂
        simp [TPE.hasTag] at heq₁
        rcases heq₁ with ⟨_, heq₁, heq₂⟩
        simp [PartialEntities.tags, PartialEntities.get] at heq₁
        rw [Option.bind_eq_some_iff] at heq₁
        rcases heq₁ with ⟨data, heq₃, heq₄⟩
        subst heq₂
        simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
        rcases h₄ with ⟨_, h₄⟩
        specialize h₄ uid data heq₃
        rcases h₄ with ⟨_, h₄₁, _, _, h₄₂⟩
        rw [heq₄] at h₄₂
        cases h₄₂
        rename_i heq₅
        subst heq₅
        simp only [Spec.hasTag, Entities.tagsOrEmpty, h₄₁, Residual.evaluate]
      case _ =>
        rw [asValue_some] at heq₁ heq₂
        rw [heq₁.choose_spec, heq₂.choose_spec]
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ uid _ =>
      simp [TPE.getTag, someOrError]
      split
      case _ heq =>
        simp [PartialEntities.tags, PartialEntities.get] at heq
        rw [Option.bind_eq_some_iff] at heq
        rcases heq with ⟨data, heq₂, heq₃⟩
        simp [RequestAndEntitiesRefine, EntitiesRefine] at h₄
        rcases h₄ with ⟨_, h₄⟩
        specialize h₄ uid data heq₂
        rcases h₄ with ⟨_, h₄₁, _, _, h₄₂⟩
        rw [heq₃] at h₄₂
        cases h₄₂
        rename_i heq₄
        subst heq₄
        simp only [Spec.getTag, Entities.tags, Data.Map.findOrErr, h₄₁]
        split <;>
        (rename_i heq₁; simp [heq₁, Residual.evaluate, Except.toOption])
      case _ =>
        simp only [Residual.evaluate, Spec.apply₂, Except.bind_ok]
    case _ => simp [Except.toOption]
 -/
  case _ =>
    split
    case _ heq =>
      simp [heq, Residual.evaluate] at hᵢ₁
      rcases to_option_right_err hᵢ₁ with ⟨_, hᵢ₁⟩
      simp [Residual.evaluate, hᵢ₁, Except.toOption]
    case _ heq _ =>
      simp [heq, Residual.evaluate] at hᵢ₂
      rcases to_option_right_err hᵢ₂ with ⟨_, hᵢ₂⟩
      simp only [Residual.evaluate, hᵢ₂, Except.bind_err, do_error_to_option]
      simp only [Except.toOption]
    case _ =>
      simp [Residual.evaluate, apply₂.self]
      exact to_option_eq_do₂
        (λ x y => Spec.apply₂ op₂ x y es) hᵢ₁ hᵢ₂


end Cedar.Thm
