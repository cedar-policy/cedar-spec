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

import Cedar.TPE.Input
import Cedar.Spec
import Cedar.Validation
import Cedar.Thm.Validation

/-!
This file defines theorems related to the inputs of TPE.
-/

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

theorem decide_eq_implies_eq {α} [DecidableEq α] {y : α} :
  ∀ x, decide (x = y) → x = y := by
      simp only [decide_eq_true_eq, imp_self, implies_true]

inductive PartialIsValid {α} (p : α → Prop) (o : Option α) : Prop
  | some (x : α) (heq : o = .some x) (h : p x) :
    PartialIsValid p o
  | none (heq : o = .none) :
    PartialIsValid p o

@[simp]
theorem PartialIsValid.some_inv {p : α → Prop} {x : α} :  (PartialIsValid p (.some x)) ↔ p x := by
  constructor
  · intro h
    cases h with
    | some y heq hy => simp only [Option.some.injEq] at heq; subst heq; exact hy
    | none heq => simp at heq
  · exact some _ rfl

theorem partial_is_valid_rfl {f : α → Bool} {p : α → Prop} {o : Option α} :
  (∀ x, f x = true → p x) → partialIsValid o f → PartialIsValid p o
:= by
  intro h₁ h₂
  cases o with
  | none => exact .none rfl
  | some x =>
    simp only [partialIsValid, Option.map_some, Option.getD_some] at h₂
    exact .some x rfl (h₁ x h₂)

def RequestRefines (req : Request) (preq : PartialRequest) : Prop :=
  PartialIsValid (· = req.principal) preq.principal.asEntityUID ∧
  req.action = preq.action ∧
  PartialIsValid (· = req.resource) preq.resource.asEntityUID  ∧
  PartialIsValid (· = req.context) preq.context ∧
  preq.principal.ty = req.principal.ty ∧
  preq.resource.ty = req.resource.ty

def EntitiesRefine (es : Entities) (pes : PartialEntities) : Prop :=
   ∀ a e₂, pes.find? a = some e₂ → (∃ e₁, es.find? a = some e₁ ∧
    PartialIsValid (· = e₁.attrs) e₂.attrs ∧
    PartialIsValid (· = e₁.ancestors) e₂.ancestors  ∧
    PartialIsValid (· = e₁.tags) e₂.tags)

/-- Concrete request `req` and entities `es` refine their partial counterparts
`peq` and `pes`.
-/
def RequestAndEntitiesRefine (req : Request) (es : Entities) (preq : PartialRequest) (pes : PartialEntities) : Prop :=
  RequestRefines req preq ∧ EntitiesRefine es pes

theorem validatePartialRequest_ok_environment? {schema : Schema} {req : PartialRequest} {env : TypeEnv} :
  validatePartialRequest schema req = .ok env →
  schema.environment? req.principal.ty req.resource.ty req.action = .some env
:= by
  intro h
  simp only [validatePartialRequest] at h
  split at h
  · rename_i env' heq
    split at h <;> try contradiction
    simp only [Except.ok.injEq] at h
    simp [h, heq]
  · contradiction

theorem entitiesIsConsistent_implies_refines {es : Entities} {pes : PartialEntities} :
  entitiesIsConsistent es pes → EntitiesRefine es pes
:= by
  intro h uid data₂ hᵢ
  replace hᵢ := Data.Map.find?_mem_toList hᵢ
  simp only [entitiesIsConsistent, List.all_eq_true, Prod.forall] at h
  specialize h uid data₂ hᵢ
  split at h <;> simp only [Bool.false_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨⟨h₂₁, h₂₂⟩, h₂₃⟩
  rename_i data₁ heq
  exists data₁
  and_intros
  · exact heq
  · exact partial_is_valid_rfl decide_eq_implies_eq h₂₁
  · exact partial_is_valid_rfl decide_eq_implies_eq h₂₂
  · exact partial_is_valid_rfl decide_eq_implies_eq h₂₃

theorem requestIsConsistent_implies_refines {req : Request} {preq : PartialRequest} :
  requestIsConsistent req preq →
  RequestRefines req preq
:= by
  intro h₁
  simp only [requestIsConsistent, Bool.and_eq_true, decide_eq_true_eq] at h₁
  obtain ⟨⟨⟨⟨⟨h_pty, h_rty⟩, h₁₁⟩, h₁₂⟩, h₁₃⟩, h₁₄⟩ := h₁
  and_intros
  · exact partial_is_valid_rfl decide_eq_implies_eq h₁₁
  · exact h₁₂
  · exact partial_is_valid_rfl decide_eq_implies_eq h₁₃
  · exact partial_is_valid_rfl decide_eq_implies_eq h₁₄
  · exact h_pty
  · exact h_rty

/-- Requests and entities that pass `isValidAndConsistent` satisfy `RequestAndEntitiesRefine`.  -/
theorem consistent_checks_ensure_refinement {schema : Schema} {req : Request} {es : Entities} {preq : PartialRequest} {pes : PartialEntities} :
  isValidAndConsistent schema req es preq pes = .ok () → RequestAndEntitiesRefine req es preq pes
:= by
  intro h
  simp only [isValidAndConsistent] at h
  split at h <;> try cases h
  rename_i env heq
  rcases do_eq_ok₂ h with ⟨h₁, h₂⟩
  constructor
  case _ =>
    have h_consistent : requestIsConsistent req preq := by
      simp only [isValidAndConsistent.requestIsValidAndConsistent] at h₁
      split at h₁ <;> simp_all
    exact requestIsConsistent_implies_refines h_consistent
  case _ =>
    have h₃ : isValidAndConsistent.entitiesIsValidAndConsistent es pes env = .ok ()
    := by
      simp only [isValidAndConsistent.envIsWellFormed, bind, Except.bind] at h₂
      split at h₂ <;> simp_all
    have h_consistent : entitiesIsConsistent es pes := by
      simp only [isValidAndConsistent.entitiesIsValidAndConsistent] at h₃
      split at h₃ <;> simp_all
    exact entitiesIsConsistent_implies_refines h_consistent

end Cedar.Thm
