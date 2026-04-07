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

inductive PartialIsValid {α} : (α → Prop) → Option α -> Prop
  | some (p : α → Prop) (x : α)
    (h : p x) :
    PartialIsValid p (.some x)
  | none :
    PartialIsValid p .none

theorem partial_is_valid_rfl (f : α → Bool) (p : α → Prop) (o : Option α) :
  (∀ x, f x = true → p x) → partialIsValid o f → PartialIsValid p o
:= by
  intro h₁
  simp [partialIsValid, Option.map]
  split <;> simp [Option.getD]
  case _ x =>
    intro h₂
    constructor
    exact h₁ x h₂
  case _ =>
    constructor

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

/-- Requests and entities that pass `isValidAndConsistent` satisfy `RequestAndEntitiesRefine`.
-/
theorem consistent_checks_ensure_refinement {schema : Schema} {req : Request} {es : Entities} {preq : PartialRequest} {pes : PartialEntities} :
  isValidAndConsistent schema req es preq pes = .ok () → RequestAndEntitiesRefine req es preq pes
:= by
  intro h
  simp [isValidAndConsistent] at h
  split at h <;> try cases h
  rcases do_eq_ok₂ h with ⟨h₁, h₂⟩
  simp [RequestAndEntitiesRefine]
  constructor
  case _ =>
    simp [RequestRefines]
    simp [isValidAndConsistent.requestIsConsistent] at h₁
    split at h₁ <;> simp at h₁
    rcases h₁ with ⟨h₁₁, h₁₂, h₁₃, h₁₄⟩
    -- Extract type equalities from requestMatchesEnvironment and schema.environment?
    rename_i env heq h_guard
    simp [not_or, Bool.not_eq_false] at h_guard
    have h_rm := h_guard.2
    simp only [requestMatchesEnvironment, instanceOfRequestType, instanceOfEntityType,
      Bool.and_eq_true, beq_iff_eq] at h_rm
    refine ⟨
      partial_is_valid_rfl _ _ _ decide_eq_implies_eq h₁₁,
      h₁₂,
      partial_is_valid_rfl _ _ _ decide_eq_implies_eq h₁₃,
      partial_is_valid_rfl _ _ _ decide_eq_implies_eq h₁₄,
      ?_, ?_⟩
    all_goals {
      unfold Schema.environment? at heq
      cases h_find : schema.acts.find? preq.action
      · simp [h_find] at heq
      · simp [h_find] at heq
        split at heq <;> simp at heq
        rw [← heq] at h_rm
        simp_all
    }

  case _ =>
    simp [
      isValidAndConsistent.envIsWellFormed,
      bind, Except.bind,
    ] at h₂
    split at h₂ <;> simp at h₂
    rename_i h₃
    replace h₂ := h₃
    simp [isValidAndConsistent.entitiesIsConsistent] at h₂
    split at h₂ <;> simp at h₂
    simp [isValidAndConsistent.entitiesMatch] at h₂
    simp [EntitiesRefine]
    intro uid data₂ hᵢ
    replace hᵢ := Data.Map.find?_mem_toList hᵢ
    simp [Data.Map.toList] at hᵢ
    specialize h₂ uid data₂ hᵢ
    split at h₂ <;> simp at h₂
    rcases h₂ with ⟨⟨h₂₁, h₂₂⟩, h₂₃⟩
    rename_i data₁ heq
    exists data₁
    constructor
    exact heq
    constructor
    exact partial_is_valid_rfl (fun x => decide (x = data₁.attrs)) (fun x => x = data₁.attrs) data₂.attrs decide_eq_implies_eq h₂₁
    constructor
    exact partial_is_valid_rfl (fun x => decide (x = data₁.ancestors)) (fun x => x = data₁.ancestors) data₂.ancestors decide_eq_implies_eq h₂₂
    exact partial_is_valid_rfl (fun x => decide (x = data₁.tags)) (fun x => x = data₁.tags) data₂.tags decide_eq_implies_eq h₂₃

end Cedar.Thm
