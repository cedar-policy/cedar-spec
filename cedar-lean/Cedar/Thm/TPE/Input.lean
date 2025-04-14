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

def RequestIsConsistent (req₁ : Request) (req₂ : PartialRequest) : Prop :=
  PartialIsValid (· = req₁.principal) req₂.principal.asEntityUID ∧
  req₁.action = req₂.action ∧
  PartialIsValid (· = req₁.resource) req₂.resource.asEntityUID  ∧
  PartialIsValid (· = req₁.context) req₂.context

def EntitiesAreConsistent (es₁ : Entities) (es₂ : PartialEntities) : Prop :=
   ∀ a e₂, es₂.find? a = some e₂ → (∃ e₁, es₁.find? a = some e₁ ∧
    PartialIsValid (· = e₁.attrs) e₂.attrs ∧
    PartialIsValid (· = e₁.ancestors) e₂.ancestors  ∧
    PartialIsValid (· = e₁.tags) e₂.tags)

/- should have a better name like `abstracts`.
Also note that `isConsistent` is a much stronger check that ensures both
partial and concrete parts are validated.
-/
def IsConsistent (req₁ : Request) (es₁ : Entities) (req₂ : PartialRequest) (es₂ : PartialEntities) : Prop :=
  RequestIsConsistent req₁ req₂ ∧ EntitiesAreConsistent es₁ es₂

theorem consistent_checks_ensure_consistency {schema : Schema} {req₁ : Request} {es₁ : Entities} {req₂ : PartialRequest} {es₂ : PartialEntities} :
  isValidAndConsistent schema req₁ es₁ req₂ es₂ = .ok () → IsConsistent req₁ es₁ req₂ es₂
:= by
  intro h
  simp [isValidAndConsistent] at h
  split at h <;> try cases h
  rcases do_eq_ok₂ h with ⟨h₁, h₂⟩
  simp [IsConsistent]
  constructor
  case _ =>
    simp [RequestIsConsistent]
    simp [isValidAndConsistent.requestIsConsistent] at h₁
    split at h₁ <;> simp at h₁
    rcases h₁ with ⟨h₁₁, h₁₂, h₁₃, h₁₄⟩
    constructor
    exact partial_is_valid_rfl (fun x => decide (x = req₁.principal)) (fun x => x = req₁.principal) req₂.principal.asEntityUID decide_eq_implies_eq h₁₁
    constructor
    exact h₁₂
    constructor
    exact partial_is_valid_rfl (fun x => decide (x = req₁.resource)) (fun x => x = req₁.resource) req₂.resource.asEntityUID decide_eq_implies_eq h₁₃
    exact partial_is_valid_rfl (fun x => decide (x = req₁.context)) (fun x => x = req₁.context) req₂.context decide_eq_implies_eq h₁₄
  case _ =>
    simp [isValidAndConsistent.entitiesIsConsistent] at h₂
    split at h₂ <;> simp at h₂
    simp [isValidAndConsistent.entitiesMatch] at h₂
    simp [EntitiesAreConsistent]
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
