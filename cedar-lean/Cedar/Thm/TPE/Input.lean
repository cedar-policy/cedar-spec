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

def PartialRequestMatchesEnvironment (env : Environment) (request : PartialRequest) : Prop :=
  PartialIsValid (InstanceOfEntityType · env.reqty.principal) request.principal.asEntityUID ∧
  request.action = env.reqty.action ∧
  PartialIsValid (InstanceOfEntityType · env.reqty.resource) request.resource.asEntityUID ∧
  PartialIsValid (InstanceOfType · (.record env.reqty.context)) request.context

def PartialEntitiesMatchEnvironment (env : Environment) (entities: PartialEntities) : Prop :=
  ∀ uid data, entities.find? uid = some data →
    ∃ entry, env.ets.find? uid.ty = some entry ∧
      IsValidEntityEID entry uid.eid ∧
      PartialIsValid (InstanceOfType · (.record entry.attrs)) data.attrs ∧
      PartialIsValid (λ ancestors => ∀ ancestor, ancestor ∈ ancestors → ancestor.ty ∈ entry.ancestors) data.ancestors ∧
      PartialIsValid (InstanceOfEntityTags · entry) data.tags

def PartialRequestAndEntitiesMatchEnvironment (env : Environment) (request : PartialRequest) (entities : PartialEntities) : Prop :=
  PartialRequestMatchesEnvironment env request ∧ PartialEntitiesMatchEnvironment env entities

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

theorem partial_request_matches_environment (env : Environment) (request : PartialRequest) :
  requestIsValid env request → PartialRequestMatchesEnvironment env request
:= by
  intro h₁
  simp [requestIsValid] at h₁
  rcases h₁ with ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩
  simp [PartialRequestMatchesEnvironment]
  apply And.intro
  exact partial_is_valid_rfl
    (fun x =>
  instanceOfEntityType x env.reqty.principal env.ets.entityTypeMembers?)
    (fun x => InstanceOfEntityType x env.reqty.principal)
    request.principal.asEntityUID
    (λ x => @instance_of_entity_type_refl x env.reqty.principal env.ets.entityTypeMembers?) h₁
  apply And.intro
  exact h₂
  apply And.intro
  exact partial_is_valid_rfl
    (fun x =>
  instanceOfEntityType x env.reqty.resource env.ets.entityTypeMembers?)
    (fun x => InstanceOfEntityType x env.reqty.resource)
    request.resource.asEntityUID
    (λ x => @instance_of_entity_type_refl x env.reqty.resource env.ets.entityTypeMembers?) h₃
  replace h₄ := partial_is_valid_rfl
    (fun x => instanceOfType (Value.record x) (CedarType.record env.reqty.context) env.ets)
    (fun x => InstanceOfType x (CedarType.record env.reqty.context))
    request.context
    (λ x => @instance_of_type_refl (Value.record x) (CedarType.record env.reqty.context) env.ets) h₄
  simp [Option.bind]
  split
  · constructor
  · rename_i heq
    rw [heq] at h₄
    simp only
    cases h₄
    rename_i heq
    constructor
    exact heq

theorem partial_entities_match_environment (env : Environment) (entities : PartialEntities) :
  entitiesIsValid env entities → PartialEntitiesMatchEnvironment env entities
:= by
  intro h₁
  simp [entitiesIsValid] at h₁
  rcases h₁ with ⟨h₁, _⟩
  simp [PartialEntitiesMatchEnvironment]
  intro uid data h₂
  specialize h₁ uid data (Data.Map.find?_mem_toList h₂)
  simp [entitiesIsValid.entityIsValid] at h₁
  split at h₁
  case _ entry heq =>
    exists entry
    simp only [Bool.and_eq_true] at h₁
    rcases h₁ with ⟨⟨⟨h₃, h₄⟩, h₅⟩, h₆⟩
    apply And.intro
    exact heq
    apply And.intro
    simp [IsValidEntityEID]
    simp [EntitySchemaEntry.isValidEntityEID] at h₃
    split at h₃
    · simp only
    · simp only
      simp [Data.Set.contains_prop_bool_equiv] at h₃
      exact h₃
    apply And.intro
    simp [Option.bind]
    split
    case _ => constructor
    case _ m heq =>
      simp only
      constructor
      simp only [heq] at h₅
      have h₇ := partial_is_valid_rfl
        (fun x => instanceOfType (Value.record x) (CedarType.record entry.attrs) env.ets)
        (fun x => InstanceOfType x (CedarType.record entry.attrs))
        (.some m)
        (λ x => @instance_of_type_refl (Value.record x) (CedarType.record entry.attrs) env.ets) h₅
      cases h₇
      rename_i h₇
      exact h₇
    apply And.intro
    have : (∀ (x : Data.Set EntityUID),
      Data.Set.all
          (fun ancestor =>
            entry.ancestors.contains ancestor.ty &&
              instanceOfEntityType ancestor ancestor.ty env.ets.entityTypeMembers?)
          x =
        true →
      ∀ (ancestor : EntityUID), ancestor ∈ x → ancestor.ty ∈ entry.ancestors) := by
      intro ancestors h ancestor hᵢ
      simp [Data.Set.all] at h
      specialize h ancestor hᵢ
      rcases h with ⟨h, _⟩
      simp [Data.Set.contains_prop_bool_equiv] at h
      exact h
    have h₇ := partial_is_valid_rfl
      (fun ancestors => Data.Set.all
        (fun ancestor =>
          entry.ancestors.contains ancestor.ty && instanceOfEntityType ancestor ancestor.ty env.ets.entityTypeMembers?)
          ancestors)
      (fun ancestors => ∀ (ancestor : EntityUID), ancestor ∈ ancestors → ancestor.ty ∈ entry.ancestors) data.ancestors this h₄
    exact h₇
    have : (∀ (x : Data.Map Tag Value),
    (match entry.tags? with
        | some tty => x.values.all fun x => instanceOfType x tty env.ets
        | none => x == Data.Map.empty) =
        true →
      InstanceOfEntityTags x entry) := by
      intro tags h
      simp [InstanceOfEntityTags]
      split
      case _ heq =>
        simp [heq] at h
        intro v hᵢ
        specialize h v hᵢ
        exact instance_of_type_refl h
      case _ heq =>
        simp [heq] at h
        exact h
    have h₇ := partial_is_valid_rfl
      (fun tags =>
        match entry.tags? with
        | some tty => tags.values.all fun x => instanceOfType x tty env.ets
        | none => tags == Data.Map.empty)
      (fun x => InstanceOfEntityTags x entry) data.tags this h₆
    exact h₇
  case _ => cases h₁

end Cedar.Thm
