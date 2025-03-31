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
import Cedar.Thm

namespace Cedar.Thm

open Cedar.TPE
open Cedar.Spec
open Cedar.Validation
open Cedar.Thm

/-
-- We do not check if `req`'s action is valid (i.e, if it's contained in `env`)
-- because this function is called after validation, which already ensures it
def requestIsValid (env : Environment) (req : PartialRequest) : Bool :=
  (partialIsValid req.principal.asEntityUID λ principal =>
    instanceOfEntityType principal principal.ty env.ets.entityTypeMembers?) &&
  (partialIsValid req.resource.asEntityUID λ resource =>
    instanceOfEntityType resource resource.ty env.ets.entityTypeMembers?) &&
  (partialIsValid req.context λ m =>
    instanceOfType (.record m) (.record env.reqty.context) env.ets)
-/

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
  PartialIsValid (InstanceOfEntityType · env.reqty.resource) request.resource.asEntityUID ∧
  PartialIsValid (InstanceOfType · (.record env.reqty.context)) request.context

/-
∀ uid data, entities.find? uid = some data →
    ∃ entry, ets.find? uid.ty = some entry ∧
      IsValidEntityEID entry uid.eid ∧
      InstanceOfType data.attrs (.record entry.attrs) ∧
      (∀ ancestor, ancestor ∈ data.ancestors → ancestor.ty ∈ entry.ancestors) ∧
      InstanceOfEntityTags data entry
-/
/-
def entitiesIsValid (env : Environment) (es : PartialEntities) : Bool :=
  (es.toList.all entityIsValid) && (env.acts.toList.all instanceOfActionSchema)
where
  entityIsValid p :=
    let (uid, ⟨attrs, ancestors, tags⟩) := p
    match env.ets.find? uid.ty with
    | .some entry =>
      entry.isValidEntityEID uid.eid &&
      (partialIsValid ancestors λ ancestors =>
        ancestors.all (λ ancestor =>
        entry.ancestors.contains ancestor.ty &&
        instanceOfEntityType ancestor ancestor.ty env.ets.entityTypeMembers?)) &&
      (partialIsValid attrs (instanceOfType · (.record entry.attrs) env.ets)) &&
      (partialIsValid tags λ tags =>
        match entry.tags? with
        | .some tty => tags.values.all (instanceOfType · tty env.ets)
        | .none     => tags == Map.empty)
    | .none       => false
  instanceOfActionSchema p :=
    let (uid, entry) := p
    match es.find? uid with
    | .some entry₁ => entry.ancestors == entry₁.ancestors
    | _            => false
-/
def PartialEntitiesMatchEnvironment (env : Environment) (entities: PartialEntities) : Prop :=
  ∀ uid data, entities.find? uid = some data →
    ∃ entry, env.ets.find? uid.ty = some entry ∧
      IsValidEntityEID entry uid.eid ∧
      PartialIsValid (InstanceOfType · (.record entry.attrs)) data.attrs ∧
      PartialIsValid (λ ancestors => ∀ ancestor, ancestor ∈ ancestors → ancestor.ty ∈ entry.ancestors) data.ancestors ∧
      PartialIsValid (InstanceOfEntityTags · entry) data.tags

def PartialRequestAndEntitiesMatchEnvironment (env : Environment) (request : PartialRequest) (entities : PartialEntities) : Prop := sorry

def IsConsistent (env : Environment) (req₁ : Request) (es₁ : Entities) (req₂ : PartialRequest) (es₂ : PartialEntities) : Prop := sorry

theorem partial_request_matches_environment (env : Environment) (request : PartialRequest) :
  requestIsValid env request → PartialRequestMatchesEnvironment env request
:= by
  intro h₁
  simp [requestIsValid] at h₁
  rcases h₁ with ⟨⟨h₁, h₂⟩, h₃⟩
  simp [PartialRequestMatchesEnvironment]
  apply And.intro
  · exact partial_is_valid_rfl
      (fun x =>
    instanceOfEntityType x env.reqty.principal env.ets.entityTypeMembers?)
      (fun x => InstanceOfEntityType x env.reqty.principal)
      request.principal.asEntityUID
      (λ x => @instance_of_entity_type_refl x env.reqty.principal env.ets.entityTypeMembers?) h₁
  · apply And.intro
    · exact partial_is_valid_rfl
        (fun x =>
      instanceOfEntityType x env.reqty.resource env.ets.entityTypeMembers?)
        (fun x => InstanceOfEntityType x env.reqty.resource)
        request.resource.asEntityUID
        (λ x => @instance_of_entity_type_refl x env.reqty.resource env.ets.entityTypeMembers?) h₂
    · have h₄ := partial_is_valid_rfl
        (fun x => instanceOfType (Value.record x) (CedarType.record env.reqty.context) env.ets)
        (fun x => InstanceOfType x (CedarType.record env.reqty.context))
        request.context
        (λ x => @instance_of_type_refl (Value.record x) (CedarType.record env.reqty.context) env.ets) h₃
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
:= by sorry
end Cedar.Thm
