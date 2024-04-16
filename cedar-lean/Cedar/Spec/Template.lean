/-
 Copyright Cedar Contributors. All Rights Reserved.

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

import Cedar.Spec.Policy

/-!
  This file defines abstract syntax for Cedar policy templates. In general,
  Cedar operations (e.g., authorization, validation) are defined over policies
  rather than templates. We generate policies from templates by using link?.
  During differential testing, templates are only used during parsing
-/

namespace Cedar.Spec

open Cedar.Data

----- Definitions -----

abbrev SlotID := String

inductive EntityUIDOrSlot where
  | entityUID (entity : EntityUID)
  | slot (id : SlotID)

inductive ScopeTemplate where
  | any
  | eq (entityOrSlot : EntityUIDOrSlot)
  | mem (entityOrSlot : EntityUIDOrSlot)
  | is (ety : EntityType)
  | isMem (ety : EntityType) (entityOrSlot : EntityUIDOrSlot)

inductive PrincipalScopeTemplate where
  | principalScope (scope : ScopeTemplate)

inductive ResourceScopeTemplate where
  | resourceScope (scope : ScopeTemplate)

abbrev TemplateID := String

structure Template where
  effect : Effect
  principalScope : PrincipalScopeTemplate
  actionScope : ActionScope
  resourceScope : ResourceScopeTemplate
  condition : Expr

abbrev Templates := Map TemplateID Template

abbrev SlotEnv := Map SlotID EntityUID

structure TemplateLinkedPolicy where
  id : PolicyID
  templateId : TemplateID
  slotEnv : SlotEnv

abbrev TemplateLinkedPolicies := List TemplateLinkedPolicy

def EntityUIDOrSlot.link? (slotEnv : SlotEnv) : EntityUIDOrSlot → Option EntityUID
  | entityUID entity => .some entity
  | slot id => slotEnv.find? id

def ScopeTemplate.link? (slotEnv : SlotEnv) : ScopeTemplate → Option Scope
  | .any => .some .any
  | .eq entityOrSlot => do
    let entity ← entityOrSlot.link? slotEnv
    .some (.eq entity)
  | .mem entityOrSlot => do
    let entity ← entityOrSlot.link? slotEnv
    .some (.mem entity)
  | .is ety => .some (.is ety)
  | .isMem ety entityOrSlot => do
    let entity ← entityOrSlot.link? slotEnv
    .some (.isMem ety entity)

def PrincipalScopeTemplate.link? (slotEnv : SlotEnv) : PrincipalScopeTemplate → Option PrincipalScope
  | .principalScope s => do
    let s ← s.link? slotEnv
    .some (.principalScope s)

def ResourceScopeTemplate.link? (slotEnv : SlotEnv) : ResourceScopeTemplate → Option ResourceScope
  | .resourceScope s => do
    let s ← s.link? slotEnv
    .some (.resourceScope s)

def Template.link? (template : Template) (id : PolicyID) (slotEnv : SlotEnv) : Option Policy := do
  let principalScope ← template.principalScope.link? slotEnv
  let resourceScope ← template.resourceScope.link? slotEnv
  .some {
    id := id,
    effect := template.effect,
    principalScope := principalScope,
    actionScope := template.actionScope,
    resourceScope := resourceScope,
    condition := template.condition
  }

def linkPolicy? (templates : Templates) (link : TemplateLinkedPolicy) : Option Policy := do
  let template ← templates.find? link.templateId
  template.link? link.id link.slotEnv

def link? (templates : Templates) (links : TemplateLinkedPolicies) : Option Policies :=
  links.mapM (linkPolicy? templates)

end Cedar.Spec
