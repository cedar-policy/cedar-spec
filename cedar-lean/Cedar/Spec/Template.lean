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
deriving Repr, DecidableEq

inductive ScopeTemplate where
  | any
  | eq (entityOrSlot : EntityUIDOrSlot)
  | mem (entityOrSlot : EntityUIDOrSlot)
  | is (ety : EntityType)
  | isMem (ety : EntityType) (entityOrSlot : EntityUIDOrSlot)
deriving Repr, DecidableEq

inductive PrincipalScopeTemplate where
  | principalScope (scope : ScopeTemplate)
deriving Repr, DecidableEq

inductive ResourceScopeTemplate where
  | resourceScope (scope : ScopeTemplate)
deriving Repr, DecidableEq

abbrev TemplateID := String

structure Template where
  effect : Effect
  principalScope : PrincipalScopeTemplate
  actionScope : ActionScope
  resourceScope : ResourceScopeTemplate
  condition : Conditions
deriving Repr, DecidableEq

abbrev Templates := Map TemplateID Template

abbrev SlotEnv := Map SlotID EntityUID

def SlotEnv.empty : SlotEnv := Map.empty

structure TemplateLinkedPolicy where
  id : PolicyID
  templateId : TemplateID
  slotEnv : SlotEnv
deriving Repr

abbrev TemplateLinkedPolicies := List TemplateLinkedPolicy

def EntityUIDOrSlot.link? (slotEnv : SlotEnv) : EntityUIDOrSlot → Except String EntityUID
  | entityUID entity => .ok entity
  | slot id => slotEnv.findOrErr id s!"missing binding for slot {id}"

def ScopeTemplate.link? (slotEnv : SlotEnv) : ScopeTemplate → Except String Scope
  | .any => .ok .any
  | .eq entityOrSlot => do
    let entity ← entityOrSlot.link? slotEnv
    .ok (.eq entity)
  | .mem entityOrSlot => do
    let entity ← entityOrSlot.link? slotEnv
    .ok (.mem entity)
  | .is ety => .ok (.is ety)
  | .isMem ety entityOrSlot => do
    let entity ← entityOrSlot.link? slotEnv
    .ok (.isMem ety entity)

def PrincipalScopeTemplate.link? (slotEnv : SlotEnv) : PrincipalScopeTemplate → Except String PrincipalScope
  | .principalScope s => do
    let s ← s.link? slotEnv
    .ok (.principalScope s)

def ResourceScopeTemplate.link? (slotEnv : SlotEnv) : ResourceScopeTemplate → Except String ResourceScope
  | .resourceScope s => do
    let s ← s.link? slotEnv
    .ok (.resourceScope s)

def Template.link? (template : Template) (id : PolicyID) (slotEnv : SlotEnv) : Except String Policy := do
  let principalScope ← template.principalScope.link? slotEnv
  let resourceScope ← template.resourceScope.link? slotEnv
  .ok {
    id := id,
    effect := template.effect,
    principalScope := principalScope,
    actionScope := template.actionScope,
    resourceScope := resourceScope,
    condition := template.condition
  }

def linkPolicy? (templates : Templates) (link : TemplateLinkedPolicy) : Except String Policy := do
  let template ← templates.findOrErr link.templateId s!"templateId {link.templateId} not found"
  template.link? link.id link.slotEnv

def link? (templates : Templates) (links : TemplateLinkedPolicies) : Except String Policies :=
  links.mapM (linkPolicy? templates)

end Cedar.Spec
