/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
  id : TemplateID
  effect : Effect
  principalScope : PrincipalScopeTemplate
  actionScope : ActionScope
  resourceScope : ResourceScopeTemplate
  condition : Expr

abbrev Templates := List Template

abbrev SlotEnv := Map SlotID EntityUID

structure TemplateLinkedPolicy where
  id : TemplateID
  slotEnv : SlotEnv

abbrev TemplateLinkedPolicies := List TemplateLinkedPolicy

def EntityUIDOrSlot.link? (entityOrSlot : EntityUIDOrSlot) (slotEnv : SlotEnv) : Option EntityUID :=
  match entityOrSlot with
  | entityUID entity => .some entity
  | slot id => slotEnv.find? id 

def ScopeTemplate.link? (scope : ScopeTemplate) (slotEnv : SlotEnv) : Option Scope :=
  match scope with
  | .any => .some .any
  | .eq entityOrSlot => do
    let entity <- entityOrSlot.link? slotEnv
    .some (.eq entity)
  | .mem entityOrSlot => do
    let entity <- entityOrSlot.link? slotEnv
    .some (.mem entity)
  | .is ety => .some (.is ety)
  | .isMem ety entityOrSlot => do
    let entity <- entityOrSlot.link? slotEnv
    .some (.isMem ety entity)

def linkPolicy? (template : Template) (slotEnv : SlotEnv) : Option Policy :=
  -- lookup template, and call linkScope

def link? (templates : Templates) (links : TemplateLinkedPolicies) : Option Policies :=
  links.mapM (linkPolicy? templates)
  

----- Derivations -----

deriving instance Repr, DecidableEq, Inhabited for Effect
deriving instance Repr, DecidableEq, Inhabited for Scope
deriving instance Repr, DecidableEq, Inhabited for PrincipalScope
deriving instance Repr, DecidableEq, Inhabited for ResourceScope
deriving instance Repr, DecidableEq, Inhabited for ActionScope
deriving instance Repr, DecidableEq, Inhabited for Policy

deriving instance Lean.ToJson for PolicyID

end Cedar.Spec
