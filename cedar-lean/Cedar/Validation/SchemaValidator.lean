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

import Cedar.Validation.Validator
import Cedar.Validation.Typechecker

/-!
This file contains the executable version of `Environment.WellFormed`
and related definitions.
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Validation
open Cedar.Spec

inductive EnvironmentValidationError where
| typeError (msg : String)

abbrev EnvironmentValidationResult := Except EnvironmentValidationError Unit

def Cedar.Spec.EntityType.validateWellFormed (env : Environment) (ety : EntityType) : EnvironmentValidationResult :=
  if env.ets.contains ety then .ok ()
  else if env.acts.toList.any λ (uid, _) => uid.ty == ety then .ok ()
  else .error (.typeError s!"entity type {ety} is not defined in the schema")

mutual

def validateAttrsWellFormed (env : Environment) (rty : List (Attr × QualifiedType)) : EnvironmentValidationResult :=
  match rty with
  | [] => .ok ()
  | (_, qty) :: rest => do
    match qty with
    | .optional ty => ty.validateWellFormed env
    | .required ty => ty.validateWellFormed env
    validateAttrsWellFormed env rest

def CedarType.validateWellFormed (env : Environment) (ty : CedarType) : EnvironmentValidationResult :=
  match ty with
  | .bool _ => .ok ()
  | .int => .ok ()
  | .string => .ok ()
  | .entity ety => ety.validateWellFormed env
  | .set ty => ty.validateWellFormed env
  | .record rty => do
    if rty.wellFormed then .ok ()
    else .error (.typeError s!"record type is not a well-formed map")
    -- Check each attribute type
    validateAttrsWellFormed env rty.toList
  | .ext _ => .ok ()

end

def StandardSchemaEntry.validateWellFormed (env : Environment) (entry : StandardSchemaEntry) : EnvironmentValidationResult :=
  do
    if entry.ancestors.wellFormed then .ok ()
    else .error (.typeError s!"ancestors set is not well-formed")
    -- Every ancestor is a valid entity type (and non-enum)
    entry.ancestors.toList.forM λ ety => do
      match env.ets.find? ety with
      | some entry =>
        if entry.isStandard then .ok ()
        else .error (.typeError s!"ancestor entity type {ety} is not a standard entity")
      | none => .error (.typeError s!"ancestor entity type {ety} does not exist")
    -- Attribute types should be well-formed
    (CedarType.record entry.attrs).validateWellFormed env
    -- The tag type is well-formed
    match entry.tags with
    | .some ty => ty.validateWellFormed env
    | .none => .ok ()

def EntitySchemaEntry.validateWellFormed (env : Environment) (entry : EntitySchemaEntry) : EnvironmentValidationResult :=
  match entry with
  | .standard entry => entry.validateWellFormed env
  | .enum es => do
    if es.wellFormed then .ok ()
    else .error (.typeError s!"enum entity is not well-formed")
    if es.isEmpty then .error (.typeError s!"enum entity is empty")
    else .ok ()

def EntitySchema.validateWellFormed (env : Environment) (ets : EntitySchema) : EnvironmentValidationResult :=
  do
    if Map.wellFormed ets then .ok ()
    else .error (.typeError s!"entity schema is not a well-formed map")
    ets.toList.forM λ (_, entry) =>
      entry.validateWellFormed env

def ActionSchemaEntry.validateWellFormed (env : Environment) (entry : ActionSchemaEntry) : EnvironmentValidationResult :=
  do
    if entry.appliesToPrincipal.wellFormed then .ok ()
    else .error (.typeError s!"appliesToPrincipal set is not well-formed")
    if entry.appliesToResource.wellFormed then .ok ()
    else .error (.typeError s!"appliesToResource set is not well-formed")
    if entry.ancestors.wellFormed then .ok ()
    else .error (.typeError s!"ancestors set is not well-formed")
    -- Every appliesTo entity types are well-formed
    entry.appliesToPrincipal.toList.forM (·.validateWellFormed env)
    entry.appliesToResource.toList.forM (·.validateWellFormed env)
    -- Ancestors of an action should be actions
    entry.ancestors.toList.forM λ uid =>
      if env.acts.contains uid then .ok ()
      else .error (.typeError s!"non-action ancestor {uid}")
    -- Check that the context type is well-formed
    (CedarType.record entry.context).validateWellFormed env

def ActionSchema.validateAcyclicActionHierarchy (acts : ActionSchema) : EnvironmentValidationResult :=
  acts.toList.forM λ (uid, entry) => do
    if entry.ancestors.contains uid then
      .error (.typeError s!"action hierarchy is cyclic at {uid}")
    else .ok ()

def ActionSchema.validateTransitiveActionHierarchy (acts : ActionSchema) : EnvironmentValidationResult :=
  acts.toList.forM λ (uid₁, entry₁) => do
    acts.toList.forM λ (uid₂, entry₂) => do
      if entry₁.ancestors.contains uid₂ then
        if entry₂.ancestors.subset entry₁.ancestors then .ok ()
        else
          .error (.typeError s!"action hierarchy is not transitive from {uid₁} to {uid₂}")
      else .ok ()

def ActionSchema.validateWellFormed (env : Environment) (acts : ActionSchema) : EnvironmentValidationResult :=
  do
    if Map.wellFormed acts then .ok ()
    else
      .error (.typeError s!"action schema is not a well-formed map")
    acts.toList.forM λ (uid, entry) => do
      if env.ets.contains uid.ty then
        .error (.typeError s!"action entity type {uid.ty} should not be in the entity schema")
      else .ok ()
      entry.validateWellFormed env
    acts.validateAcyclicActionHierarchy
    acts.validateTransitiveActionHierarchy

def RequestType.validateWellFormed (env : Environment) (reqty : RequestType) : EnvironmentValidationResult :=
  match env.acts.find? reqty.action with
  | some entry => do
    if entry.appliesToPrincipal.contains reqty.principal then .ok ()
    else
      .error (.typeError s!"action {reqty.action} does not apply to principal {reqty.principal}")
    if entry.appliesToResource.contains reqty.resource then .ok ()
    else
      .error (.typeError s!"action {reqty.action} does not apply to resource {reqty.resource}")
    if reqty.context == entry.context then .ok ()
    else
      .error (.typeError s!"action {reqty.action} context type does not match schema")
  | none => .error (.typeError s!"action {reqty.action} does not exist in schema")

def Environment.validateWellFormed (env : Environment) : EnvironmentValidationResult := do
  env.ets.validateWellFormed env
  env.acts.validateWellFormed env
  env.reqty.validateWellFormed env

-- TODO: Can be optimized, as `Environment.validateWellFormed`
--       mostly only depends on the schema part of the environment.
def Schema.validateWellFormed (schema : Schema) : EnvironmentValidationResult :=
  schema.environments.forM Environment.validateWellFormed

end Cedar.Validation
