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
This file contains the executable version of `TypeEnv.WellFormed`
and related definitions.
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Validation
open Cedar.Spec

inductive EnvironmentValidationError where
| typeError (msg : String)

instance : ToString EnvironmentValidationError where
  toString err :=
    match err with
    | .typeError msg => s!"type error: {msg}"

abbrev EnvironmentValidationResult := Except EnvironmentValidationError Unit

def EntityType.validateWellFormed (env : TypeEnv) (ety : EntityType) : EnvironmentValidationResult :=
  if env.ets.contains ety then .ok ()
  else if env.acts.toList.any λ (uid, _) => uid.ty == ety then .ok ()
  else .error (.typeError s!"entity type {ety} is not defined in the schema")

mutual

def QualifiedType.validateWellFormed (env : TypeEnv) (qty : QualifiedType) : EnvironmentValidationResult :=
  match qty with
  | .optional ty => ty.validateWellFormed env
  | .required ty => ty.validateWellFormed env

def validateAttrsWellFormed (env : TypeEnv) (rty : List (Attr × QualifiedType)) : EnvironmentValidationResult :=
  match rty with
  | [] => .ok ()
  | (_, qty) :: rest => do
    qty.validateWellFormed env
    validateAttrsWellFormed env rest

def CedarType.validateWellFormed (env : TypeEnv) (ty : CedarType) : EnvironmentValidationResult :=
  match ty with
  | .bool _ => .ok ()
  | .int => .ok ()
  | .string => .ok ()
  | .entity ety => EntityType.validateWellFormed env ety
  | .set ty => ty.validateWellFormed env
  | .record rty => do
    if rty.wellFormed then .ok ()
    else .error (.typeError s!"record type is not a well-formed map")
    -- Check each attribute type
    validateAttrsWellFormed env rty.toList
  | .ext _ => .ok ()

end

def CedarType.validateLifted (ty : CedarType) : EnvironmentValidationResult :=
  match ty with
  | .bool .anyBool => .ok ()
  | .bool _ => .error (.typeError s!"bool type is not lifted")
  | .int => .ok ()
  | .string => .ok ()
  | .entity _ => .ok ()
  | .set ty => ty.validateLifted
  | .record rty =>
    rty.toList.attach.forM λ ⟨(_, qty), _⟩ =>
      match qty with
      | .optional ty => ty.validateLifted
      | .required ty => ty.validateLifted
  | .ext _ => .ok ()
termination_by sizeOf ty
decreasing_by
  any_goals simp
  any_goals
    rename_i hmem
    have h := List.sizeOf_lt_of_mem hmem
    cases rty
    simp [Map.toList, Map.kvs] at h ⊢
    omega

def StandardSchemaEntry.validateWellFormed (env : TypeEnv) (entry : StandardSchemaEntry) : EnvironmentValidationResult :=
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
    (CedarType.record entry.attrs).validateLifted
    -- The tag type is well-formed
    match entry.tags with
    | .some ty => do
      ty.validateWellFormed env
      ty.validateLifted
    | .none => .ok ()

def EntitySchemaEntry.validateWellFormed (env : TypeEnv) (entry : EntitySchemaEntry) : EnvironmentValidationResult :=
  match entry with
  | .standard entry => entry.validateWellFormed env
  | .enum es => do
    if es.wellFormed then .ok ()
    else .error (.typeError s!"enum entity is not well-formed")
    if es.isEmpty then .error (.typeError s!"enum entity is empty")
    else .ok ()

def EntitySchema.validateWellFormed (env : TypeEnv) (ets : EntitySchema) : EnvironmentValidationResult :=
  do
    if Map.wellFormed ets then .ok ()
    else .error (.typeError s!"entity schema is not a well-formed map")
    ets.toList.forM λ (_, entry) =>
      entry.validateWellFormed env

def ActionSchemaEntry.validateWellFormed (env : TypeEnv) (entry : ActionSchemaEntry) : EnvironmentValidationResult :=
  do
    if entry.appliesToPrincipal.wellFormed then .ok ()
    else .error (.typeError s!"appliesToPrincipal set is not well-formed")
    if entry.appliesToResource.wellFormed then .ok ()
    else .error (.typeError s!"appliesToResource set is not well-formed")
    if entry.ancestors.wellFormed then .ok ()
    else .error (.typeError s!"ancestors set is not well-formed")
    -- Every appliesTo entity types are well-formed
    entry.appliesToPrincipal.toList.forM (EntityType.validateWellFormed env)
    entry.appliesToResource.toList.forM (EntityType.validateWellFormed env)
    -- Ancestors of an action should be actions
    entry.ancestors.toList.forM λ uid =>
      if env.acts.contains uid then .ok ()
      else .error (.typeError s!"non-action ancestor {uid}")
    -- Check that the context type is well-formed
    (CedarType.record entry.context).validateWellFormed env
    (CedarType.record entry.context).validateLifted

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

def ActionSchema.validateWellFormed (env : TypeEnv) (acts : ActionSchema) : EnvironmentValidationResult :=
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

def ActionSignature.validateWellFormed (env : TypeEnv) (sig : ActionSignature) : EnvironmentValidationResult :=
  match env.acts.find? sig.action with
  | some entry => do
    if entry.appliesToPrincipal.contains sig.principal then .ok ()
    else
      .error (.typeError s!"action {sig.action} does not apply to principal {sig.principal}")
    if entry.appliesToResource.contains sig.resource then .ok ()
    else
      .error (.typeError s!"action {sig.action} does not apply to resource {sig.resource}")
    if sig.context == entry.context then .ok ()
    else
      .error (.typeError s!"action {sig.action} context type does not match schema")
  | none => .error (.typeError s!"action {sig.action} does not exist in schema")

def TypeEnv.validateWellFormed (env : TypeEnv) : EnvironmentValidationResult := do
  env.ets.validateWellFormed env
  env.acts.validateWellFormed env
  env.sig.validateWellFormed env

-- TODO: Can be optimized, as `TypeEnv.validateWellFormed`
--       mostly only depends on the schema part of the environment.
def Schema.validateWellFormed (schema : Schema) : EnvironmentValidationResult :=
  schema.environments.forM TypeEnv.validateWellFormed

end Cedar.Validation
