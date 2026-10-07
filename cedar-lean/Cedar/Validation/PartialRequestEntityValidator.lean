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

module

public import Cedar.Validation.PartialSchema
public import Cedar.Validation.RequestEntityValidator

/-!
This file validates requests and entity stores against partial schemas.
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

----- Views of Schema, for validation -----

def PartialEntitySchemaEntry.validationView : PartialEntitySchemaEntry → EntitySchemaEntry
  | .defined entry => entry
  | .external ancestors => .standard {
      ancestors,
      attrs := Map.empty,
      tags := none
    }

def PartialActionSchemaEntry.validationView : PartialActionSchemaEntry → ActionSchemaEntry
  | .defined entry => entry
  | .external ancestors => {
      appliesToPrincipal := Set.empty,
      appliesToResource := Set.empty,
      ancestors,
      context := Map.empty
    }

def PartialSchema.validationView (ps : PartialSchema) : Schema := {
  ets := ps.ets.mapOnValues PartialEntitySchemaEntry.validationView,
  acts := ps.acts.mapOnValues PartialActionSchemaEntry.validationView
}

----- Validation -----

public def PartialSchema.validateRequest
    (ps : PartialSchema)
    (request : Request) : RequestValidationResult :=
  Cedar.Validation.validateRequest ps.validationView request

/--
Validate, treating external schema as empty schema declarations.
Does validate actions with external type.
Does NOT validate entities with external type.
-/
public def PartialSchema.validateEntities
    (ps : PartialSchema)
    (entities : Entities) : EntityValidationResult :=
  let schema := ps.validationView
  let env : TypeEnv := {
    ets := schema.ets,
    acts := schema.acts,
    reqty := default
  }
  entities.toList.forM λ (uid, data) =>
    match ps.ets.find? uid.ty with
    | some (.external _) =>
      .error (.typeError s!"entity {uid} has an external type and cannot be validated")
    | _ => instanceOfSchema.instanceOfSchemaEntry env uid data

end Cedar.Validation
