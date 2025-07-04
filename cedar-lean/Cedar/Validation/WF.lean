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

inductive EnvironmentValidationError where
| typeError (msg : String)

abbrev EnvironmentValidationResult := Except EnvironmentValidationError Unit

def EntitySchema.wellFormed (env : Environment) (ets : EntitySchema) : EnvironmentValidationResult :=
  sorry

def ActionSchema.wellFormed (env : Environment) (acts : ActionSchema) : EnvironmentValidationResult :=
  do
    if Data.Map.wellFormed acts then .ok ()
    else
      .error (.typeError s!"action schema is not a well-formed map")
    sorry

def RequestType.wellFormed (env : Environment) (reqty : RequestType) : EnvironmentValidationResult :=
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

def Environment.wellFormed (env : Environment) : EnvironmentValidationResult := do
  env.ets.wellFormed env
  env.acts.wellFormed env
  env.reqty.wellFormed env

-- TODO: Can be optimized, as `Environment.wellFormed`
--       mostly only depends on the schema part of the environment.
def Schema.wellFormed (schema : Schema) : EnvironmentValidationResult :=
  schema.environments.forM Environment.wellFormed

end Cedar.Validation
