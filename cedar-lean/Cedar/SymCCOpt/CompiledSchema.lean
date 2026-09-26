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

public import Cedar.Validation.Types
public import Cedar.SymCC.Env

namespace Cedar.SymCC

open Cedar.Validation
open Cedar.Spec

/--
Represents a schema compiled into a symbolic representation of its entity types,
stored together with the original schema. Building `SymEntities` is expensive
but only depends on the schema (and not specific request type), so this
structure avoids repeating that work on multiple solver queriers using the same
schema.
-/
public structure CompiledSchema where
  schema : Schema
  entities : SymEntities
deriving Repr, Inhabited

public def CompiledSchema.compile (schema : Schema) : CompiledSchema :=
  ⟨ schema, SymEntities.ofSchema schema.ets schema.acts ⟩

public def CompiledSchema.symEnv (schema : CompiledSchema) (reqty : RequestType) : SymEnv :=
  ⟨ SymRequest.ofRequestType reqty, schema.entities ⟩

public def CompiledSchema.typeEnv (schema : CompiledSchema) (reqty : RequestType) : TypeEnv :=
  ⟨ schema.schema.ets, schema.schema.acts, reqty ⟩
