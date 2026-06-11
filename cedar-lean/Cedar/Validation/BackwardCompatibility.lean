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
import Cedar.Validation.EnvironmentValidator

/-!
# Backward Compatibility Checks for Schema Changes

Executable functions that determine whether a schema change is backward-compatible
(i.e., cannot break policy validation).
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

private instance : DecidableEq ActionSchemaEntry := by
  intro a b; cases a; cases b
  simp only [ActionSchemaEntry.mk.injEq]; exact inferInstance

/--
Decidable check that `schema₂` is a backward-compatible entity-schema extension
of `schema₁`. Returns `true` when:
- The action schemas are identical
- Every entity type entry in `schema₁` has the same entry in `schema₂`
- No action uid's entity type collides with `schema₂.ets`
-/
def isValidEtsExtension (schema₁ schema₂ : Schema) : Bool :=
  (schema₁.acts.toList == schema₂.acts.toList) &&
  schema₁.ets.toList.all (fun (ety, entry) => schema₂.ets.find? ety == some entry) &&
  schema₂.acts.toList.all (fun (uid, _) => !schema₂.ets.contains uid.ty)

/--
Check that `newSchema` is an "appliesTo restriction" of `oldSchema`: same entity
types, and for each action, the context and ancestors are unchanged and the
appliesTo sets have only shrunk (new ⊆ old).
-/
def isAppliesToRestriction (oldSchema newSchema : Schema) : Bool :=
  (oldSchema.ets.toList == newSchema.ets.toList) &&
  oldSchema.acts.toList.all (fun (action, oldEntry) =>
    match newSchema.acts.find? action with
    | none => false
    | some newEntry => decide (oldEntry.ancestors = newEntry.ancestors)) &&
  newSchema.acts.toList.all (fun (action, newEntry) =>
    match oldSchema.acts.find? action with
    | none => false
    | some oldEntry =>
      decide (oldEntry.context = newEntry.context) &&
      newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal &&
      newEntry.appliesToResource.subset oldEntry.appliesToResource &&
      newEntry.appliesToPrincipal.wellFormed &&
      newEntry.appliesToResource.wellFormed) &&
  newSchema.acts.wellFormed

/--
Combined backward-compatibility check: `schema₃` extends entity types from
`schema₁` AND restricts appliesTo sets. Validates via an intermediate schema
that has the new entity types but the old action schema.
-/
def isBackwardCompatible (schema₁ schema₃ : Schema) : Bool :=
  let schema₂ : Schema := { ets := schema₃.ets, acts := schema₁.acts }
  isValidEtsExtension schema₁ schema₂ &&
  isAppliesToRestriction schema₂ schema₃ &&
  schema₁.acts.wellFormed

end Cedar.Validation
