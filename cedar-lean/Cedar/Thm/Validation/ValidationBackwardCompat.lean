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

import Cedar.Thm.Validation.ValidationBackwardCompat.EtsExtension
import Cedar.Thm.Validation.ValidationBackwardCompat.AppliesToRestriction

/-!
# Backward Compatibility for Cedar Schema Changes

This module proves that certain schema changes cannot break policy validation:

## 1. Entity Schema Extension (`validate_of_isValidEtsExtension`)

Adding new entity types to the entity schema never invalidates existing policies.
The executable check `isValidEtsExtension` determines whether a schema change
qualifies.

## 2. AppliesTo Restriction (`validateOrImpossible_of_appliesTo_restriction`)

Removing items from `appliesToPrincipal`/`appliesToResource` on actions cannot
introduce new type errors. Policies may become "impossible" (all environments
produce `.bool .ff`) but cannot acquire type errors. The executable check
`isAppliesToRestriction` determines whether a schema change qualifies.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

/--
**Executable backward compatibility for entity schema extension**: if
`isValidEtsExtension schema₁ schema₂` returns `true` (same actions, all old
entity type entries preserved, action/entity disjointness) and `schema₁` is
well-formed, then policies validated against `schema₁` also validate against
`schema₂`.
-/
theorem validate_of_isValidEtsExtension
    (schema₁ schema₂ : Schema)
    (policies : Policies)
    (hext : isValidEtsExtension schema₁ schema₂ = true)
    (hwf₁ : schema₁.validateWellFormed = .ok ())
    (hold : validate policies schema₁ = .ok ()) :
    validate policies schema₂ = .ok () :=
  validate_of_isValidEtsExtension' schema₁ schema₂ policies hext hwf₁ hold

/--
**Executable backward compatibility for appliesTo restriction**: if
`isAppliesToRestriction oldSchema newSchema` returns `true` (same entity types,
same action hierarchy, appliesTo only shrunk, well-formed new acts) and `oldSchema`
is well-formed, then `validateOrImpossible` passes on `newSchema`.

Policies may become "impossible" when appliesTo entries are removed, but cannot
acquire new type errors.
-/
theorem validateOrImpossible_of_appliesTo_restriction
    (oldSchema newSchema : Schema)
    (policies : Policies)
    (hrestr : isAppliesToRestriction oldSchema newSchema = true)
    (hwf₁ : Schema.validateWellFormed oldSchema = .ok ())
    (hold : validate policies oldSchema = .ok ()) :
    Cedar.Slice.validateOrImpossible policies newSchema = true :=
  validateOrImpossible_of_appliesTo_restriction' oldSchema newSchema policies hrestr hwf₁ hold

end Cedar.Thm
