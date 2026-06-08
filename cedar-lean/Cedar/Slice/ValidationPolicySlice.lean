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

import Cedar.Spec
import Cedar.Validation

/-!
This file defines a validation-focused policy slicing algorithm.

Given two schemas that differ only in certain actions' definitions, we identify
which policies need to be revalidated. The permissible changes that allow
incremental revalidation are:
- Any change to an action's context type
- Extension of an action's appliesTo list (new principal/resource types added)

Changes that require a full revalidation of all policies:
- Any change to the entity schema (entity types, attributes, ancestors)
- Any change to action hierarchy membership (ancestors field)

Changes that do NOT require revalidation:
- Truncation of an action's appliesTo list (types removed)

Key insight for appliesTo changes:
- If the appliesTo list is *extended* (new principal/resource types added), the
  policy must be revalidated because there are new environments to check.
- If the appliesTo list is *truncated* (types removed), no revalidation is
  needed: the new schema's environments for that action are a subset of the old
  schema's environments, so if validation passed before, it still passes.
- Context changes always require revalidation of policies matching that action.

A policy only needs revalidation if its action scope matches a changed action.
-/

namespace Cedar.Slice

open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/--
Describes how an action's schema entry has changed between two schemas.
Only changes that could potentially invalidate a policy are tracked here.
-/
inductive ActionChange where
  | contextChanged (action : EntityUID)
  | appliesToExtended (action : EntityUID)
deriving Repr, DecidableEq

def ActionChange.action : ActionChange → EntityUID
  | .contextChanged a => a
  | .appliesToExtended a => a

/--
Checks whether a full revalidation is required (as opposed to incremental).
A full revalidation is needed when:
1. The entity schema has changed (entity types, attributes, ancestors)
2. Any action's hierarchy membership (ancestors) has changed

Returns `true` if a full revalidation is required.
-/
def requiresFullRevalidation (oldSchema newSchema : Schema) : Bool :=
  oldSchema.ets != newSchema.ets ||
  oldSchema.acts.toList.any (fun (action, oldEntry) =>
    match newSchema.acts.find? action with
    | none => true
    | some newEntry => oldEntry.ancestors != newEntry.ancestors) ||
  newSchema.acts.toList.any (fun (action, _) =>
    !(oldSchema.acts.contains action))

/--
Determines whether a policy's action scope could possibly match a given action,
considering the action hierarchy defined in the schema.
-/
def actionScopeMatchesAction (acts : ActionSchema) (action : EntityUID) (scope : ActionScope) : Bool :=
  match scope with
  | .actionScope .any => true
  | .actionScope (.eq uid) => uid == action || acts.descendentOf action uid
  | .actionScope (.mem uid) => acts.descendentOf action uid
  | .actionScope (.is ety) => action.ty == ety
  | .actionScope (.isMem ety uid) => action.ty == ety && acts.descendentOf action uid
  | .actionInAny ls => ls.any (fun listedAction => acts.descendentOf action listedAction)

/--
Determines whether a policy's action scope matches any of the changed actions.
-/
def actionScopeMatchesAnyChangedAction (acts : ActionSchema) (changes : List ActionChange) (scope : ActionScope) : Bool :=
  changes.any (fun change => actionScopeMatchesAction acts change.action scope)

/--
Given a list of action changes, return the subset of policies whose
well-typedness could potentially be affected and therefore need revalidation.

This function should only be used when `requiresFullRevalidation` returns false.
When a full revalidation is required, all policies must be rechecked.

A policy is included in the slice if its action scope could match a changed
action. Policies with unconstrained action scopes (`action scope == any`) are
always included when any action has changed.
-/
def validationSlice (acts : ActionSchema) (changes : List ActionChange) (policies : Policies) : Policies :=
  policies.filter (fun policy => actionScopeMatchesAnyChangedAction acts changes policy.actionScope)

/--
Compute the list of action changes between two schemas. An action is considered
changed if its context type differs or if its appliesTo sets have been extended
(new types added). Actions whose appliesTo sets have only been truncated are not
included (validation result is preserved by monotonicity).

Precondition: `requiresFullRevalidation oldSchema newSchema = false` (the entity
schema is unchanged and action hierarchy is unchanged).
-/
def computeActionChanges (oldSchema newSchema : Schema) : List ActionChange :=
  newSchema.acts.toList.filterMap fun (action, newEntry) =>
    match oldSchema.acts.find? action with
    | none => some (.contextChanged action)
    | some oldEntry =>
      if oldEntry.context != newEntry.context then
        some (.contextChanged action)
      else if !(newEntry.appliesToPrincipal.subset oldEntry.appliesToPrincipal) ||
              !(newEntry.appliesToResource.subset oldEntry.appliesToResource) then
        some (.appliesToExtended action)
      else
        none

end Cedar.Slice
