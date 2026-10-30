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

public import Cedar.Validation.RequestEntityValidator
import Cedar.Data.SizeOf -- `Map.sizeOf_lt_of_toList` for a termination proof

/-!
This file defines the action closure of a schema action (`Schema.actionClosure`)
and the executable side conditions under which authorization of a request on
that action depends only on the action entities in its closure:

  * `Schema.noActionLiteralsInConditions`: no policy has an action-typed entity
    literal in a `when`/`unless` body, and
  * `Schema.noActionTypedAttrs`: the schema uses no action type where an entity
    type is expected.

The corresponding theorem is
`Cedar.Validation.isAuthorized_insensitive_to_offclosure_actions`.
-/

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

/-- The action entities a schema contributes to the entity store: each action
    becomes an entity with its ancestors and empty attrs/tags. This is the Lean
    analogue of the Rust `Schema::action_entities`, built via the canonical
    `actionSchemaEntryToEntityData`. -/
public def Schema.actionEntities (s : Schema) : Entities :=
  s.acts.mapOnValues actionSchemaEntryToEntityData

/-- The transitive action closure of `uid` in `s`: `uid` together with its
    ancestor actions. In a well-formed schema `ancestors` is already transitively
    closed, so this is the set of action entities a request on `uid` can consult. -/
public def Schema.actionClosure (s : Schema) (uid : EntityUID) : Set EntityUID :=
  match s.acts.find? uid with
  | none       => Set.empty
  | some entry => Set.make (uid :: entry.ancestors.toList)

----- Action literals in policy conditions -----

/-- Every entity UID that appears as a literal anywhere in `x`. -/
public def _root_.Cedar.Spec.Expr.literalUIDs (x : Expr) : Set EntityUID :=
  match x with
  | .lit (.entityUID uid) => Set.singleton uid
  | .lit _                => Set.empty
  | .var _                => Set.empty
  | .ite x₁ x₂ x₃         => x₁.literalUIDs ∪ x₂.literalUIDs ∪ x₃.literalUIDs
  | .and x₁ x₂            => x₁.literalUIDs ∪ x₂.literalUIDs
  | .or x₁ x₂             => x₁.literalUIDs ∪ x₂.literalUIDs
  | .unaryApp _ x         => x.literalUIDs
  | .binaryApp _ x₁ x₂    => x₁.literalUIDs ∪ x₂.literalUIDs
  | .getAttr x _          => x.literalUIDs
  | .hasAttr x _          => x.literalUIDs
  | .extHasAttr x _ _     => x.literalUIDs
  | .set xs               => xs.mapUnion₁ (λ ⟨x, _⟩ => x.literalUIDs)
  | .record axs           => axs.mapUnion₂ (λ ⟨⟨_, x⟩, _⟩ => x.literalUIDs)
  | .call _ xs            => xs.mapUnion₁ (λ ⟨x, _⟩ => x.literalUIDs)
termination_by sizeOf x
decreasing_by
  any_goals
    simp
    try simp at *
    try omega
  all_goals
    rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp at *
    omega

/-- Entity UID literals in a policy's `when`/`unless` bodies. The scope is
    deliberately excluded: `action == A` and `action in A` only read the request
    action's own entity data, which every action TC store carries. -/
public def _root_.Cedar.Spec.Policy.conditionLiteralUIDs (p : Policy) : Set EntityUID :=
  p.condition.mapUnion (·.body.literalUIDs)

/-- Executable check: no policy has an action-typed entity literal in a
    `when`/`unless` body. Action types are the types of the actions declared in
    `s`. A literal such as `Action::"x" in Action::"y"` in a condition reads the
    entity data of actions outside the request action's closure, which the
    action TC store omits, so it is ruled out. -/
public def Schema.noActionLiteralsInConditions (s : Schema) (policies : Policies) : Bool :=
  policies.all λ p => p.conditionLiteralUIDs.toList.all λ uid => !s.acts.actionType? uid.ty

----- Action-typed attributes -----

/-- `true` iff every entity type mentioned anywhere in `ty` (including inside
    nested sets and records) satisfies `ok`. -/
public def CedarType.entityTypesAll (ok : EntityType → Bool) (ty : CedarType) : Bool :=
  match ty with
  | .bool _     => true
  | .int        => true
  | .string     => true
  | .entity ety => ok ety
  | .set ty     => ty.entityTypesAll ok
  | .record rty =>
    rty.toList.attach.all λ ⟨(_, qty), _⟩ =>
      match qty with
      | .optional ty => ty.entityTypesAll ok
      | .required ty => ty.entityTypesAll ok
  | .ext _      => true
termination_by sizeOf ty
decreasing_by
  any_goals simp
  all_goals
    rename_i hmem
    have h₁ := List.sizeOf_lt_of_mem hmem
    have h₂ := Map.sizeOf_lt_of_toList rty
    simp only [Prod.mk.sizeOf_spec, Qualified.optional.sizeOf_spec,
      Qualified.required.sizeOf_spec] at h₁
    omega

/-- `true` iff every entity type mentioned in the attribute types of `rty` is a
    declared entity type of `s` (so not an action type). -/
public def Schema.recordMentionsNoActionTypes (s : Schema) (rty : RecordType) : Bool :=
  (CedarType.record rty).entityTypesAll s.ets.contains

/--
Executable check: no action type is used where the schema expects an entity
type. Specifically, every entity type mentioned in an entity attribute, entity
tag, or action context type (at any depth), and every `appliesTo` principal and
resource type, must be a declared entity type in `s.ets`. Action types never are
(`ActionSchema.validateWellFormed` rejects an action type in `s.ets`).

Schemas that come from the Rust implementation are expected to always pass this
check: the Rust schema parser rejects an action type used as an attribute type,
since action types are not declared entity types there. The Lean model is
looser: `EntityType.validateWellFormed` accepts any type that is the type of a
declared action, and that check also applies to attribute, tag, context, and
`appliesTo` types. Without this check, an action UID can reach evaluation as a
value (an attribute, or the request principal or resource) instead of as a
literal, and the evaluator then reads entity data outside the request action's
closure. So `Schema.noActionLiteralsInConditions` alone is not enough.

Two counterexamples in the Lean model show this. In each one every check
passes, yet the full store and the action TC store disagree. Run them
with `lake env lean <file>` from `cedar-lean`.

Counterexample 1, an action-typed context field:

```lean
import Cedar.Spec
import Cedar.Validation.Validator
import Cedar.Validation.EnvironmentValidator
import Cedar.Validation.RequestEntityValidator
import Cedar.Validation.Decompose

open Cedar.Spec Cedar.Data Cedar.Validation

def userTy   : EntityType := ⟨"User", []⟩
def actionTy : EntityType := ⟨"Action", []⟩
def act (s : String) : EntityUID := ⟨actionTy, s⟩

-- Action `view` has context { a: Action, b: Action }. Actions x in y.
def schema : Schema := {
  ets := Map.make [(userTy, .standard ⟨Set.empty, Map.empty, none⟩)],
  acts := Map.make [
    (act "view", ⟨Set.singleton userTy, Set.singleton userTy, Set.empty,
                  Map.make [("a", .required (.entity actionTy)),
                            ("b", .required (.entity actionTy))]⟩),
    (act "x", ⟨Set.empty, Set.empty, Set.singleton (act "y"), Map.empty⟩),
    (act "y", ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩)]
}

-- permit(principal, action, resource) when { context.a in context.b };
def policy : Policy := {
  id := "p0", effect := .permit,
  principalScope := .principalScope .any,
  actionScope := .actionScope .any,
  resourceScope := .resourceScope .any,
  condition := [⟨.when, .binaryApp .mem (.getAttr (.var .context) "a")
                                         (.getAttr (.var .context) "b")⟩]
}

def req : Request := {
  principal := ⟨userTy, "alice"⟩, action := act "view", resource := ⟨userTy, "doc"⟩,
  context := Map.make [("a", .prim (.entityUID (act "x"))),
                       ("b", .prim (.entityUID (act "y")))]
}

def users : List (EntityUID × EntityData) :=
  [(⟨userTy, "alice"⟩, ⟨Map.empty, Set.empty, Map.empty⟩),
   (⟨userTy, "doc"⟩,   ⟨Map.empty, Set.empty, Map.empty⟩)]

def fullStore : Entities := Map.make (users ++ schema.actionEntities.toList)

-- What the action TC store for `view` gives authz: only `view`'s closure.
def actionTcStore : Entities :=
  Map.make (users ++ schema.actionEntities.toList.filter
    (λ (u, _) => (schema.actionClosure (act "view")).contains u))

def showOk {ε} : Except ε Unit → String
  | .ok () => "ok" | .error _ => "error"

def showDecision : Decision → String
  | .allow => "allow" | .deny => "deny"

#eval s!"schema.validateWellFormed      = {showOk schema.validateWellFormed}"
#eval s!"validate [policy] schema       = {showOk (validate [policy] schema)}"
#eval s!"validateRequest                = {showOk (validateRequest schema req)}"
#eval s!"validateEntities (full store)  = {showOk (validateEntities schema fullStore)}"
#eval s!"noActionLiteralsInConditions   = {schema.noActionLiteralsInConditions [policy]}"
#eval s!"isAuthorized (full store)      = {showDecision (isAuthorized req fullStore [policy]).decision}"
#eval s!"isAuthorized (action TC store) = {showDecision (isAuthorized req actionTcStore [policy]).decision}"
```

Output:

```
schema.validateWellFormed      = ok
validate [policy] schema       = ok
validateRequest                = ok
validateEntities (full store)  = ok
noActionLiteralsInConditions   = true
isAuthorized (full store)      = allow
isAuthorized (action TC store) = deny
```

The full store allows because `Action::"x" in Action::"y"`. The action TC store for
`view` carries only `view`'s closure, so it has no entity data for `x` and
denies. `schema.noActionTypedAttrs` returns `false` for this schema.

Counterexample 2, an action type in `appliesTo`. Same imports and helpers
(`userTy`, `actionTy`, `act`, `showOk`, `showDecision`) as above:

```lean
-- Action `view` applies to principal: Action. Actions x in y.
def schema : Schema := {
  ets := Map.make [(userTy, .standard ⟨Set.empty, Map.empty, none⟩)],
  acts := Map.make [
    (act "view", ⟨Set.singleton actionTy, Set.singleton userTy, Set.empty, Map.empty⟩),
    (act "x", ⟨Set.empty, Set.empty, Set.singleton (act "y"), Map.empty⟩),
    (act "y", ⟨Set.empty, Set.empty, Set.empty, Map.empty⟩)]
}

-- permit(principal in Action::"y", action, resource);
def policy : Policy := {
  id := "p0", effect := .permit,
  principalScope := .principalScope (.mem (act "y")),
  actionScope := .actionScope .any, resourceScope := .resourceScope .any, condition := [] }

def req : Request :=
  { principal := act "x", action := act "view", resource := ⟨userTy, "doc"⟩, context := Map.empty }

def users : List (EntityUID × EntityData) := [(⟨userTy, "doc"⟩, ⟨Map.empty, Set.empty, Map.empty⟩)]
def fullStore : Entities := Map.make (users ++ schema.actionEntities.toList)
def actionTcStore : Entities := Map.make (users ++ schema.actionEntities.toList.filter
    (λ (u, _) => (schema.actionClosure (act "view")).contains u))

#eval s!"wf={showOk schema.validateWellFormed} validate={showOk (validate [policy] schema)} req={showOk (validateRequest schema req)} ents={showOk (validateEntities schema fullStore)}"
#eval s!"noLits={schema.noActionLiteralsInConditions [policy]}"
#eval s!"full={showDecision (isAuthorized req fullStore [policy]).decision} actionTc={showDecision (isAuthorized req actionTcStore [policy]).decision}"
```

Output:

```
wf=ok validate=ok req=ok ents=ok
noLits=true
full=allow actionTc=deny
```

The policy's only action literal is in the principal scope, which
`noActionLiteralsInConditions` allows. It is harmless when the principal is a
real entity, but here the principal is the action `x`, so `principal in
Action::"y"` reads `x`'s entity data, which the action TC store for `view` omits.
`schema.noActionTypedAttrs` returns `false` for this schema.
-/
public def Schema.noActionTypedAttrs (s : Schema) : Bool :=
  s.ets.values.all (λ entry =>
    s.recordMentionsNoActionTypes entry.attrs &&
    (entry.tags?.map (·.entityTypesAll s.ets.contains)).getD true) &&
  s.acts.values.all (λ entry =>
    s.recordMentionsNoActionTypes entry.context &&
    entry.appliesToPrincipal.toList.all s.ets.contains &&
    entry.appliesToResource.toList.all s.ets.contains)

end Cedar.Validation
