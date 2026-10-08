# Adding External Entities to Cedar-Spec (Allow External Entity Declaration, [RFC 116](https://github.com/cedar-policy/rfcs/pull/116))

## Goal
- [RFC 116](https://github.com/cedar-policy/rfcs/pull/116) adds `external entity` and `external action` declarations to Cedar schemas. 
An external declaration names an entity type or action that some other schema defines, so a schema can be used without loading the others.

- A _partial schema_ is a schema that _may_ contain external declarations.

- A _schema_ is a _partial schema_; a partial schema with no external declaration is a schema.

- Add _schema linking_. Linking two partial schemas gives another partial schema or fails.

- A partial schema can validate entities and requests.

- Only a complete schema can validate policies, use TPE or run SymCC.

- A partial schema can validate entities of types that are not external, but refer to external entities without assuming any structure of the external entities (other than ancestor relations).

- A partial schema cannot validate any normal external entity, because such an external entity necessarily assumes structure about the external entity type.

- [Diverge from the RFC (decision 9)](#decision-9)
 A partial schema can validate an external action's entity.

- Once every external is linked, the combined schema behaves as if the externals were never declared.


## Examples

### Well-formed partial schemas
A partial schema must declare every entity type and action it refers to, either as a definition or as an external. This catches typos before any linking (RFC, ["Motivation"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#motivation) and ["Alternatives"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#alternatives)).

<table>
<tr><th>Schema</th><th>Validity</th></tr>
<tr>
<td>

```cedar
external entity B;
entity A { b: B };
```

</td>
<td>

Valid

</td>
</tr>
<tr>
<td>

```cedar
external entity G;
external entity F in G;
entity A in F;
```

</td>
<td>

Valid

</td>
</tr>
<tr>
<td>

```cedar
external entity User;
external action g;
action a in g
  appliesTo {
    principal: User,
    resource: User,
  };
```

</td>
<td>

Valid

</td>
</tr>
<tr>
<td>

```cedar
external action b in a;
action a in b;
```

</td>
<td>

Error: `actionHierarchyCycle`

</td>
</tr>
<tr>
<td>

```cedar
external entity A;
entity A;
```

</td>
<td>

Error: duplicate declaration (Rust parser)

</td>
</tr>
</table>

- The second and third rows show that externals may have external parents, and may appear in `appliesTo`.
- A schema can't declare a name both as a definition and as an external. Rust rejects this when parsing, as it rejects duplicate declarations today; a `PartialSchema` holds one entry per name, so Lean never sees it.

### Linking
Each example links a partial schema `P` with a partial schema `C`, and shows the result in Cedar syntax.

<a id="example-1"></a>**1. Entity: partial + complete = complete.** `P` refers to the external `B`, and `C` defines it.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity B;
entity A { b: B };
```

</td>
<td>

```cedar
entity B;
```

</td>
<td>

```cedar
entity A { b: B };
entity B;
```

</td>
</tr>
</table>

<a id="example-2"></a>**2. Action: an external action links to a definition with an `appliesTo`.** `P` declares the action `write` as external, and `C` defines it. An external action declares only its parents (here none), and its definition supplies the `appliesTo` and context (RFC, ["External actions"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#external-actions)). `C` refers to `User` and `Doc`, so it declares them as external.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
entity User;
entity Doc;
external action write;
```

</td>
<td>

```cedar
external entity User;
external entity Doc;
action write
  appliesTo {
    principal: User,
    resource: Doc,
  };
```

</td>
<td>

```cedar
entity User;
entity Doc;
action write
  appliesTo {
    principal: User,
    resource: Doc,
  };
```

</td>
</tr>
</table>

- Against `P`, every request for `write` is invalid, because its `appliesTo` is unknown.
- Against `link P C`, a request for `write` with a `User` principal and a `Doc` resource is valid.

<a id="example-3"></a>**3. Partial + partial = partial.** Both schemas declare `B` as external and neither defines it, so `B` stays unresolved.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity B;
entity A { b: B };
```

</td>
<td>

```cedar
external entity B;
entity D { b: B };
```

</td>
<td>

```cedar
external entity B;
entity A { b: B };
entity D { b: B };
```

</td>
</tr>
</table>

<a id="example-4"></a>**4. Mutual externals: partial + partial = complete.** Each schema defines what the other declares as external.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity B;
entity A { b: B };
```

</td>
<td>

```cedar
external entity A;
entity B { a: A };
```

</td>
<td>

```cedar
entity A { b: B };
entity B { a: A };
```

</td>
</tr>
</table>

<a id="example-5"></a>**5. Ancestors through an external.** Against `P` alone, `A`'s ancestors are already `F` and `G`, through `F`'s declared parent. The link keeps them.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity G;
external entity F in G;
entity A in F;
```

</td>
<td>

```cedar
entity G;
entity F in G;
```

</td>
<td>

```cedar
entity G;
entity F in G;
entity A in F;
```

</td>
</tr>
</table>

<a id="example-6"></a>**6. Repeated externals combine their declared parents.** `F` is still unresolved, with the parents from both declarations.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity G;
external entity F in G;
```

</td>
<td>

```cedar
external entity H;
external entity F in H;
```

</td>
<td>

```cedar
external entity G;
external entity H;
external entity F in [G, H];
```

</td>
</tr>
</table>

<a id="example-7"></a>**7. A definition may add parents.** `F`'s definition has `H` as well as the declared `G`.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity G;
external entity F in G;
```

</td>
<td>

```cedar
entity G;
entity H;
entity F in [G, H];
```

</td>
<td>

```cedar
entity G;
entity H;
entity F in [G, H];
```

</td>
</tr>
</table>

<a id="example-8"></a>**8. Error: a cross-schema cycle would enlarge defined ancestors.** `P` and `C` are each closed, but linking them would add `A` to `A`'s ancestor set and `B` to `B`'s. A successful link does not change a defined entity's closed ancestors.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity B;
entity A in B;
```

</td>
<td>

```cedar
external entity A;
entity B in A;
```

</td>
<td>

Error: `definedEntityAncestorsChanged`

</td>
</tr>
</table>

<a id="example-9"></a>**9. A transitive ancestor satisfies an external declaration.** `C` compiles `F`'s closed ancestors to `X` and `G`, so it contains the ancestor promised by `P`. The Lean linker compares closed ancestor sets and does not distinguish direct parents.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity G;
external entity F in G;
```

</td>
<td>

```cedar
entity G;
entity X in G;
entity F in X;
```

</td>
<td>

```cedar
entity G;
entity X in G;
entity F in X;
```

</td>
</tr>
</table>

<a id="example-10"></a>**10. Error: action parents must match exactly.** Unlike [example 7](#example-7), an action's definition may not add parents, and repeated external declarations of an action must agree.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external action g;
external action w in g;
```

</td>
<td>

```cedar
action g;
action r;
action w in [g, r];
```

</td>
<td>

Error: `externalActionParentsMismatch`

</td>
</tr>
</table>

<a id="example-11"></a>**11. Error: an external can't be an enumerated type.** Against `P`, an `A` whose `e` is `E::"y"` is checked by type name only. So `P` can't check that `"y"` is one of the enum's values.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity E;
entity A { e: E };
```

</td>
<td>

```cedar
entity E enum ["x"];
```

</td>
<td>

Error: `externalIsEnum`

</td>
</tr>
</table>

<a id="example-12"></a>**12. Error: two definitions of the same name.** This holds even when the definitions are identical; `action a;` linked with `action a;` is `duplicateAction`.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
entity A;
```

</td>
<td>

```cedar
entity A;
```

</td>
<td>

Error: `duplicateEntityType`

</td>
</tr>
</table>

<a id="example-13"></a>**13. Error: an external cannot add an ancestor to a definition.** `P` defines `E` with the closed ancestor set containing only `X`. The ancestor `G` promised by `C` is absent from that definition.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity X;
entity E in X;
```

</td>
<td>

```cedar
external entity G;
external entity E in G;
```

</td>
<td>

Error: `externalAncestorsNotInDefinition`

</td>
</tr>
</table>

<a id="example-14"></a>**14. Error: linking cannot enlarge a defined entity's closed ancestors.** Linking the new hierarchy for `X` would add `G` to the ancestors of the defined `E`. The linker rejects that change.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity X;
entity E in X;
```

</td>
<td>

```cedar
external entity G;
external entity X in G;
```

</td>
<td>

Error: `definedEntityAncestorsChanged`

</td>
</tr>
</table>

<a id="example-15"></a>**15. An external entity's closed ancestors can grow.** This uses the same hierarchy as [example 14](#example-14), but `E` is external. Closing the linked hierarchy adds `G` to `E` without changing a definition.

<table>
<tr><th>P</th><th>C</th><th>link P C</th></tr>
<tr>
<td>

```cedar
external entity X;
external entity E in X;
```

</td>
<td>

```cedar
external entity G;
external entity X in G;
```

</td>
<td>

```cedar
external entity G;
external entity X in G;
external entity E in [X, G];
```

</td>
</tr>
</table>

The distinction between examples 14 and 15 keeps intermediate links stable: closure may add facts to external entries, but a successful link never rewrites a definition.

### Validating entities and requests
Unless noted otherwise, all rows use this partial schema `S`:
```cedar
external entity B;
external entity D;
entity A in B { b: B } tags B;
entity R { act: Action };
external action g;
external action w in g;
external action x in w;
action act in g appliesTo {
  principal: B,
  resource: A,
  context: {
    reviewer?: B,
    delegate?: Action,
  },
};
```

An entity of a defined type may refer to externals in its attributes, tags and ancestors. An entity of an external type can't be validated, because its attributes, tags and ancestors are unknown. An external action's entity can, because its declaration fixes its ancestors and action entities have no attributes or tags ([decision 9](#decision-9)).

Each displayed object denotes the complete singleton entity store. Its fields are shorthand for the usual entity JSON, except that `parents` shows the closed ancestor set seen by Lean; omitted tags mean an empty tag map. `[]` denotes the empty store. `T::"id"` is an entity UID with entity type `T` and entity id `"id"`. The Cedar source above reaches Lean with closed ancestor sets, so `x` has ancestors `w` and `g`.

<table width="100%">
<tr><th width="45%">Entity store</th><th width="55%">Validate Against <code>S</code></th></tr>
<tr>
<td>

```
[]
```

</td>
<td>

Valid: partial validation checks only supplied entries and does not require the declared action entities `act`, `g`, `w` or `x` to be present

</td>
</tr>
<tr>
<td>

```
{
  uid: A::"a",
  attrs: { b: B::"x" },
  parents: []
}
```

</td>
<td>

Valid: an attribute that refers to external type `B` only needs a UID of that type. `A in B` permits a `B` ancestor but does not require every `A` entity to have one

</td>
</tr>
<tr>
<td>

```
{
  uid: A::"a",
  attrs: { b: B::"x" },
  parents: [],
  tags: { owner: B::"owner" }
}
```

</td>
<td>

Valid: a tag on a defined entity may refer to an external entity type; the referenced `B` entity does not need to be in this store

</td>
</tr>
<tr>
<td>

```
{
  uid: A::"a",
  attrs: { b: B::"x" },
  parents: [B::"y"]
}
```

</td>
<td>

Valid: `S` declares `B` as a parent type of `A`, even though `B` is external

</td>
</tr>
<tr>
<td>

```
{
  uid: A::"a",
  attrs: { b: B::"x" },
  parents: [D::"d"]
}
```

</td>
<td>

Invalid: `D` is declared, but `S` doesn't say that `A` can be in `D`, so the ancestor can't be checked (RFC, ["External ancestor types"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#external-ancestor-types)). Linking `entity D; entity B in D;` is rejected because it would enlarge the closed ancestors of defined entity `A`

</td>
</tr>
<tr>
<td>

```
{
  uid: B::"x",
  attrs: {},
  parents: []
}
```

</td>
<td>

Invalid: `B` itself is external

</td>
</tr>
<tr>
<td>

```
{
  uid: R::"r",
  attrs: { act: Action::"g" },
  parents: []
}
```

</td>
<td>

Valid: `Action::"g"` is an exact action UID declared by `S`. Validation checks that declaration but does not use `g`'s ancestors or `appliesTo` when checking this value

</td>
</tr>
<tr>
<td>

```
{
  uid: R::"r",
  attrs: { act: Action::"missing" },
  parents: []
}
```

</td>
<td>

Invalid: an action-valued attribute must contain an exact action UID declared by `S`; having entity type `Action` is not sufficient

</td>
</tr>
<tr>
<td>

```
{
  uid: Action::"act",
  attrs: {},
  parents: [Action::"g"]
}
```

</td>
<td>

Valid: the parent is external, but `act`'s ancestors are known

</td>
</tr>
<tr>
<td>

```
{
  uid: Action::"g",
  attrs: {},
  parents: []
}
```

</td>
<td>

Valid: `g` is external, but its declaration says it has no parents, so its entity is fully known

</td>
</tr>
<tr>
<td>

```
{
  uid: Action::"w",
  attrs: {},
  parents: [Action::"g"]
}
```

</td>
<td>

Valid: `w`'s declaration fixes its parents to exactly `g`

</td>
</tr>
<tr>
<td>

```
{
  uid: Action::"w",
  attrs: {},
  parents: []
}
```

</td>
<td>

Invalid: `w`'s ancestors must be exactly `{g}`, in `S` and in every schema that links `S`

</td>
</tr>
<tr>
<td>

```
{
  uid: Action::"x",
  attrs: {},
  parents: [Action::"w", Action::"g"]
}
```

</td>
<td>

Valid: `x`'s closed ancestor set contains both its declared parent `w` and the transitive ancestor `g`

</td>
</tr>
<tr>
<td>

```
{
  uid: Action::"x",
  attrs: {},
  parents: [Action::"w"]
}
```

</td>
<td>

Invalid: action entities must contain the exact closed ancestor set, so omitting transitive ancestor `g` is invalid

</td>
</tr>
<tr>
<td>

```
{
  uid: Action::"g",
  attrs: { x: 1 },
  parents: []
}
```

</td>
<td>

Invalid: action entities can't have attributes, as today

</td>
</tr>
</table>

`S₀` is `S` without the definition of `act`. Its remaining actions are external, so its validation view has no request environments.

<table width="100%">
<tr><th width="45%">Entity store</th><th width="55%">Validate Against <code>S₀</code></th></tr>
<tr>
<td>

```
{
  uid: A::"a",
  attrs: { b: 1 },
  parents: []
}
```

</td>
<td>

Invalid: partial validation scans the supplied store directly, so having no request environments does not bypass attribute validation

</td>
</tr>
</table>

<table width="100%">
<tr><th width="45%">Request</th><th width="55%">Validate Against <code>S</code></th></tr>
<tr>
<td>

```
{
  principal: B::"x",
  action: Action::"act",
  resource: A::"a",
  context: {}
}
```

</td>
<td>

Valid: `B` is external, but `act` lists it in `appliesTo`; the optional context fields may be omitted

</td>
</tr>
<tr>
<td>

```
{
  principal: B::"x",
  action: Action::"act",
  resource: A::"a",
  context: { reviewer: B::"reviewer" }
}
```

</td>
<td>

Valid: the context of a defined action may contain a value of an external entity type

</td>
</tr>
<tr>
<td>

```
{
  principal: B::"x",
  action: Action::"act",
  resource: A::"a",
  context: { delegate: Action::"g" }
}
```

</td>
<td>

Valid: external action `g` may appear as a context value even though it cannot be used as the request action

</td>
</tr>
<tr>
<td>

```
{
  principal: B::"x",
  action: Action::"act",
  resource: A::"a",
  context: { reviewer: D::"reviewer" }
}
```

</td>
<td>

Invalid: `D` is declared and external, but `reviewer` requires the exact entity type `B`

</td>
</tr>
<tr>
<td>

```
{
  principal: A::"a",
  action: Action::"act",
  resource: A::"a",
  context: {}
}
```

</td>
<td>

Invalid: `act` doesn't apply to `A` principals. Although `A` has ancestor type `B`, request validation requires the principal type listed in `appliesTo` exactly

</td>
</tr>
<tr>
<td>

```
{
  principal: B::"x",
  action: Action::"g",
  resource: A::"a",
  context: {}
}
```

</td>
<td>

Invalid: the `appliesTo` of an external action is unknown

</td>
</tr>
</table>

## Codebase update
Paths are relative to `cedar-lean/`.
- `Cedar/Validation/PartialSchema.lean`: add `PartialEntitySchema`, `PartialActionSchema`, `PartialSchema`, coercion from `Schema`, and `PartialSchema.asSchema?`.
- `Cedar/Validation/Linker.lean`: add `link P C : Except LinkError PartialSchema` using the closed-ancestor rules above.
- `Cedar/Validation/PartialRequestEntityValidator.lean`: add `PartialSchema.validateEntities` and `PartialSchema.validateRequest` (decisions [4](#decision-4), [5](#decision-5) and [9](#decision-9)).
- `Cedar/Validation/Types.lean`: add `EntitySchemaEntry.withAncestors`, which replaces a standard entry's ancestors.
- Unchanged: the typechecker, `validate`, TPE, SymCC and every function on `Schema`.
- New theorems ([next section](#main-theorems)) go in `Cedar/Thm/External/PartialSchema.lean`, `Cedar/Thm/External/Linker.lean` and `Cedar/Thm/External/PartialValidation.lean`. `Cedar/Thm/External.lean` imports these three files, and `Cedar/Thm.lean` imports `Cedar/Thm/External.lean`.
- General facts that the proofs need go in `Cedar/Thm/Data` and `Cedar/Thm/Validation`:
  - `Cedar/Thm/Data/Relation.lean` (new, imported from `Cedar/Thm/Data.lean`): facts about `Relation.TransGen`, and about walks, which the linker proofs use to bound the rounds of `closeAncestors`.
  - `Cedar/Thm/Data/Map.lean`: `filter_wf`, `find?_eq_toList_find?`, `make_toList_map_find?`, and facts about `mapMOnValues`.
  - `Cedar/Thm/Data/MapUnion.lean`: `foldl_union_wf`; `mem_foldl_union_iff_mem_or_exists` becomes public.
  - `Cedar/Thm/Data/List/Lemmas.lean`: `forall₂_find?_some`, `forall₂_find?_none` and `mapM_isSome`.
  - `Cedar/Thm/Validation/Typechecker/WF.lean`: `CedarType.WellFormed.mono`, `TypeEnv.maps_wf_of_eq`, and well-formedness of the empty record type (`emptyRecord_wf`, `emptyRecord_lifted`) and of standard entries (`standardEntry_wf`).
  - `Cedar/Thm/Validation/EnvironmentValidation.lean`: completeness of the `validateWellFormed` checks (`*_is_complete`), the converse of the existing soundness lemmas, and `mem_environments`, which describes `Schema.environments`.
  - `Cedar/Thm/Validation/RequestEntityValidation.lean`: how `instanceOfType` and `instanceOfSchema` depend on the schema, such as `instanceOfType_mono`.
- Unit tests go in `UnitTest/Linker.lean` and `UnitTest/PartialSchema.lean`, registered in `UnitTest/Main.lean`.

## Main theorems
Throughout, `P`, `C` and `D` are partial schemas, `S` is an entity store and `r` is a request. The semantic results state their well-formedness preconditions explicitly; link results are not assumed well-formed.

### Semantic results

- <a id="linking-order-independence"></a><a id="linking-commutativity"></a>Thm: Linking Commutativity:
Changing the input order changes neither a successful result nor whether linking fails.
```
C.WellFormed →
link P C = .ok T → link C P = .ok T

P.WellFormed → C.WellFormed →
((∃ err, link P C = .error err) ↔ (∃ err, link C P = .error err))
```

- <a id="linking-associativity"></a>Thm: Linking Associativity:
Changing the grouping changes neither a successful result nor whether linking fails.
```
P.WellFormed → C.WellFormed → D.WellFormed →
link P C = .ok T₁ → link T₁ D = .ok T →
∃ T₂, link C D = .ok T₂ ∧ link P T₂ = .ok T

P.WellFormed → C.WellFormed → D.WellFormed →
((∃ err, (do let T₁ ← link P C; link T₁ D) = .error err) ↔
  (∃ err, (do let T₂ ← link C D; link P T₂) = .error err))
```

- Well-Formedness Preservation:
Linking two well-formed partial schemas gives a well-formed result.
```
P.WellFormed → C.WellFormed → link P C = .ok T → T.WellFormed
```

- Completed Schemas Are Well-Formed:
A complete link passes the existing schema well-formedness check.
```
P.WellFormed → C.WellFormed → link P C = .ok T →
T.asSchema? = some s → s.validateWellFormed = .ok ()
```

- Completion Existence:
Every well-formed partial schema has a complete linking extension.
```
P.WellFormed →
∃ C T s, C.WellFormed ∧ link P C = .ok T ∧ T.asSchema? = some s
```

- Defined Entity Ancestors Do Not Expand:
A defined entity from `P` keeps the same closed ancestor set. Swapping the inputs with [Linking Commutativity](#linking-commutativity) gives the same for `C`.
```
P.WellFormed → C.WellFormed → link P C = .ok T →
P.ets.find? n = some (.defined e) →
∃ e', T.ets.find? n = some (.defined e') ∧ e'.ancestors = e.ancestors
```

- <a id="entity-validation-soundness"></a>Thm: Entity Validation Soundness:
Entities valid against a partial schema stay valid after linking.
```
link P C = .ok T →
P.validateEntities S = .ok () → T.validateEntities S = .ok ()
```

- <a id="request-validation-soundness"></a>Thm: Request Validation Soundness:
Requests valid against a partial schema stay valid after linking.
```
P.WellFormed → C.WellFormed → link P C = .ok T →
P.validateRequest r = .ok () → T.validateRequest r = .ok ()
```

- <a id="entity-validation-completeness"></a>Thm: Entity Validation Completeness:
Entities valid against every complete schema that links a partial schema are valid against that partial schema.
```
P.WellFormed →
(∀ C T, C.WellFormed → link P C = .ok T →
  (T.asSchema?).isSome → T.validateEntities S = .ok ()) →
P.validateEntities S = .ok ()
```

- <a id="request-validation-completeness"></a>Thm: Request Validation Completeness:
Requests valid against every complete schema that links a partial schema are valid against that partial schema.
```
P.WellFormed →
(∀ C T, C.WellFormed → link P C = .ok T →
  (T.asSchema?).isSome → T.validateRequest r = .ok ()) →
P.validateRequest r = .ok ()
```

- Complete-Validation Agreement:
At a completion, request validation agrees exactly. Entity validation implies complete validation after adding the canonical entity for every action.
```
P.WellFormed → C.WellFormed → link P C = .ok T →
T.asSchema? = some s → T.validateRequest r = validateRequest s r

P.WellFormed → C.WellFormed → link P C = .ok T →
T.asSchema? = some s → T.validateEntities S = .ok () →
validateEntities s (S ++ s.acts.mapOnValues actionSchemaEntryToEntityData) = .ok ()
```
On an action that `S` already contains, `++` keeps the entity from `S`.

### Sanity rules
These characterize the closed-ancestor linker; they are not semantic results.

- Definitions Are Preserved:
Every entity or action definition from either input appears unchanged in the result.
```
link P C = .ok T →
  (∀ n e, P.ets.find? n = some (.defined e) → T.ets.find? n = some (.defined e)) ∧
  (∀ n e, C.ets.find? n = some (.defined e) → T.ets.find? n = some (.defined e)) ∧
  (∀ a e, P.acts.find? a = some (.defined e) → T.acts.find? a = some (.defined e)) ∧
  (∀ a e, C.acts.find? a = some (.defined e) → T.acts.find? a = some (.defined e))
```

- Declarations Are Preserved:
The result declares exactly the entity types and action UIDs declared by either input.
```
link P C = .ok T →
(T.ets.contains n ↔ P.ets.contains n ∨ C.ets.contains n)

link P C = .ok T →
(T.acts.contains a ↔ P.acts.contains a ∨ C.acts.contains a)
```

- Completeness Is Detected:
A partial schema converts exactly when it contains no external entry.
```
P.asSchema?.isSome ↔ P.isComplete
```

- Complete-Schema Bridge:
Conversion round-trips, and the validation view agrees with the complete schema.
```
(Schema.toPartialSchema s).asSchema? = some s

(Schema.toPartialSchema s).validationView = s

P.asSchema? = some s → P.validationView = s
```

## Major Design decisions and Alternatives
1. <a id="decision-1"></a>**Add a new inductive type for `PartialSchemaEntry`.** The alternative adds an `.external` case to `EntitySchemaEntry`. That forces every exhaustive match on it to be fixed in one PR, including about 6.9k lines of SymCC proofs.
2. <a id="decision-2"></a>**`Schema` stays complete-only and coerces into `PartialSchema`.** Policy validation, TPE and SymCC take only a `Schema`, so Lean's types enforce the [RFC's restriction](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#api). The alternative, a subtype `{ ps : PartialSchema // no externals }`, changes every `schema.ets` access and its proofs.
3. <a id="decision-3"></a>**Like `Schema`, `PartialSchema` assumes ancestor sets are transitively closed.** Partial validation consumes them unchanged; linking two well-formed partial schemas must preserve ancestor closure and every other `PartialSchema.WellFormed` condition.
4. <a id="decision-4"></a>**Partial validation reuses today's checks on a view of the partial schema.** In the view, an external entity type is a standard type with its closed declared ancestors and no attributes or tags, and an external action has its declared ancestors and an empty `appliesTo`. Instances of external entity types are rejected before the reused checks run, so the view's empty attributes are never used as facts; an external action's instance goes through the reused action check ([decision 9](#decision-9)).
5. <a id="decision-5"></a>**`PartialSchema.validateEntities` iterates over the store, without `actionExists`.** Today's `validateEntities` runs once per request environment, so it accepts any store when there is none (e.g. `S` without `act`). `actionExists` would break [Entity Validation Soundness](#entity-validation-soundness), because linking adds actions the store lacks.
6. <a id="decision-6"></a>**Each `PartialSchema` must be well-formed on its own.** The [RFC's `SchemaFragment`](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#api) may hold unresolved references that are checked only after combining. Combining such fragments stays in Rust, and Lean receives the result.
7. <a id="decision-7"></a>**Rules about common and built-in types stay in Rust.** The Lean schema has neither, so Rust rejects an external that names one before handing the schema to Lean.
8. <a id="decision-8"></a>**A value may refer to an external action** (e.g. `R::"r"` with `act: Action::"g"`). Only the action's name is checked, so linking its definition can't make the value invalid. The RFC doesn't cover this case, so Rust must make the same choice.
9. <a id="decision-9"></a>**External action entities are validated, which diverges from the RFC.** [RFC 116](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md) lists "Validate an unresolved external action entity" under ["We cannot"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#detailed-design), because the fragment lacks the action's `appliesTo`; but validating an action entity never reads `appliesTo`. The declaration fixes the action's parents exactly, and action entities have no attributes or tags, so its entity is the same in every schema that links P: validating it keeps [Entity Validation Soundness](#entity-validation-soundness) and makes [Entity Validation Completeness](#entity-validation-completeness) hold. Rust must match, and the RFC needs an amendment.
