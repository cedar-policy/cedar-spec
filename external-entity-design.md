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

<a id="example-8"></a>**8. Cycles through externals.** Entity type hierarchies may have cycles, as today, so `A` and `B` become ancestors of each other. Action hierarchies must stay acyclic, so a cycle there is `actionHierarchyCycle`.

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

```cedar
entity A in B;
entity B in A;
```

</td>
</tr>
</table>

<a id="example-9"></a>**9. Error: a declared parent must be a direct parent of the definition.** `G` is an ancestor of `F`, but only through `X` (RFC, ["External ancestor types"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#external-ancestor-types)).

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

Error: `externalParentNotDirect`

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

### Validating entities and requests
All rows use this partial schema `S`:
```cedar
external entity B;
external entity D;
entity A in B { b: B };
entity R { act: Action };
external action g;
external action w in g;
action act in g appliesTo { principal: B, resource: A };
```

An entity of a defined type may refer to externals in its attributes, tags and ancestors. An entity of an external type can't be validated, because its attributes, tags and ancestors are unknown. An external action's entity can, because its declaration fixes its parents and action entities have no attributes or tags ([decision 9](#decision-9)).

Each entity is a record of its UID, attributes and parents, a shorthand for the usual entity JSON. `T::"id"` is an entity UID: entity type `T`, entity id `"id"`.

<table width="100%">
<tr><th width="45%">Entity</th><th width="55%">Validate Against <code>S</code></th></tr>
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

Valid: an attribute that refers to an external type only needs the right type name

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

Invalid: `D` is declared, but `S` doesn't say that `A` can be in `D`, so the ancestor can't be checked (RFC, ["External ancestor types"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#external-ancestor-types)). It becomes valid after linking `entity D; entity B in D;`

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

Valid: `g` is a declared external action, and only its name is checked. Nothing about `g`'s parents or `appliesTo` is assumed

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

Invalid: `w`'s parents must be exactly `g`, in `S` and in every schema that links `S`

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

Valid: `B` is external, but `act` lists it in `appliesTo`

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

Invalid: `act` doesn't apply to `A` principals

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
- `Cedar/Validation/Types.lean`: add `PartialEntitySchema`, mapping each entity type to `.defined (entry : EntitySchemaEntry)` or `.external (parents : Set EntityType)`.
- Add `PartialActionSchema`, mapping each action to `.defined (entry : ActionSchemaEntry)` or `.external (parents : Set EntityUID)`.
- `PartialSchema` holds both maps, and `Schema` coerces into it (decisions [1](#decision-1)–[3](#decision-3)).
- `Cedar/Validation/Linker.lean` (new): the well-formedness check, `link P C : Except LinkError PartialSchema`, and `PartialSchema.toSchema?`. Their results are the examples above; `toSchema?` returns a `Schema` only when no external is left.
- `Cedar/Validation/RequestEntityValidator.lean`: add `PartialSchema.validateEntities` and `PartialSchema.validateRequest` (decisions [4](#decision-4), [5](#decision-5) and [9](#decision-9)).
- Unchanged: the typechecker, `validate`, TPE, SymCC and every function on `Schema`. So no existing theorem should break.
- New theorems ([next section](#main-theorems)) go in `Cedar/Thm/Validation/Linker.lean` and `Cedar/Thm/Validation/PartialSchema.lean`, imported from `Cedar/Thm/Validation.lean`; `lake lint` fails if an import is missing.
- Unit tests go in `UnitTest/Linker.lean` and `UnitTest/PartialSchema.lean`, registered in `UnitTest/Main.lean`. Each example above becomes a test, with the schemas written as Lean literals because Lean can't parse Cedar text.

## Main theorems
Throughout, `link P C = .ok T`: T is the result of linking partial schema C into P.

### Semantic results

- <a id="linking-order-independence"></a>Thm: Linking Order Independence: 
The result doesn't depend on the order in which schemas are linked (commutativity and associativity).
```
link P C = .ok T → link C P = .ok T

link P C = .ok T₁ → link T₁ D = .ok T → ∃ T₂, link C D = .ok T₂ ∧ link P T₂ = .ok T
```

- Well-Formedness Preservation: 
Linking two well-formed partial schemas gives a well-formed partial schema.
```
P.WellFormed → C.WellFormed → link P C = .ok T → T.WellFormed
```

- <a id="entity-validation-soundness"></a>Thm: Entity Validation Soundness: 
Entities valid against a partial schema stay valid after linking.
```
link P C = .ok T → P.validateEntities S = .ok () → T.validateEntities S = .ok ()
```

- <a id="request-validation-soundness"></a>Thm: Request Validation Soundness: 
Requests valid against a partial schema stay valid after linking.
```
link P C = .ok T → P.validateRequest r  = .ok () → T.validateRequest r = .ok ()
```

- <a id="entity-validation-completeness"></a>Thm: Entity Validation Completeness: 
Entities valid against every complete schema that links a partial schema are valid against that partial schema.
```
(∀ C T, link P C = .ok T → (T.toSchema?).isSome → T.validateEntities S = .ok ()) →
P.validateEntities S = .ok ()
```

- <a id="request-validation-completeness"></a>Thm: Request Validation Completeness: 
Requests valid against every complete schema that links a partial schema are valid against that partial schema.
```
(∀ C T, link P C = .ok T → (T.toSchema?).isSome → T.validateRequest r = .ok ()) →
P.validateRequest r = .ok ()
```
- Corollary: Agreement with Complete Validation: 
When linking gives a complete schema, partial validation implies validation against the complete, linked schema.
```
link P C = .ok T → T.toSchema? = some s →
P.validateEntities S = .ok () → validateEntities s (S.withActionsOf s) = .ok ()

link P C = .ok T → T.toSchema? = some s →
P.validateRequest r = .ok () → validateRequest s r = .ok ()
```

### Sanity rules
These check that `link` implements the [RFC's linking rules](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#detailed-design); they are not semantic results.
- Linker Completeness: 
The linker succeeds exactly on the pairs of partial schemas that satisfy the [RFC's linking rules](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#detailed-design).
```
(∃ T, link P C = .ok T) ↔ Linkable P C
```
- Definitions Replace Externals: 
A definition replaces every external declaration of its name (RFC, ["Detailed design"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#detailed-design)).
```
link P C = .ok T → C.ets.find? n = some (.defined e) → T.ets.find? n = some (.defined e)
```

- Declarations Are Preserved: 
The result declares exactly the names that P or C declares.
```
link P C = .ok T → (T.declares n ↔ P.declares n ∨ C.declares n)
```
- Repeated Externals Combine: 
An entity type that both schemas declare as external gets the union of the declared parents; an action keeps its declared parents, which must agree (RFC, ["Detailed design"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#detailed-design) and ["External actions"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#external-actions)).
```
link P C = .ok T → P.ets.find? n = some (.external p₁) → C.ets.find? n = some (.external p₂) →
T.ets.find? n = some (.external (p₁ ∪ p₂))
link P C = .ok T → P.acts.find? a = some (.external p) → C.acts.find? a = some (.external p) →
T.acts.find? a = some (.external p)
```
- Completeness Is Detected: 
The result is complete exactly when every external of P or C is defined by P or C.
```
link P C = .ok T →
((T.toSchema?).isSome ↔ ∀ n, P.isExternal n ∨ C.isExternal n → P.defines n ∨ C.defines n)
```
- Completed Schemas Are Well-Formed: 
A complete schema produced from a well-formed partial schema passes today's well-formedness check, so the existing theorems apply to it.
```
T.WellFormed → T.toSchema? = some s → s.validateWellFormed = .ok ()
```
- Complete Schemas Round-Trip: 
Converting a schema to a partial schema and back gives the same schema, as long as its ancestor sets are transitively closed.
```
s.AncestorsClosed → (↑s : PartialSchema).toSchema? = some s
```

## Major Design decisions and Alternatives
1. <a id="decision-1"></a>**Add a new inductive type for `PartialSchemaEntry`.** The alternative adds an `.external` case to `EntitySchemaEntry`. That forces every exhaustive match on it to be fixed in one PR, including about 6.9k lines of SymCC proofs.
2. <a id="decision-2"></a>**`Schema` stays complete-only and coerces into `PartialSchema`.** Policy validation, TPE and SymCC take only a `Schema`, so Lean's types enforce the [RFC's restriction](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#api). The alternative, a subtype `{ ps : PartialSchema // no externals }`, changes every `schema.ets` access and its proofs.
3. <a id="decision-3"></a>**`PartialSchema` stores direct parents.** The linker needs them for the [RFC's direct-parent rule](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#external-ancestor-types) ([example 9](#example-9)); transitive closure happens only in validation and `toSchema?`. A coerced `Schema` has only closed ancestor sets, so the rule is checked against those.
4. <a id="decision-4"></a>**Partial validation reuses today's checks on a view of the partial schema.** In the view, an external entity type is a standard type with its closed declared ancestors and no attributes or tags, and an external action has its declared ancestors and an empty `appliesTo`. Instances of external entity types are rejected before the reused checks run, so the view's empty attributes are never used as facts; an external action's instance goes through the reused action check ([decision 9](#decision-9)).
5. <a id="decision-5"></a>**`PartialSchema.validateEntities` iterates over the store, without `actionExists`.** Today's `validateEntities` runs once per request environment, so it accepts any store when there is none (e.g. `S` without `act`). `actionExists` would break [Entity Validation Soundness](#entity-validation-soundness), because linking adds actions the store lacks.
6. <a id="decision-6"></a>**Each `PartialSchema` must be well-formed on its own.** The [RFC's `SchemaFragment`](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#api) may hold unresolved references that are checked only after combining. Combining such fragments stays in Rust, and Lean receives the result.
7. <a id="decision-7"></a>**Rules about common and built-in types stay in Rust.** The Lean schema has neither, so Rust rejects an external that names one before handing the schema to Lean.
8. <a id="decision-8"></a>**A value may refer to an external action** (e.g. `R::"r"` with `act: Action::"g"`). Only the action's name is checked, so linking its definition can't make the value invalid. The RFC doesn't cover this case, so Rust must make the same choice.
9. <a id="decision-9"></a>**External action entities are validated, which diverges from the RFC.** [RFC 116](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md) lists "Validate an unresolved external action entity" under ["We cannot"](https://github.com/cedar-policy/rfcs/blob/rfc-validating-entities/text/0116-entity-validation-schema-fragments.md#detailed-design), because the fragment lacks the action's `appliesTo`; but validating an action entity never reads `appliesTo`. The declaration fixes the action's parents exactly, and action entities have no attributes or tags, so its entity is the same in every schema that links P: validating it keeps [Entity Validation Soundness](#entity-validation-soundness) and makes [Entity Validation Completeness](#entity-validation-completeness) hold. Rust must match, and the RFC needs an amendment.
