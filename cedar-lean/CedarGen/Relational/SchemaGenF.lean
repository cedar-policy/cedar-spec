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

import CedarGen.Relational.SchemaGen

/-! # A complete schema generator, with strictness flags

`GenTypeEnvF wfMaps wfActs wfEnum wfRest closed noEnumAnc idents r budget env` describes type
environments built in one pass that a derived generator can follow. A flag set to `true` adds a
condition, and stricter settings are sub-relations of laxer ones (`GenTypeEnvF.mono`):

* `wfMaps`, `wfActs`, `wfEnum` and `wfRest` together are `validateWellFormed` (sorted maps, an acyclic
  and transitive action hierarchy, non-empty enumerations, declared references and lifted types);
* `closed` and `noEnumAnc` give the hierarchies the shape Rust's schemas have;
* `idents` restricts names to those Rust accepts.

With every flag `false` the environments are exactly those satisfying `EnvAssumptions`; with the four
`wf` flags, exactly the `TypeEnvWF` ones (`SchemaGenFThm`). Every setting keeps at most `budget`
request environments.

The relations are written for Specimen's completeness proofs (`SchemaGenFDerive`): a flag-indexed rule
is stated once per value of its flag, a rule binds at most one intermediate of each type, last, and a
later use of an already produced variable is wrapped in `id`, so that Specimen does not produce it
there. -/

namespace Cedar.Validation.Relational.SchemaGen

open Cedar.Spec
open Cedar.Data
open Cedar.Validation
open Cedar.Validation.Relational.Schema

/-! ## Names Rust accepts -/

-- `isCedarIdent` (a Cedar identifier, as Rust's `Id::from_normalized_str` and `Name::try_from`
-- accept) is the spec's, `Cedar.Validation.Relational.isCedarIdent`.

/-- An entity type name Rust's protobuf decoder accepts. -/
def isIdentName (n : Name) : Bool := isCedarIdent n.id && n.path.all isCedarIdent

/-- An action entity type Rust accepts: `ns::Action`. -/
def isActionType (n : Name) : Bool := n.id == "Action" && n.path.all isCedarIdent

/-- With `true`, an identifier name. -/
inductive NameIf : Bool → EntityType → Prop where
  | ident : ∀ b x, isIdentName x = true → NameIf b x
  | any : ∀ x, NameIf false x

/-- With `true`, an action type `ns::Action`. -/
inductive ActTyIf : Bool → EntityType → Prop where
  | action : ∀ b x, isActionType x = true → ActTyIf b x
  | any : ∀ x, ActTyIf false x

/-! ## Arranging lists: sorted or deduplicated -/

/-- The list without duplicates, keeping the last occurrence of each element. -/
def dedupKeep {α} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedupKeep xs else x :: dedupKeep xs

/-- The keys of a map: sorted and duplicate-free (`List.canonicalize`, at either flag), or, at
`false`, only duplicate-free, in their drawn order. -/
inductive KeyArrET : Bool → List EntityType → List EntityType → Prop where
  | sortT : ∀ xs, KeyArrET true xs (List.canonicalize id xs)
  | sortF : ∀ xs, KeyArrET false xs (List.canonicalize id xs)
  | dedupF : ∀ xs, KeyArrET false xs (dedupKeep xs)

/-- `KeyArrET` for action UIDs. -/
inductive KeyArrUID : Bool → List EntityUID → List EntityUID → Prop where
  | sortT : ∀ xs, KeyArrUID true xs (List.canonicalize id xs)
  | sortF : ∀ xs, KeyArrUID false xs (List.canonicalize id xs)
  | dedupF : ∀ xs, KeyArrUID false xs (dedupKeep xs)

/-- The elements of a set: sorted and duplicate-free, or, at `false`, as drawn. -/
inductive SetArrET : Bool → List EntityType → List EntityType → Prop where
  | sortT : ∀ xs, SetArrET true xs (List.canonicalize id xs)
  | sortF : ∀ xs, SetArrET false xs (List.canonicalize id xs)
  | keepF : ∀ xs, SetArrET false xs xs

/-- `SetArrET` for action UIDs. -/
inductive SetArrUID : Bool → List EntityUID → List EntityUID → Prop where
  | sortT : ∀ xs, SetArrUID true xs (List.canonicalize id xs)
  | sortF : ∀ xs, SetArrUID false xs (List.canonicalize id xs)
  | keepF : ∀ xs, SetArrUID false xs xs

/-- `SetArrET` for strings. -/
inductive SetArrStr : Bool → List String → List String → Prop where
  | sortT : ∀ xs, SetArrStr true xs (List.canonicalize id xs)
  | sortF : ∀ xs, SetArrStr false xs (List.canonicalize id xs)
  | keepF : ∀ xs, SetArrStr false xs xs

/-! ## Raw lists -/

/-- A list of names, each `NameIf i`. -/
inductive RawNames : Bool → List EntityType → Prop where
  | nil : ∀ i, RawNames i []
  | cons : ∀ i x xs, NameIf i x → RawNames i xs → RawNames i (x :: xs)

/-- A list of strings. -/
inductive RawStrs : List String → Prop where
  | nil : RawStrs []
  | cons : ∀ x xs, RawStrs xs → RawStrs (x :: xs)

/-- A list of strings, non-empty at `true`. -/
inductive RawStrsNE : Bool → List String → Prop where
  | consT : ∀ x xs, RawStrs xs → RawStrsNE true (x :: xs)
  | consF : ∀ x xs, RawStrs xs → RawStrsNE false (x :: xs)
  | nilF : RawStrsNE false []

/-- Not among the entity types, with `true`. -/
inductive NotInIf : Bool → EntityType → List EntityType → Prop where
  | strict : ∀ b x ks, NotInET x ks → NotInIf b x ks
  | lax : ∀ x ks, NotInIf false x ks

/-- An action type: `ns::Action` with `idents`, not an entity type with `wfActs`. -/
inductive ActTyOK : Bool → Bool → List EntityType → EntityType → Prop where
  | mk : ∀ a i ks x, ActTyIf i x → NotInIf a x ks → ActTyOK a i ks x

/-- A list of action UIDs: their types `ActTyOK`, their eids any string. -/
inductive RawUids : Bool → Bool → List EntityType → List EntityUID → Prop where
  | nil : ∀ a i ks, RawUids a i ks []
  | cons : ∀ a i ks ty eid us,
      ActTyOK a i ks ty →
      RawUids a i ks us →
      RawUids a i ks (⟨ty, eid⟩ :: us)

/-- The types of the action UIDs. -/
inductive TypesOf : List EntityUID → List EntityType → Prop where
  | nil : TypesOf [] []
  | cons : ∀ ty eid us ts, TypesOf us ts → TypesOf (⟨ty, eid⟩ :: us) (ty :: ts)

/-- Any rank (drawn up to the size). -/
inductive RankOf : Nat → Prop where
  | mk : ∀ k, RankOf k

/-- A rank for each action. -/
inductive Ranked : List EntityUID → List (EntityUID × Nat) → Prop where
  | nil : Ranked [] []
  | cons : ∀ u us k rs, RankOf k → Ranked us rs → Ranked (u :: us) ((u, k) :: rs)

/-! ## Entity kinds -/

/-- Standard (`false`) or enumerated (`true`). -/
inductive KindOf : Bool → Prop where
  | std : KindOf false
  | enum : KindOf true

/-- A kind for each name. -/
inductive Kinds : List EntityType → List (EntityType × Bool) → Prop where
  | nil : Kinds [] []
  | cons : ∀ x xs k ks, KindOf k → Kinds xs ks → Kinds (x :: xs) ((x, k) :: ks)

/-- The standard names. -/
inductive StdNames : List (EntityType × Bool) → List EntityType → Prop where
  | nil : StdNames [] []
  | std : ∀ x ks ss, StdNames ks ss → StdNames ((x, false) :: ks) (x :: ss)
  | enum : ∀ x ks ss, StdNames ks ss → StdNames ((x, true) :: ks) ss

/-- The enumerated names. -/
inductive EnumNames : List (EntityType × Bool) → List EntityType → Prop where
  | nil : EnumNames [] []
  | std : ∀ x ks es, EnumNames ks es → EnumNames ((x, false) :: ks) es
  | enum : ∀ x ks es, EnumNames ks es → EnumNames ((x, true) :: ks) (x :: es)

/-! ## Types -/

/-- A Boolean type: `anyBool`, or, at `false` (not lifted), any. -/
inductive BoolIf : Bool → BoolType → Prop where
  | anyT : BoolIf true .anyBool
  | anyF : BoolIf false .anyBool
  | ttF : BoolIf false .tt
  | ffF : BoolIf false .ff

/-- A reference to an entity type, at `chk`: a declared entity type, or (without `idents`) an
action type; without `chk`, any. -/
inductive RefIf : Bool → Bool → List EntityType → List EntityType → EntityType → Prop where
  | entTT : ∀ ks ats x, DefinedEntityType ks x → RefIf true true ks ats x
  | entTF : ∀ ks ats x, DefinedEntityType ks x → RefIf true false ks ats x
  | actTF : ∀ ks ats x, DefinedEntityType ats x → RefIf true false ks ats x
  | entFT : ∀ ks ats x, DefinedEntityType ks x → RefIf false true ks ats x
  | anyFT : ∀ ks ats x, RefIf false true ks ats x
  | entFF : ∀ ks ats x, DefinedEntityType ks x → RefIf false false ks ats x
  | actFF : ∀ ks ats x, DefinedEntityType ats x → RefIf false false ks ats x
  | anyFF : ∀ ks ats x, RefIf false false ks ats x

/-- The list without a second binding of any key, keeping the last binding of each. -/
def dedupKeys {α β} [DecidableEq α] : List (α × β) → List (α × β)
  | [] => []
  | p :: ps => if ps.any (fun q => decide (q.1 = p.1)) then dedupKeys ps else p :: dedupKeys ps

/-- A record type's attributes, from the drawn ones: at `chk`, sorted by key and deduplicated
(`List.canonicalize Prod.fst`), or, without `wfMaps`, deduplicated in drawn order; without `chk`,
as drawn. -/
inductive AttrArr : Bool → Bool → List (Attr × QualifiedType) → List (Attr × QualifiedType) → Prop where
  | sortTT : ∀ raw, AttrArr true true raw (List.canonicalize Prod.fst raw)
  | sortTF : ∀ raw, AttrArr true false raw (List.canonicalize Prod.fst raw)
  | dedupTF : ∀ raw, AttrArr true false raw (dedupKeys raw)
  | sortFT : ∀ raw, AttrArr false true raw (List.canonicalize Prod.fst raw)
  | rawFT : ∀ raw, AttrArr false true raw raw
  | sortFF : ∀ raw, AttrArr false false raw (List.canonicalize Prod.fst raw)
  | dedupFF : ∀ raw, AttrArr false false raw (dedupKeys raw)
  | rawFF : ∀ raw, AttrArr false false raw raw

mutual

/-- A type: at `chk`, `TyWf` and `TypeValid` (records duplicate-free, entity types declared),
records sorted with `wfMaps`, Booleans lifted with `wfRest`; without `chk`, any type. -/
inductive TyF (m d i c : Bool) (ks ats : List EntityType) : CedarType → Prop where
  | bool : ∀ bty, BoolIf d bty → TyF m d i c ks ats (.bool bty)
  | int : TyF m d i c ks ats .int
  | string : TyF m d i c ks ats .string
  | decimal : TyF m d i c ks ats (.ext .decimal)
  | ipAddr : TyF m d i c ks ats (.ext .ipAddr)
  | datetime : TyF m d i c ks ats (.ext .datetime)
  | duration : TyF m d i c ks ats (.ext .duration)
  | entity : ∀ ety, RefIf c i ks ats ety → TyF m d i c ks ats (.entity ety)
  | set : ∀ ty, TyF m d i c ks ats ty → TyF m d i c ks ats (.set ty)
  | record : ∀ attrs raw, FieldsF m d i c ks ats raw → AttrArr c m (id raw) attrs →
      TyF m d i c ks ats (.record (Map.mk attrs))

/-- Attributes, each with a type. -/
inductive FieldsF (m d i c : Bool) (ks ats : List EntityType) : List (Attr × QualifiedType) → Prop where
  | nil : FieldsF m d i c ks ats []
  | req : ∀ k ty fs, TyF m d i c ks ats ty → FieldsF m d i c ks ats fs →
      FieldsF m d i c ks ats ((k, .required ty) :: fs)
  | opt : ∀ k ty fs, TyF m d i c ks ats ty → FieldsF m d i c ks ats fs →
      FieldsF m d i c ks ats ((k, .optional ty) :: fs)

end

/-- A record type's attributes. -/
inductive RecTyF (m d i c : Bool) (ks ats : List EntityType) : List (Attr × QualifiedType) → Prop where
  | mk : ∀ attrs raw, FieldsF m d i c ks ats raw → AttrArr c m (id raw) attrs →
      RecTyF m d i c ks ats attrs

/-- No tags, or a tag type. -/
inductive TagsF (m d i : Bool) (ks ats : List EntityType) : Option CedarType → Prop where
  | none : TagsF m d i ks ats .none
  | some : ∀ ty, TyF m d i true ks ats ty → TagsF m d i ks ats (.some ty)

/-! ## Entity hierarchy -/

/-- The candidate parents: the standard names, or, without `noEnumAnc`, all names. -/
inductive AncPool : Bool → List EntityType → List EntityType → List EntityType → Prop where
  | stdT : ∀ all std, AncPool true all std std
  | stdF : ∀ all std, AncPool false all std std
  | allF : ∀ all std, AncPool false all std all

/-- A sublist. -/
inductive SubET : List EntityType → List EntityType → Prop where
  | nil : SubET [] []
  | skip : ∀ x xs ys, SubET xs ys → SubET (x :: xs) ys
  | pick : ∀ x xs ys, SubET xs ys → SubET (x :: xs) (x :: ys)

/-- Not an enumerated name, with `noEnumAnc`. -/
inductive NotEnumIf : Bool → List EntityType → EntityType → Prop where
  | strictT : ∀ eks x, NotInET x eks → NotEnumIf true eks x
  | strictF : ∀ eks x, NotInET x eks → NotEnumIf false eks x
  | laxF : ∀ eks x, NotEnumIf false eks x

/-- A parent drawn freely: a candidate (`AncPool`) among all names, or, without `wfRest`, any type
(not enumerated, with `noEnumAnc`). -/
inductive AncElem : Bool → Bool → List EntityType → List EntityType → List EntityType →
    EntityType → Prop where
  | declT : ∀ n ks sks eks pool x, AncPool n ks sks pool → DefinedEntityType pool x →
      AncElem true n ks sks eks x
  | declF : ∀ n ks sks eks pool x, AncPool n ks sks pool → DefinedEntityType pool x →
      AncElem false n ks sks eks x
  | anyF : ∀ n ks sks eks x, NotEnumIf n eks x → AncElem false n ks sks eks x

/-- A list of `AncElem`s. -/
inductive AncElems : Bool → Bool → List EntityType → List EntityType → List EntityType →
    List EntityType → Prop where
  | nil : ∀ d n ks sks eks, AncElems d n ks sks eks []
  | cons : ∀ d n ks sks eks x xs, AncElem d n ks sks eks x → AncElems d n ks sks eks xs →
      AncElems d n ks sks eks (x :: xs)

/-- A standard entity type's parents, in mode `r`, given all names `ks`, the standard ones `sks`,
the enumerated ones `eks`, and the names declared before it (`seen`, its standard ones `seenStd`):
* `dense`: each earlier candidate with probability one half (the candidates: the earlier standard
  names, or, without `noEnumAnc`, all earlier names), or (`free`) any list of `AncElem`s;
* `sparse`: none, or one earlier candidate;
* `flat`: none.
The parents are a set, arranged by `SetArrET`. -/
inductive ParentsF : HierMode → Bool → Bool → Bool → List EntityType → List EntityType →
    List EntityType → List EntityType → List EntityType → List EntityType → Prop where
  | denseStdT : ∀ m d ks sks eks seen seenStd ps raw,
      SubET seenStd raw → SetArrET m (id raw) ps →
      ParentsF .dense m d true ks sks eks seen seenStd ps
  | denseStdF : ∀ m d ks sks eks seen seenStd ps raw,
      SubET seenStd raw → SetArrET m (id raw) ps →
      ParentsF .dense m d false ks sks eks seen seenStd ps
  | denseAllF : ∀ m d ks sks eks seen seenStd ps raw,
      SubET seen raw → SetArrET m (id raw) ps →
      ParentsF .dense m d false ks sks eks seen seenStd ps
  | freeT : ∀ m d ks sks eks seen seenStd ps raw,
      AncElems d true ks sks eks raw → SetArrET m (id raw) ps →
      ParentsF .dense m d true ks sks eks seen seenStd ps
  | freeF : ∀ m d ks sks eks seen seenStd ps raw,
      AncElems d false ks sks eks raw → SetArrET m (id raw) ps →
      ParentsF .dense m d false ks sks eks seen seenStd ps
  | sparseNoneT : ∀ m d ks sks eks seen seenStd,
      ParentsF .sparse m d true ks sks eks seen seenStd []
  | sparseNoneF : ∀ m d ks sks eks seen seenStd,
      ParentsF .sparse m d false ks sks eks seen seenStd []
  | sparseStdT : ∀ m d ks sks eks seen seenStd p,
      DefinedEntityType seenStd p →
      ParentsF .sparse m d true ks sks eks seen seenStd [p]
  | sparseStdF : ∀ m d ks sks eks seen seenStd p,
      DefinedEntityType seenStd p →
      ParentsF .sparse m d false ks sks eks seen seenStd [p]
  | sparseAllF : ∀ m d ks sks eks seen seenStd p,
      DefinedEntityType seen p →
      ParentsF .sparse m d false ks sks eks seen seenStd [p]
  | flatT : ∀ m d ks sks eks seen seenStd,
      ParentsF .flat m d true ks sks eks seen seenStd []
  | flatF : ∀ m d ks sks eks seen seenStd,
      ParentsF .flat m d false ks sks eks seen seenStd []

/-- An enumerated type's eids: a set, non-empty with `wfEnum`. -/
inductive EidsF : Bool → Bool → List String → Prop where
  | mk : ∀ m e eids raw, RawStrsNE e raw → SetArrStr m (id raw) eids → EidsF m e eids

/-- The entity entries, one for each name (with its kind), threading the names declared so far. -/
inductive EntsF (m e d n i : Bool) (r : HierMode) (ks sks eks ats : List EntityType) :
    List EntityType → List EntityType → List (EntityType × Bool) →
    List (EntityType × EntitySchemaEntry) → Prop where
  | nil : ∀ seen seenStd, EntsF m e d n i r ks sks eks ats seen seenStd [] []
  | std : ∀ seen seenStd x kinds ps attrs tags ents,
      ParentsF r m d n ks sks eks seen seenStd ps →
      RecTyF m d i true ks ats attrs →
      TagsF m d i ks ats tags →
      EntsF m e d n i r ks sks eks ats (x :: seen) (x :: seenStd) kinds ents →
      EntsF m e d n i r ks sks eks ats seen seenStd ((x, false) :: kinds)
        ((x, .standard ⟨Set.mk ps, Map.mk attrs, tags⟩) :: ents)
  | enum : ∀ seen seenStd x kinds eids ents,
      EidsF m e eids →
      EntsF m e d n i r ks sks eks ats (x :: seen) seenStd kinds ents →
      EntsF m e d n i r ks sks eks ats seen seenStd ((x, true) :: kinds)
        ((x, .enum (Set.mk eids)) :: ents)

/-! ## Transitive closure -/

/-- Add `x` to `acc` unless it is there: in order with `s`, at the end otherwise. -/
def addAnc {α} [DecidableEq α] [LT α] [DecidableLT α] (s : Bool) (acc : List α) (x : α) : List α :=
  if x ∈ acc then acc else if s then List.insertCanonical id x acc else acc ++ [x]

/-- The ancestors of the first entry with key `b`, none if there is none. -/
def lookupAncs {α β} [DecidableEq α] (get : β → List α) (g : List (α × β)) (b : α) : List α :=
  match g.find? (fun p => decide (p.1 = b)) with
  | some p => get p.2
  | none => []

/-- One step: each entry gains the ancestors of its ancestors. -/
def closeStep {α β} [DecidableEq α] [LT α] [DecidableLT α] (get : β → List α) (set : β → List α → β)
    (s : Bool) (g : List (α × β)) : List (α × β) :=
  g.map fun p => (p.1, set p.2 (((get p.2).flatMap (lookupAncs get g)).foldl (addAnc s) (get p.2)))

/-- `closeStep` as many times as there are entries, which is enough to close the hierarchy (and is
checked: `closedB`). -/
def closeAll {α β} [DecidableEq α] [LT α] [DecidableLT α] (get : β → List α) (set : β → List α → β)
    (s : Bool) (g : List (α × β)) : List (α × β) :=
  Nat.iterate (closeStep get set s) g.length g

/-- Transitively closed: if `q` is an ancestor of `p`, so are `q`'s ancestors. -/
def closedB {α β} [DecidableEq α] (get : β → List α) (g : List (α × β)) : Bool :=
  g.all fun p => g.all fun q => !(decide (q.1 ∈ get p.2)) || (get q.2).all fun x => decide (x ∈ get p.2)

/-- No entry is its own ancestor. -/
def irreflB {α β} [DecidableEq α] (get : β → List α) (g : List (α × β)) : Bool :=
  g.all fun p => !(decide (p.1 ∈ get p.2))

/-- An entity entry's ancestors (an enumeration has none). -/
def entAncs : EntitySchemaEntry → List EntityType
  | .standard e => e.ancestors.elts
  | .enum _ => []

/-- An entity entry with the ancestors `l` (an enumeration is unchanged). -/
def entWith : EntitySchemaEntry → List EntityType → EntitySchemaEntry
  | .standard e, l => .standard { e with ancestors := Set.mk l }
  | .enum eids, _ => .enum eids

/-- An action's ancestors. -/
def actAncs (e : ActionSchemaEntry) : List EntityUID := e.ancestors.elts

/-- An action with the ancestors `l`. -/
def actWith (e : ActionSchemaEntry) (l : List EntityUID) : ActionSchemaEntry :=
  { e with ancestors := Set.mk l }

/-- The entity entries' ancestor sets, closed transitively with `closed` (in order: `closeS`, at
either `wfMaps`; or at the end, `closeA`, without `wfMaps`); kept as drawn otherwise. -/
inductive CloseEnts : Bool → Bool → List (EntityType × EntitySchemaEntry) →
    List (EntityType × EntitySchemaEntry) → Prop where
  | keep : ∀ m g, CloseEnts false m g g
  | closeS : ∀ c m g, closedB entAncs (closeAll entAncs entWith true g) = true →
      CloseEnts c m g (closeAll entAncs entWith true g)
  | closeA : ∀ c g, closedB entAncs (closeAll entAncs entWith false g) = true →
      CloseEnts c false g (closeAll entAncs entWith false g)

/-- The actions' ancestor sets, closed transitively and checked acyclic with `wfActs`. -/
inductive CloseActs : Bool → Bool → List (EntityUID × ActionSchemaEntry) →
    List (EntityUID × ActionSchemaEntry) → Prop where
  | keep : ∀ m g, CloseActs false m g g
  | closeS : ∀ a m g, closedB actAncs (closeAll actAncs actWith true g) = true →
      irreflB actAncs (closeAll actAncs actWith true g) = true →
      CloseActs a m g (closeAll actAncs actWith true g)
  | closeA : ∀ a g, closedB actAncs (closeAll actAncs actWith false g) = true →
      irreflB actAncs (closeAll actAncs actWith false g) = true →
      CloseActs a false g (closeAll actAncs actWith false g)

/-! ## Actions -/

/-- The action UID occurs in the list. -/
inductive DefinedUID : List EntityUID → EntityUID → Prop where
  | here : ∀ u rest, DefinedUID (u :: rest) u
  | there : ∀ u u' rest, u ≠ u' → DefinedUID rest u → DefinedUID (u' :: rest) u

/-- The action UID does not occur in the list. -/
inductive NotInUID : EntityUID → List EntityUID → Prop where
  | nil : ∀ u, NotInUID u []
  | cons : ∀ u x rest, u ≠ x → NotInUID u rest → NotInUID u (x :: rest)

/-- The actions ranked below `k`. -/
def lowerOf (ranked : List (EntityUID × Nat)) (k : Nat) : List EntityUID :=
  ranked.filterMap fun p => if p.2 < k then some p.1 else none

/-- The actions ranked below `k`, as a relation. -/
inductive LowerOf : List (EntityUID × Nat) → Nat → List EntityUID → Prop where
  | mk : ∀ ranked k, LowerOf ranked k (lowerOf ranked k)

/-- An action's candidate parents: those ranked below it, or, without `wfActs`, all actions. -/
inductive ACands : Bool → List (EntityUID × Nat) → Nat → List EntityUID → List EntityUID → Prop where
  | lowerT : ∀ ranked k uids pool, LowerOf ranked k pool → ACands true ranked k uids pool
  | lowerF : ∀ ranked k uids pool, LowerOf ranked k pool → ACands false ranked k uids pool
  | allF : ∀ ranked k uids, ACands false ranked k uids uids

/-- A sublist of action UIDs. -/
inductive SubUID : List EntityUID → List EntityUID → Prop where
  | nil : SubUID [] []
  | skip : ∀ x xs ys, SubUID xs ys → SubUID (x :: xs) ys
  | pick : ∀ x xs ys, SubUID xs ys → SubUID (x :: xs) (x :: ys)

/-- An action parent drawn freely: a candidate, or, without `wfRest`, an undeclared action. -/
inductive AElem : Bool → Bool → List (EntityUID × Nat) → Nat → List EntityUID → EntityUID → Prop where
  | declT : ∀ a ranked k uids pool x, ACands a ranked k uids pool → DefinedUID pool x →
      AElem true a ranked k uids x
  | declF : ∀ a ranked k uids pool x, ACands a ranked k uids pool → DefinedUID pool x →
      AElem false a ranked k uids x
  | undeclF : ∀ a ranked k uids ty eid, NotInUID ⟨ty, eid⟩ uids →
      AElem false a ranked k uids ⟨ty, eid⟩

/-- A list of `AElem`s. -/
inductive AElems : Bool → Bool → List (EntityUID × Nat) → Nat → List EntityUID →
    List EntityUID → Prop where
  | nil : ∀ d a ranked k uids, AElems d a ranked k uids []
  | cons : ∀ d a ranked k uids x xs, AElem d a ranked k uids x → AElems d a ranked k uids xs →
      AElems d a ranked k uids (x :: xs)

/-- An action's parents, in mode `r` (as `ParentsF`): the candidates are the actions ranked
below it, or, without `wfActs`, all actions. -/
inductive AParents : HierMode → Bool → Bool → Bool → List (EntityUID × Nat) → Nat →
    List EntityUID → List EntityUID → Prop where
  | denseLowerT : ∀ m d ranked k uids ps raw,
      SubUID (lowerOf ranked k) raw → SetArrUID m (id raw) ps →
      AParents .dense m d true ranked k uids ps
  | denseLowerF : ∀ m d ranked k uids ps raw,
      SubUID (lowerOf ranked k) raw → SetArrUID m (id raw) ps →
      AParents .dense m d false ranked k uids ps
  | denseAllF : ∀ m d ranked k uids ps raw,
      SubUID uids raw → SetArrUID m (id raw) ps →
      AParents .dense m d false ranked k uids ps
  | freeT : ∀ m d ranked k uids ps raw,
      AElems d true ranked k uids raw → SetArrUID m (id raw) ps →
      AParents .dense m d true ranked k uids ps
  | freeF : ∀ m d ranked k uids ps raw,
      AElems d false ranked k uids raw → SetArrUID m (id raw) ps →
      AParents .dense m d false ranked k uids ps
  | sparseNoneT : ∀ m d ranked k uids, AParents .sparse m d true ranked k uids []
  | sparseNoneF : ∀ m d ranked k uids, AParents .sparse m d false ranked k uids []
  | sparseLowerT : ∀ m d ranked k uids p,
      DefinedUID (lowerOf ranked k) p → AParents .sparse m d true ranked k uids [p]
  | sparseLowerF : ∀ m d ranked k uids p,
      DefinedUID (lowerOf ranked k) p → AParents .sparse m d false ranked k uids [p]
  | sparseAllF : ∀ m d ranked k uids p,
      DefinedUID uids p → AParents .sparse m d false ranked k uids [p]
  | flatT : ∀ m d ranked k uids, AParents .flat m d true ranked k uids []
  | flatF : ∀ m d ranked k uids, AParents .flat m d false ranked k uids []

/-- A list of `appliesTo` types: at `wfRest`, declared (`RefIf`). -/
inductive AppliesF : Bool → Bool → List EntityType → List EntityType → List EntityType → Prop where
  | nil : ∀ d i ks ats, AppliesF d i ks ats []
  | cons : ∀ d i ks ats x xs, RefIf d i ks ats x → AppliesF d i ks ats xs →
      AppliesF d i ks ats (x :: xs)

/-- At most `n` `appliesTo` types. -/
inductive AppliesBounded : Bool → Bool → List EntityType → List EntityType → Nat →
    List EntityType → Prop where
  | nil : ∀ d i ks ats n, AppliesBounded d i ks ats n []
  | cons : ∀ d i ks ats n x xs, RefIf d i ks ats x → AppliesBounded d i ks ats n xs →
      AppliesBounded d i ks ats (n + 1) (x :: xs)

/-- Between one and `n` `appliesTo` types. -/
inductive AppliesNE : Bool → Bool → List EntityType → List EntityType → Nat →
    List EntityType → Prop where
  | mk : ∀ d i ks ats n x xs, RefIf d i ks ats x → AppliesBounded d i ks ats n xs →
      AppliesNE d i ks ats (n + 1) (x :: xs)

/-- An action's drawn resource types, given its principal types `ps` and the budget `b` left:
bounded so that the environments they make fit in `b`; free if there are no principals. -/
inductive RawResources : Bool → Bool → List EntityType → List EntityType → Nat →
    List EntityType → List EntityType → Prop where
  | none : ∀ d i ks ats b raw, AppliesF d i ks ats raw → RawResources d i ks ats b [] raw
  | some : ∀ d i ks ats b p ps raw, AppliesBounded d i ks ats (b / (ps.length + 1)) raw →
      RawResources d i ks ats b (p :: ps) raw

/-- An action's principal types: drawn, then arranged. -/
inductive PrincipalsF : Bool → Bool → Bool → List EntityType → List EntityType → List EntityType →
    Prop where
  | mk : ∀ m d i ks ats ps raw, AppliesF d i ks ats raw → SetArrET m (id raw) ps →
      PrincipalsF m d i ks ats ps

/-- An action's resource types within the budget `b` (`RawResources`), arranged. -/
inductive ResourcesF : Bool → Bool → Bool → List EntityType → List EntityType → Nat →
    List EntityType → List EntityType → Prop where
  | mk : ∀ m d i ks ats b ps rs raw, RawResources d i ks ats b ps raw → SetArrET m (id raw) rs →
      ResourcesF m d i ks ats b ps rs

/-- Between one and `n` `appliesTo` types (`AppliesNE`), arranged. -/
inductive AppliesNEF : Bool → Bool → Bool → List EntityType → List EntityType → Nat →
    List EntityType → Prop where
  | mk : ∀ m d i ks ats n ps raw, AppliesNE d i ks ats n raw → SetArrET m (id raw) ps →
      AppliesNEF m d i ks ats n ps

/-- The action entries along `todo` (each with its rank), sharing the budget `b` of request
environments. -/
inductive ActsB (m a d i : Bool) (r : HierMode) (ks ats : List EntityType) (uids : List EntityUID)
    (ranked : List (EntityUID × Nat)) :
    Nat → List (EntityUID × Nat) → List (EntityUID × ActionSchemaEntry) → Prop where
  | nil : ∀ b, ActsB m a d i r ks ats uids ranked b [] []
  | cons : ∀ b u k todo ps rs ancs ctx acts,
      PrincipalsF m d i ks ats ps →
      ResourcesF m d i ks ats b ps rs →
      AParents r m d a ranked k uids ancs →
      RecTyF m d i d ks ats ctx →
      ActsB m a d i r ks ats uids ranked (b - ps.length * rs.length) todo acts →
      ActsB m a d i r ks ats uids ranked b ((u, k) :: todo)
        ((u, ⟨Set.mk ps, Set.mk rs, Set.mk ancs, Map.mk ctx⟩) :: acts)

/-- `ActsB` with the request still to place: some action, `request`, is the request's, with one
of its principal types and one of its resource types; until then `cons` passes it on, keeping
one environment of the budget for it. -/
inductive ActsR (m a d i : Bool) (r : HierMode) (ks ats : List EntityType) (uids : List EntityUID)
    (ranked : List (EntityUID × Nat)) :
    Nat → List (EntityUID × Nat) → List (EntityUID × ActionSchemaEntry) → RequestType → Prop where
  | cons : ∀ b u k todo ps rs ancs ctx acts reqty,
      PrincipalsF m d i ks ats ps →
      ResourcesF m d i ks ats (b - 1) ps rs →
      AParents r m d a ranked k uids ancs →
      RecTyF m d i d ks ats ctx →
      ActsR m a d i r ks ats uids ranked (b - ps.length * rs.length) todo acts reqty →
      ActsR m a d i r ks ats uids ranked b ((u, k) :: todo)
        ((u, ⟨Set.mk ps, Set.mk rs, Set.mk ancs, Map.mk ctx⟩) :: acts) reqty
  | request : ∀ b u k todo ps p rs res ancs ctx acts,
      AppliesNEF m d i ks ats b ps →
      DefinedEntityType ps p →
      AppliesNEF m d i ks ats (b / ps.length) rs →
      DefinedEntityType rs res →
      AParents r m d a ranked k uids ancs →
      RecTyF m d i d ks ats ctx →
      ActsB m a d i r ks ats uids ranked (b - ps.length * rs.length) todo acts →
      ActsR m a d i r ks ats uids ranked b ((u, k) :: todo)
        ((u, ⟨Set.mk ps, Set.mk rs, Set.mk ancs, Map.mk ctx⟩) :: acts)
        ⟨p, u, res, Map.mk ctx⟩

/-- A declared entity or action type, whatever the flags (the request's action type). -/
inductive RefAny : List EntityType → List EntityType → EntityType → Prop where
  | ent : ∀ ks ats x, DefinedEntityType ks x → RefAny ks ats x
  | act : ∀ ks ats x, DefinedEntityType ats x → RefAny ks ats x

/-- Without `wfRest`, the request is free: declared principal, resource and action types, a valid
context. -/
inductive ReqFree : Bool → Bool → List EntityType → List EntityType → RequestType → Prop where
  | mk : ∀ m i ks ats p ty eid res ctx,
      RefIf true i ks ats p →
      RefIf true i ks ats res →
      RefAny ks ats ty →
      RecTyF m false i true ks ats ctx →
      ReqFree m i ks ats ⟨p, ⟨ty, eid⟩, res, Map.mk ctx⟩

/-! ## Type environments -/

/-- The names of a schema, before any entry: the entity type names `ks` with their kinds, the
standard and enumerated ones, the action UIDs, their types and ranks. -/
structure Skeleton where
  ks : List EntityType
  kinds : List (EntityType × Bool)
  sks : List EntityType
  eks : List EntityType
  uids : List EntityUID
  ats : List EntityType
  ranked : List (EntityUID × Nat)

/-- The entity type names: drawn, then arranged. -/
inductive NamesF : Bool → Bool → List EntityType → Prop where
  | mk : ∀ m i ks rawN, RawNames i rawN → KeyArrET m (id rawN) ks → NamesF m i ks

/-- The action UIDs: drawn, then arranged; their types and ranks. -/
inductive UidsF : Bool → Bool → Bool → List EntityType → List EntityUID → List EntityType →
    List (EntityUID × Nat) → Prop where
  | mk : ∀ m a i ks uids ats ranked rawU,
      RawUids a i ks rawU → KeyArrUID m (id rawU) uids → TypesOf (id uids) ats →
      Ranked (id uids) ranked → UidsF m a i ks uids ats ranked

/-- No definition shadows one in the empty namespace (Rust's RFC 70 check,
`AllDefs::rfc_70_shadowing_checks`): no namespaced entity type `ns::X` next to an entity type `X`,
and no action `ns::Action::"a"` next to `Action::"a"`. -/
def noShadowB (ks : List EntityType) (uids : List EntityUID) : Bool :=
  ks.all (fun x => !x.path.isEmpty || ks.all (fun y => y.path.isEmpty || y.id != x.id)) &&
  uids.all (fun u => !u.ty.path.isEmpty ||
    uids.all (fun v => v.ty.path.isEmpty || v.eid != u.eid))

/-- The action UIDs, kept as they are, `noShadowB` with the entity type names at `true` (its
producer is in `SchemaGenFLaws`). -/
inductive ShadowIf : Bool → List EntityType → List EntityUID → List EntityUID → Prop where
  | strict : ∀ b ks uids, noShadowB ks uids = true → ShadowIf b ks uids uids
  | lax : ∀ ks uids, ShadowIf false ks uids uids

theorem ShadowIf.eq_ok {i ks u u'} (h : ShadowIf i ks u u') :
    u' = u ∧ (i = true → noShadowB ks u = true) := by
  cases h with
  | strict _ _ _ h => exact ⟨rfl, fun _ => h⟩
  | lax => exact ⟨rfl, fun h => nomatch h⟩

/-- The skeleton. Each premise produces one of its lists, in the order written; later uses are
wrapped in `id`, which keeps Specimen from producing a list there. -/
inductive SkelF : Bool → Bool → Bool → Skeleton → Prop where
  | mk : ∀ m a i ks kinds sks eks uids ats ranked uids₀,
      NamesF m i ks →
      Kinds (id ks) kinds →
      StdNames (id kinds) sks →
      EnumNames (id kinds) eks →
      UidsF m a i (id ks) uids₀ ats ranked →
      ShadowIf i (id ks) (id uids₀) uids →
      SkelF m a i ⟨ks, kinds, sks, eks, uids, ats, ranked⟩

/-- The entity entries over the skeleton, closed with `closed`. -/
inductive EntsAll (m e d c n i : Bool) (r : HierMode) (sk : Skeleton) :
    List (EntityType × EntitySchemaEntry) → Prop where
  | mk : ∀ ents pre,
      EntsF m e d n i r sk.ks sk.sks sk.eks sk.ats [] [] sk.kinds pre →
      CloseEnts c m (id pre) ents →
      EntsAll m e d c n i r sk ents

/-- The action entries over the skeleton, one of them the request's, closed with `wfActs`. -/
inductive ActsAllR (m a i : Bool) (r : HierMode) (sk : Skeleton) (b : Nat) :
    List (EntityUID × ActionSchemaEntry) → RequestType → Prop where
  | mk : ∀ acts reqty pre,
      ActsR m a true i r sk.ks sk.ats sk.uids sk.ranked b sk.ranked pre reqty →
      CloseActs a m (id pre) acts →
      ActsAllR m a i r sk b acts reqty

/-- The action entries over the skeleton, closed with `wfActs`. -/
inductive ActsAllB (m a i : Bool) (r : HierMode) (sk : Skeleton) (b : Nat) :
    List (EntityUID × ActionSchemaEntry) → Prop where
  | mk : ∀ acts pre,
      ActsB m a false i r sk.ks sk.ats sk.uids sk.ranked b sk.ranked pre →
      CloseActs a m (id pre) acts →
      ActsAllB m a i r sk b acts

/-- A hierarchy mode, drawn first (uniformly) so that a campaign covers each. -/
inductive AnyMode : HierMode → Prop where
  | dense : AnyMode .dense
  | sparse : AnyMode .sparse
  | flat : AnyMode .flat

/-- The schema generator. With `wfRest` (`decl`) the request is one of the actions'; without it
(`free`) it is drawn on its own. -/
inductive GenTypeEnvF : Bool → Bool → Bool → Bool → Bool → Bool → Bool → HierMode → Nat →
    TypeEnv → Prop where
  | decl : ∀ m a e c n i r b ents acts reqty sk,
      AnyMode r →
      SkelF m a i sk →
      EntsAll m e true c n i (id r) (id sk) ents →
      ActsAllR m a i (id r) (id sk) b acts reqty →
      GenTypeEnvF m a e true c n i r b ⟨Map.mk ents, Map.mk acts, reqty⟩
  | free : ∀ m a e c n i r b ents acts reqty sk,
      AnyMode r →
      SkelF m a i sk →
      EntsAll m e false c n i (id r) (id sk) ents →
      ActsAllB m a i (id r) (id sk) b acts →
      ReqFree m i (id sk).ks (id sk).ats reqty →
      GenTypeEnvF m a e false c n i r b ⟨Map.mk ents, Map.mk acts, reqty⟩

end Cedar.Validation.Relational.SchemaGen
