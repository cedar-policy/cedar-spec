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

public import Cedar.Spec
public import Cedar.Validation

@[expose] public section

/-! # Relational specification of the Cedar typing judgement

`HasType decl syn x c env ty cout` holds when `x` has type `ty` and earns the capabilities `cout`
under the capabilities `c`. Each rule is one branch of `typeOf`; `HasType false false` agrees with
`typeOf` on environments satisfying `EnvAssumptions` (`hasType_iff_typeOf_ok`). The flags add the
syntactic conditions `validate` and the parser impose (see *Strictness flags*). -/

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## Structural helpers -/

/-- Two distinct Boolean types. -/
inductive BoolTypeNeq : BoolType → BoolType → Prop where
  | tt_ff : BoolTypeNeq .tt .ff
  | tt_any : BoolTypeNeq .tt .anyBool
  | ff_tt : BoolTypeNeq .ff .tt
  | ff_any : BoolTypeNeq .ff .anyBool
  | any_tt : BoolTypeNeq .anyBool .tt
  | any_ff : BoolTypeNeq .anyBool .ff

/-- Two distinct primitive values. -/
inductive PrimNeq : Prim → Prim → Prop where
  | bool_int : ∀ b i, PrimNeq (.bool b) (.int i)
  | bool_string : ∀ b s, PrimNeq (.bool b) (.string s)
  | bool_entity : ∀ b uid, PrimNeq (.bool b) (.entityUID uid)
  | int_bool : ∀ i b, PrimNeq (.int i) (.bool b)
  | int_string : ∀ i s, PrimNeq (.int i) (.string s)
  | int_entity : ∀ i uid, PrimNeq (.int i) (.entityUID uid)
  | string_bool : ∀ s b, PrimNeq (.string s) (.bool b)
  | string_int : ∀ s i, PrimNeq (.string s) (.int i)
  | string_entity : ∀ s uid, PrimNeq (.string s) (.entityUID uid)
  | entity_bool : ∀ uid b, PrimNeq (.entityUID uid) (.bool b)
  | entity_int : ∀ uid i, PrimNeq (.entityUID uid) (.int i)
  | entity_string : ∀ uid s, PrimNeq (.entityUID uid) (.string s)
  | bool_bool : ∀ b₁ b₂, b₁ ≠ b₂ → PrimNeq (.bool b₁) (.bool b₂)
  | int_int : ∀ i₁ i₂, i₁ ≠ i₂ → PrimNeq (.int i₁) (.int i₂)
  | string_string : ∀ s₁ s₂, s₁ ≠ s₂ → PrimNeq (.string s₁) (.string s₂)
  | entity_entity : ∀ uid₁ uid₂, uid₁ ≠ uid₂ → PrimNeq (.entityUID uid₁) (.entityUID uid₂)

mutual

/-- `Lub ty₁ ty₂ ty` holds when `ty₁ ⊔ ty₂ = some ty` (`lub?`). -/
inductive Lub : CedarType → CedarType → CedarType → Prop where
  | boolSame : ∀ b, Lub (.bool b) (.bool b) (.bool b)
  | boolDiff : ∀ b₁ b₂, BoolTypeNeq b₁ b₂ → Lub (.bool b₁) (.bool b₂) (.bool .anyBool)
  | int : Lub .int .int .int
  | string : Lub .string .string .string
  | entity : ∀ ety, Lub (.entity ety) (.entity ety) (.entity ety)
  | ext : ∀ xty, Lub (.ext xty) (.ext xty) (.ext xty)
  | set : ∀ s₁ s₂ s, Lub s₁ s₂ s → Lub (.set s₁) (.set s₂) (.set s)
  | record : ∀ r₁ r₂ r, LubRecord r₁ r₂ r → Lub (.record (.mk r₁)) (.record (.mk r₂)) (.record (.mk r))

/-- `lubQualifiedType`: the least upper bound of two qualified types. -/
inductive LubQualified : QualifiedType → QualifiedType → QualifiedType → Prop where
  | optional : ∀ t₁ t₂ t, Lub t₁ t₂ t → LubQualified (.optional t₁) (.optional t₂) (.optional t)
  | required : ∀ t₁ t₂ t, Lub t₁ t₂ t → LubQualified (.required t₁) (.required t₂) (.required t)

/-- `lubRecordType`: the pointwise least upper bound of two record types with the same keys
    in the same order. -/
inductive LubRecord : List (Attr × QualifiedType) → List (Attr × QualifiedType) → List (Attr × QualifiedType) → Prop where
  | nil : LubRecord [] [] []
  | cons : ∀ k v₁ v₂ v r₁ r₂ r, LubQualified v₁ v₂ v → LubRecord r₁ r₂ r → LubRecord ((k, v₁) :: r₁) ((k, v₂) :: r₂) ((k, v) :: r)

end

mutual

/-- Two types have a least upper bound (`(ty₁ ⊔ ty₂).isSome`), without naming it. -/
inductive LubCompat : CedarType → CedarType → Prop where
  | bool : ∀ b₁ b₂, LubCompat (.bool b₁) (.bool b₂)
  | int : LubCompat .int .int
  | string : LubCompat .string .string
  | entity : ∀ ety, LubCompat (.entity ety) (.entity ety)
  | ext : ∀ xty, LubCompat (.ext xty) (.ext xty)
  | set : ∀ s₁ s₂, LubCompat s₁ s₂ → LubCompat (.set s₁) (.set s₂)
  | record : ∀ r₁ r₂, LubCompatRecord r₁ r₂ → LubCompat (.record (.mk r₁)) (.record (.mk r₂))

/-- The record case of `LubCompat`. -/
inductive LubCompatRecord : List (Attr × QualifiedType) → List (Attr × QualifiedType) → Prop where
  | nil : LubCompatRecord [] []
  | consReq : ∀ k t₁ t₂ r₁ r₂, LubCompat t₁ t₂ → LubCompatRecord r₁ r₂ →
      LubCompatRecord ((k, .required t₁) :: r₁) ((k, .required t₂) :: r₂)
  | consOpt : ∀ k t₁ t₂ r₁ r₂, LubCompat t₁ t₂ → LubCompatRecord r₁ r₂ →
      LubCompatRecord ((k, .optional t₁) :: r₁) ((k, .optional t₂) :: r₂)
end

/-! ## Map and set membership -/

/-- `k` is bound to `v` somewhere in the map (not necessarily by its first binding). -/
inductive MapContains {α β : Type} : α → β → Map α β → Prop where
  | here : ∀ k v rest, MapContains k v (.mk ((k, v) :: rest))
  | there : ∀ k v k' v' rest, MapContains k v (.mk rest) → MapContains k v (.mk ((k', v') :: rest))

/-- `k` is not a key of the map. -/
inductive MapNotContainsKey {α β : Type} [DecidableEq α] : α → Map α β → Prop where
  | empty : ∀ k, MapNotContainsKey k (.mk [])
  | skip : ∀ k k' v' rest, k ≠ k' → MapNotContainsKey k (.mk rest) → MapNotContainsKey k (.mk ((k', v') :: rest))

/-- `x` is an element of the set. -/
inductive SetContains {α : Type} : α → Set α → Prop where
  | here : ∀ x rest, SetContains x (.mk (x :: rest))
  | there : ∀ x y rest, SetContains x (.mk rest) → SetContains x (.mk (y :: rest))

/-- The map has a binding `⟨a, b⟩ ↦ va` for an entity UID with type `a` and eid `b`. -/
inductive MapContainsPairKey {v} : EntityType → String → v → Map EntityUID v → Prop where
  | here : MapContainsPairKey a b va (Map.mk ((⟨a,b⟩, va) :: m))
  | nextA : a ≠ a' → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))
  | nextB : b ≠ b' → MapContainsPairKey a b va (Map.mk m) → MapContainsPairKey a b va (Map.mk ((⟨a',b'⟩, v') :: m))

/-! ## Entity UID validity -/

/-- `⟨ety, eid⟩` is a valid entity UID (`EntitySchema.isValidEntityUID` or
    `ActionSchema.contains`): `ety` is a standard entity type, an enumerated entity type with
    `eid` among its members, or `⟨ety, eid⟩` is an action. -/
inductive ValidEntityUID : EntityType → String → EntitySchema → ActionSchema → Prop where
  | standard : ∀ ety eid entry ets acts, MapContains ety (EntitySchemaEntry.standard entry) ets →
      ValidEntityUID ety eid ets acts
  | enum : ∀ ety eid eids ets acts, MapContains ety (EntitySchemaEntry.enum eids) ets →
      SetContains eid eids → ValidEntityUID ety eid ets acts
  | action : ∀ ety eid ets acts entry, MapContainsPairKey ety eid entry acts →
      ValidEntityUID ety eid ets acts

/-- `ety` is a key of the entity schema or the type of an action, as in `typeOf`. -/
inductive ValidEntityType : EntityType → EntitySchema → ActionSchema → Prop where
  | inSchema : ∀ ety entry ets acts, MapContains ety entry ets → ValidEntityType ety ets acts
  | isAction : ∀ ety eid entry ets acts, MapContainsPairKey ety eid entry acts → ValidEntityType ety ets acts

/-! ## Capabilities -/

/-- `(x, k) ∈ c`. -/
inductive CapMem : Expr → Key → Capabilities → Prop where
  | here : ∀ x k rest, CapMem x k ((x, k) :: rest)
  | there : ∀ x k x' k' rest, CapMem x k rest → CapMem x k ((x', k') :: rest)

/-- `(x, .tag e) ∈ c`: the tag `e` of `x` is known to exist. -/
inductive CapTagMem : Expr → Expr → Capabilities → Prop where
  | here : ∀ x e rest, CapTagMem x e ((x, .tag e) :: rest)
  | there : ∀ x e x' k' rest, CapTagMem x e rest → CapTagMem x e ((x', k') :: rest)

/-- `(x, .attr a) ∈ c`: the attribute `a` of `x` is known to exist. -/
inductive CapAttrMem : Expr → Attr → Capabilities → Prop where
  | here : ∀ x a rest, CapAttrMem x a ((x, .attr a) :: rest)
  | there : ∀ x a x' k' rest, CapAttrMem x a rest → CapAttrMem x a ((x', k') :: rest)

/-- `CapMerge c₁ c₂ c`: `c` interleaves `c₁` and `c₂`, possibly sharing equal heads. Every
    such `c` has the same elements as `c₁ ∪ c₂`, which is all `typeOf` relies on. -/
inductive CapMerge : Capabilities → Capabilities → Capabilities → Prop where
  | nil : CapMerge [] [] []
  | left : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge ((x, k) :: c₁) c₂ ((x, k) :: c)
  | right : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge c₁ ((x, k) :: c₂) ((x, k) :: c)
  | both : ∀ x k c₁ c₂ c, CapMerge c₁ c₂ c → CapMerge ((x, k) :: c₁) ((x, k) :: c₂) ((x, k) :: c)

/-- Every capability of the first list is in the second. -/
inductive CapSubset : Capabilities → Capabilities → Prop where
  | nil : CapSubset [] c
  | cons : ∀ x k rest c, CapMem x k c → CapSubset rest c → CapSubset ((x, k) :: rest) c

/-- The capabilities of `c₁` that are also in `c₂` (`c₁ ∩ c₂`). -/
def capIntersect (c₁ c₂ : Capabilities) : Capabilities :=
  c₁.filter (fun (x, k) => c₂.any (fun (x', k') => x' == x && k' == k))

/-! ## Attribute access helpers -/

/-- `hasAttrInRecord`: `x has a` for a receiver of record type `rty` that declares `a`. -/
inductive HasAttrInRecord : RecordType → Expr → Attr → Capabilities → Bool → CedarType →
    Capabilities → Prop where
  | found_in_caps : ∀ rty x a c knownToExist qty, CapAttrMem x a c → MapContains (id a) qty rty →
      HasAttrInRecord rty x a c knownToExist (.bool .tt) []
  | found_required_known : ∀ rty x a c ty, MapContains a (.required ty) rty →
      HasAttrInRecord rty x a c true (.bool .tt) []
  | found_not_known : ∀ rty x a c qty, MapContains a qty rty → ¬ CapAttrMem x a c →
      HasAttrInRecord rty x a c false (.bool .anyBool) [(x, .attr a)]
  | found_optional_known : ∀ rty x a c ty, MapContains a (.optional ty) rty → ¬ CapAttrMem x a c →
      HasAttrInRecord rty x a c true (.bool .anyBool) [(x, .attr a)]

/-- `getAttrInRecord`: `x.a` for a receiver of record type `rty`. -/
inductive GetAttrInRecord : RecordType → Expr → Attr → Capabilities → CedarType → Prop where
  | required : ∀ rty x a c aty, MapContains a (.required aty) rty → GetAttrInRecord rty x a c aty
  | optional : ∀ rty x a c aty, CapAttrMem x a c → MapContains (id a) (.optional aty) rty → GetAttrInRecord rty x a c aty

/-! ## Entity schema lookups -/

/-- The standard entity type `ety` has ancestor types `ancs`. -/
inductive MapContainsAncestors : EntityType → Set EntityType → EntitySchema → Prop where
  | here : ∀ ety ancs attrs tags rest,
    MapContainsAncestors ety ancs (.mk ((ety, .standard ⟨ancs, attrs, tags⟩) :: rest))
  | there : ∀ ety ancs k' v' rest,
    MapContainsAncestors ety ancs (.mk rest) →
    MapContainsAncestors ety ancs (.mk ((k', v') :: rest))

/-- The standard entity type `ety` has attributes `attrs` (`EntitySchema.attrs?`). -/
inductive MapContainsAttrs : EntityType → RecordType → EntitySchema → Prop where
  | here : ∀ ety ancs attrs tags rest,
    MapContainsAttrs ety attrs (.mk ((ety, .standard ⟨ancs, attrs, tags⟩) :: rest))
  | there : ∀ ety attrs k' v' rest,
    MapContainsAttrs ety attrs (.mk rest) →
    MapContainsAttrs ety attrs (.mk ((k', v') :: rest))

/-- The standard entity type `ety` has tags of type `ty` (`EntitySchema.tags?`). -/
inductive MapContainsTagType : EntityType → CedarType → EntitySchema → Prop where
  | here : ∀ ety ty ancs attrs rest,
    MapContainsTagType ety ty (.mk ((ety, .standard ⟨ancs, attrs, .some ty⟩) :: rest))
  | there : ∀ ety ty k' v' rest,
    MapContainsTagType ety ty (.mk rest) →
    MapContainsTagType ety ty (.mk ((k', v') :: rest))

/-- The standard entity type `ety` has no tags. -/
inductive MapContainsNoTags : EntityType → EntitySchema → Prop where
  | here : ∀ ety ancs attrs rest,
    MapContainsNoTags ety (.mk ((ety, .standard ⟨ancs, attrs, .none⟩) :: rest))
  | there : ∀ ety k' v' rest,
    MapContainsNoTags ety (.mk rest) →
    MapContainsNoTags ety (.mk ((k', v') :: rest))

/-- `ety` is an enumerated entity type with members `eids`, by its first binding. -/
inductive MapContainsEnum : EntityType → Set String → EntitySchema → Prop where
  | here : ∀ ety eids rest,
    MapContainsEnum ety eids (.mk ((ety, .enum eids) :: rest))
  | there : ∀ ety eids k' v' rest,
    k' ≠ ety →
    MapContainsEnum ety eids (.mk rest) →
    MapContainsEnum ety eids (.mk ((k', v') :: rest))

/-! ## Entity ancestry -/

/-- Some action of entity type `ety₁` has an ancestor of entity type `ety₂`. Mirrors
    `ActionSchema.maybeDescendentOf`, which `TypeEnv.descendentOf` consults for an entity
    type that the entity schema does not declare (an action type). -/
inductive MaybeActionDescendentOf : ActionSchema → EntityType → EntityType → Prop where
  | mk : ∀ acts uid entry anc,
    MapContains uid entry acts →
    SetContains anc entry.ancestors →
    MaybeActionDescendentOf acts uid.ty anc.ty

/-- `TypeEnv.descendentOf`: an entity of type `ety₁` may be a member of one of type `ety₂`. -/
inductive DescendentOf : EntitySchema → ActionSchema → EntityType → EntityType → Prop where
  | refl : ∀ ets acts ety, DescendentOf ets acts ety ety
  | ancestor : ∀ ets acts ety₁ ety₂ ancs,
    MapContainsAncestors ety₁ ancs ets →
    SetContains ety₂ ancs →
    DescendentOf ets acts ety₁ ety₂
  -- An action type (not in `ets`) descends from `ety₂` when some action of that type has
  -- an ancestor of type `ety₂`.
  | action : ∀ ets acts ety₁ ety₂,
    MapNotContainsKey ety₁ ets →
    MaybeActionDescendentOf acts ety₁ ety₂ →
    DescendentOf ets acts ety₁ ety₂

/-- `TypeEnv.descendentOf` is false: `ety₁` is a declared (standard or enumerated) entity type
    other than `ety₂` that does not list `ety₂` among its ancestor types. -/
inductive NotDescendentOf : EntitySchema → ActionSchema → EntityType → EntityType → Prop where
  | diff : ∀ ets acts ety₁ ety₂ ancs,
    ety₁ ≠ ety₂ →
    MapContainsAncestors ety₁ ancs ets →
    Not (SetContains ety₂ ancs) →
    NotDescendentOf ets acts ety₁ ety₂
  -- An enum entity type has no ancestors, so it descends from nothing but itself.
  | enum : ∀ ets acts ety₁ ety₂ eids,
    ety₁ ≠ ety₂ →
    MapContainsEnum ety₁ eids ets →
    NotDescendentOf ets acts ety₁ ety₂

/-! ## Action hierarchy -/

/-- `ActionSchema.descendentOf uid₁ uid₂` for an action `uid₁`: `uid₁` is `uid₂` or lists it
    among its ancestors. -/
inductive ActionDescendentOf : ActionSchema → EntityUID → EntityUID → Prop where
  | refl : ∀ acts uid entry, MapContains uid entry acts → ActionDescendentOf acts uid uid
  | ancestor : ∀ acts uid₁ uid₂ entry,
    MapContains uid₁ entry acts →
    SetContains uid₂ entry.ancestors →
    ActionDescendentOf acts uid₁ uid₂

/-- Some literal entity in the set `xs` is an action-descendent target of `uid₁`.
Mirrors the functional `uids.any (acts.descendentOf uid₁ ·)` used by `typeOfInₛ`:
`x in [set]` is `tt` iff the set actually *contains* an ancestor of `x`. -/
inductive ActionInSet : ActionSchema → EntityUID → List Expr → Prop where
  | here : ∀ acts uid₁ uid₂ rest,
      ActionDescendentOf acts uid₁ uid₂ →
      ActionInSet acts uid₁ (.lit (.entityUID uid₂) :: rest)
  | there : ∀ acts uid₁ x rest,
      ActionInSet acts uid₁ rest →
      ActionInSet acts uid₁ (x :: rest)

/-- `ActionSchema.descendentOf uid₁ uid₂` is false for an action `uid₁`. -/
inductive NotActionDescendentOf : ActionSchema → EntityUID → EntityUID → Prop where
  | diff : ∀ acts uid₁ uid₂ entry,
    uid₁ ≠ uid₂ →
    MapContains uid₁ entry acts →
    Not (SetContains uid₂ entry.ancestors) →
    NotActionDescendentOf acts uid₁ uid₂

/-! ## Tags -/

/-- Entities of type `ety` have tags of type `ty`. -/
inductive HasTagSchema : EntitySchema → EntityType → CedarType → Prop where
  | mk : ∀ ets ety ty,
    MapContainsTagType ety ty ets →
    HasTagSchema ets ety ty

/-- Entities of the declared entity type `ety` have no tags. -/
inductive NoTags : EntitySchema → EntityType → Prop where
  | none : ∀ ets ety,
    MapContainsNoTags ety ets →
    NoTags ets ety
  -- An enum entity type carries no tags (`tags?` returns the empty tag set).
  | enum : ∀ ets ety eids,
    MapContainsEnum ety eids ets →
    NoTags ets ety

/-- A nonempty list of `ipaddr` types. -/
inductive IpAddrTypes : List CedarType → Prop where
  | one : IpAddrTypes [.ext .ipAddr]
  | cons : ∀ tys, IpAddrTypes tys → IpAddrTypes (.ext .ipAddr :: tys)

/-! ## Set literals -/

/-- `AllLub acc tys ty`: folding `⊔` over `tys` starting from `acc` gives `ty`
    (`tys.foldlM lub? acc = some ty`). -/
inductive AllLub : CedarType → List CedarType → CedarType → Prop where
  | nil : ∀ ty, AllLub ty [] ty
  | cons : ∀ acc hd tl lubTy result, Lub acc hd lubTy → AllLub lubTy tl result → AllLub acc (hd :: tl) result

/-! ## Extension function calls -/

/-- The string parses as a decimal. -/
inductive ValidDecimal : String → Prop where
  | mk : ∀ s d, Cedar.Spec.Ext.Decimal.decimal s = some d → ValidDecimal s

/-- The string parses as an IP address or range. -/
inductive ValidIP : String → Prop where
  | mk : ∀ s ip, Cedar.Spec.Ext.IPAddr.ip s = some ip → ValidIP s

/-- The string parses as a datetime. -/
inductive ValidDatetime : String → Prop where
  | mk : ∀ s dt, Cedar.Spec.Ext.Datetime.parse s = some dt → ValidDatetime s

/-- The string parses as a duration. -/
inductive ValidDuration : String → Prop where
  | mk : ∀ s dur, Cedar.Spec.Ext.Datetime.Duration.parse s = some dur → ValidDuration s

/-! ## Literal operands -/

/-- Both expressions are literals. `typeOf` decides `==` on two literals exactly. -/
inductive BothLit : Expr → Expr → Prop where
  | mk : ∀ p₁ p₂, BothLit (.lit p₁) (.lit p₂)

/-- `x₁` is an action literal and `x₂` an entity literal: `typeOf` types `x₁ in x₂` using the
    action hierarchy. -/
inductive IsActionLitMem : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ uid₂ acts entry,
    MapContains uid₁ entry acts →
    IsActionLitMem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂)) acts

/-- `x₁` is an action literal and `x₂` a set of entity literals: `typeOf` types `x₁ in x₂`
    using the action hierarchy. -/
inductive IsActionLitMemSet : Expr → Expr → ActionSchema → Prop where
  | mk : ∀ uid₁ xs acts entry,
    MapContains uid₁ entry acts →
    (∀ x, x ∈ xs → ∃ uid, x = .lit (.entityUID uid)) →
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts

/-! ## Record literals: key order

`SortsTo` sorts a record literal's attributes by key, as `Map.make` does, and holds only when the
keys are distinct. -/

/-- `KeyAbove lb a` holds when `a` strictly exceeds the lower bound `lb` (`none` acts as −∞).
    The comparison is `<` on `Attr = String` (lexicographic by codepoint). -/
inductive KeyAbove : Option Attr → Attr → Prop where
  | none : ∀ a, KeyAbove none a
  | some : ∀ b a, b < a → KeyAbove (some b) a

/-- `InsertSortedField ax axs axs'`: inserting `ax` into `axs` by key gives `axs'`. Mirrors
    `List.insertCanonical Prod.fst`, except that there is no rule for a key already in `axs`. -/
inductive InsertSortedField : (Attr × Expr) → List (Attr × Expr) → List (Attr × Expr) → Prop where
  | nil : ∀ a x, InsertSortedField (a, x) [] [(a, x)]
  | here : ∀ a x a' x' axs,
    a < a' →
    InsertSortedField (a, x) ((a', x') :: axs) ((a, x) :: (a', x') :: axs)
  | there : ∀ a x a' x' axs axs',
    a' < a →
    InsertSortedField (a, x) axs axs' →
    InsertSortedField (a, x) ((a', x') :: axs) ((a', x') :: axs')

/-- `SortsTo axs axs'`: `axs'` is `axs` sorted by key, by insertion sort with strict `<`
    (mirroring `List.canonicalize Prod.fst`), so the keys of `axs` are distinct. -/
inductive SortsTo : List (Attr × Expr) → List (Attr × Expr) → Prop where
  | nil : SortsTo [] []
  | cons : ∀ ax axs axs' axs'',
    SortsTo axs axs' →
    InsertSortedField ax axs' axs'' →
    SortsTo (ax :: axs) axs''

/-! ## Attribute steps on an already-typed receiver -/

/-- A Boolean type other than `.ff`. -/
inductive NotFf : BoolType → Prop where
  | tt : NotFf .tt
  | anyBool : NotFf .anyBool

/-- `typeOfHasAttr`: `x has a`, for a receiver `x` of type `ty`, has type `.bool b` and earns
    capabilities `ci`. -/
inductive HasAttrOn : TypeEnv → CedarType → Expr → Attr → Capabilities → BoolType →
    Capabilities → Prop where
  | record : ∀ env rty x a c b ci,
    HasAttrInRecord rty x a c true (.bool b) ci →
    HasAttrOn env (.record rty) x a c b ci
  | recordNotFound : ∀ env rts x a c,
    MapNotContainsKey a (.mk rts) →
    HasAttrOn env (.record (.mk rts)) x a c .ff []
  | entity : ∀ ets acts reqty ety rty x a c b ci,
    MapContainsAttrs ety rty ets →
    HasAttrInRecord rty x a c false (.bool b) ci →
    HasAttrOn ⟨ets, acts, reqty⟩ (.entity ety) x a c b ci
  | entityNotFound : ∀ ets acts reqty ety rty x a c,
    MapContainsAttrs ety rty ets →
    MapNotContainsKey a rty →
    HasAttrOn ⟨ets, acts, reqty⟩ (.entity ety) x a c .ff []
  -- An enum entity type has no attributes (`attrs?` gives the empty record).
  | enum : ∀ ets acts reqty ety eids x a c,
    MapContainsEnum ety eids ets →
    HasAttrOn ⟨ets, acts, reqty⟩ (.entity ety) x a c .ff []
  -- Action entities have no attributes.
  | action : ∀ ets acts reqty ety eid entry x a c,
    MapNotContainsKey ety ets →
    MapContainsPairKey ety eid entry acts →
    HasAttrOn ⟨ets, acts, reqty⟩ (.entity ety) x a c .ff []

/-- `typeOfGetAttr`: `x.a`, for a receiver `x` of type `ty`, has type `aty`. -/
inductive GetAttrOn : TypeEnv → CedarType → Expr → Attr → Capabilities → CedarType → Prop where
  | record : ∀ env rty x a c aty,
    GetAttrInRecord rty x a c aty →
    GetAttrOn env (.record rty) x a c aty
  | entity : ∀ ets acts reqty ety rty x a c aty,
    MapContainsAttrs ety rty ets →
    GetAttrInRecord rty x a c aty →
    GetAttrOn ⟨ets, acts, reqty⟩ (.entity ety) x a c aty

/-- `typeOfExtHasAttr`: `x has a.as` for a receiver of type `ty`. -/
inductive ExtHasAttrChain : TypeEnv → CedarType → Expr → Attr → List Attr → Capabilities →
    BoolType → Capabilities → Prop where
  | last : ∀ env ty x a c b ci,
    HasAttrOn env ty x a c b ci →
    ExtHasAttrChain env ty x a [] c b ci
  | absent : ∀ env ty x a a' as c ci,
    HasAttrOn env ty x a c .ff ci →
    ExtHasAttrChain env ty x a (a' :: as) c .ff ci
  | restFf : ∀ env ty x a a' as c hb ci cc tyNext cr,
    HasAttrOn env ty x a c hb ci →
    NotFf hb →
    CapMerge c ci cc →
    GetAttrOn env ty x a cc tyNext →
    ExtHasAttrChain env tyNext (.getAttr x a) a' as cc .ff cr →
    ExtHasAttrChain env ty x a (a' :: as) c .ff []
  | restTt : ∀ env ty x a a' as c hb ci cc tyNext cr cout,
    HasAttrOn env ty x a c hb ci →
    NotFf hb →
    CapMerge c ci cc →
    GetAttrOn env ty x a cc tyNext →
    ExtHasAttrChain env tyNext (.getAttr x a) a' as cc .tt cr →
    CapMerge ci cr cout →
    ExtHasAttrChain env ty x a (a' :: as) c hb cout
  | restAnyBool : ∀ env ty x a a' as c hb ci cc tyNext cr cout,
    HasAttrOn env ty x a c hb ci →
    NotFf hb →
    CapMerge c ci cc →
    GetAttrOn env ty x a cc tyNext →
    ExtHasAttrChain env tyNext (.getAttr x a) a' as cc .anyBool cr →
    CapMerge ci cr cout →
    ExtHasAttrChain env ty x a (a' :: as) c .anyBool cout

/-! ## Syntactic conditions on expressions -/

/-! ### Declared entities (`checkEntities`) -/

mutual
/-- `checkEntities` succeeds: every entity literal is valid and every `is` type declared. -/
inductive EntitiesDeclared : EntitySchema → ActionSchema → Expr → Prop where
  | litBool : ∀ ets acts b, EntitiesDeclared ets acts (.lit (.bool b))
  | litInt : ∀ ets acts i, EntitiesDeclared ets acts (.lit (.int i))
  | litString : ∀ ets acts s, EntitiesDeclared ets acts (.lit (.string s))
  | litEntity : ∀ ets acts ety eid, ValidEntityUID ety eid ets acts →
      EntitiesDeclared ets acts (.lit (.entityUID ⟨ety, eid⟩))
  | var : ∀ ets acts v, EntitiesDeclared ets acts (.var v)
  | ite : ∀ ets acts a b c, EntitiesDeclared ets acts a → EntitiesDeclared ets acts b →
      EntitiesDeclared ets acts c → EntitiesDeclared ets acts (.ite a b c)
  | and : ∀ ets acts a b, EntitiesDeclared ets acts a → EntitiesDeclared ets acts b →
      EntitiesDeclared ets acts (.and a b)
  | or : ∀ ets acts a b, EntitiesDeclared ets acts a → EntitiesDeclared ets acts b →
      EntitiesDeclared ets acts (.or a b)
  | is : ∀ ets acts ety a, ValidEntityType ety ets acts → EntitiesDeclared ets acts a →
      EntitiesDeclared ets acts (.unaryApp (.is ety) a)
  | not : ∀ ets acts a, EntitiesDeclared ets acts a → EntitiesDeclared ets acts (.unaryApp .not a)
  | neg : ∀ ets acts a, EntitiesDeclared ets acts a → EntitiesDeclared ets acts (.unaryApp .neg a)
  | isEmpty : ∀ ets acts a, EntitiesDeclared ets acts a →
      EntitiesDeclared ets acts (.unaryApp .isEmpty a)
  | like : ∀ ets acts p a, EntitiesDeclared ets acts a →
      EntitiesDeclared ets acts (.unaryApp (.like p) a)
  | binaryApp : ∀ ets acts op a b, EntitiesDeclared ets acts a → EntitiesDeclared ets acts b →
      EntitiesDeclared ets acts (.binaryApp op a b)
  | getAttr : ∀ ets acts a k, EntitiesDeclared ets acts a → EntitiesDeclared ets acts (.getAttr a k)
  | hasAttr : ∀ ets acts a k, EntitiesDeclared ets acts a → EntitiesDeclared ets acts (.hasAttr a k)
  | extHasAttr : ∀ ets acts a k ks, EntitiesDeclared ets acts a →
      EntitiesDeclared ets acts (.extHasAttr a k ks)
  | set : ∀ ets acts xs, EntitiesDeclaredList ets acts xs → EntitiesDeclared ets acts (.set xs)
  | record : ∀ ets acts axs, EntitiesDeclaredRecord ets acts axs →
      EntitiesDeclared ets acts (.record axs)
  | call : ∀ ets acts f xs, EntitiesDeclaredList ets acts xs →
      EntitiesDeclared ets acts (.call f xs)

/-- `EntitiesDeclared` for each expression of a list. -/
inductive EntitiesDeclaredList : EntitySchema → ActionSchema → List Expr → Prop where
  | nil : ∀ ets acts, EntitiesDeclaredList ets acts []
  | cons : ∀ ets acts x xs, EntitiesDeclared ets acts x → EntitiesDeclaredList ets acts xs →
      EntitiesDeclaredList ets acts (x :: xs)

/-- `EntitiesDeclared` for each field of a record literal. -/
inductive EntitiesDeclaredRecord : EntitySchema → ActionSchema → List (Attr × Expr) → Prop where
  | nil : ∀ ets acts, EntitiesDeclaredRecord ets acts []
  | cons : ∀ ets acts a x axs, EntitiesDeclared ets acts x → EntitiesDeclaredRecord ets acts axs →
      EntitiesDeclaredRecord ets acts ((a, x) :: axs)
end

/-! ### The image of the parser -/

/-- Cedar's reserved identifiers, and the reserved name component `__cedar`. -/
def reservedIdents : List String :=
  ["true", "false", "if", "then", "else", "in", "is", "like", "has", "__cedar"]

/-- A Cedar identifier, `[_a-zA-Z][_a-zA-Z0-9]*`, not reserved (Rust's `is_normalized_ident`). -/
def isCedarIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => (c.isAlpha || c == '_') && cs.all (fun c => c.isAlphanum || c == '_') &&
      !(reservedIdents.contains s)

/-- The attributes of an extended `has` as the parser writes them: identifiers, unless there is
    only one. -/
def extHasAttrsParsed (a : Attr) (as : List Attr) : Bool :=
  as.isEmpty || (a :: as).all isCedarIdent

/-- The expression is one the parser can produce: distinct record keys, and identifier
    extended-`has` paths. -/
inductive ParserImage : Expr → Prop where
  | lit : ∀ p, ParserImage (.lit p)
  | var : ∀ v, ParserImage (.var v)
  | ite : ∀ a b c, ParserImage a → ParserImage b → ParserImage c →
      ParserImage (.ite a b c)
  | and : ∀ a b, ParserImage a → ParserImage b → ParserImage (.and a b)
  | or : ∀ a b, ParserImage a → ParserImage b → ParserImage (.or a b)
  | unaryApp : ∀ op a, ParserImage a → ParserImage (.unaryApp op a)
  | binaryApp : ∀ op a b, ParserImage a → ParserImage b →
      ParserImage (.binaryApp op a b)
  | getAttr : ∀ a k, ParserImage a → ParserImage (.getAttr a k)
  | hasAttr : ∀ a k, ParserImage a → ParserImage (.hasAttr a k)
  | extHasAttr : ∀ a k ks, extHasAttrsParsed k ks = true → ParserImage a →
      ParserImage (.extHasAttr a k ks)
  | set : ∀ xs, (∀ x ∈ xs, ParserImage x) → ParserImage (.set xs)
  | record : ∀ axs, (axs.map Prod.fst).Nodup → (∀ x ∈ axs.map Prod.snd, ParserImage x) →
      ParserImage (.record axs)
  | call : ∀ f xs, (∀ x ∈ xs, ParserImage x) → ParserImage (.call f xs)

/-! ## Strictness flags

`decl` requires declared entities (`checkEntities`) and `syn` the parser's image (`ParserImage`),
including in the operands `typeOf` skips. With both `false`, `HasType` is `typeOf`. -/

/-- The target type `T` of an `is` test, when the `decl` flag is `b`. With `b = true` it must
    be a declared entity type (`checkEntities`); with `b = false` it is arbitrary (`typeOf`
    does not check it). -/
inductive IsTargetOf : Bool → TypeEnv → EntityType → Prop where
  | strict : ∀ b env T, ValidEntityType T env.ets env.acts → IsTargetOf b env T
  | lax : ∀ env T, IsTargetOf false env T

/-- `EntitiesDeclared ets acts x` when the `decl` flag is `b = true`; nothing when `b = false`. -/
inductive DeclIf : Bool → EntitySchema → ActionSchema → Expr → Prop where
  | yes : ∀ b ets acts x, EntitiesDeclared ets acts x → DeclIf b ets acts x
  | no : ∀ ets acts x, DeclIf false ets acts x

/-- `ParserImage x` when the `syn` flag is `b = true`; nothing when `b = false`. -/
inductive ParserImageIf : Bool → Expr → Prop where
  | yes : ∀ b x, ParserImage x → ParserImageIf b x
  | no : ∀ x, ParserImageIf false x

/-- The attributes of an extended `has` are `extHasAttrsParsed` when the `syn` flag is
    `b = true`; arbitrary when `b = false`. -/
inductive ExtHasIf : Bool → Attr → List Attr → Prop where
  | yes : ∀ b a as, extHasAttrsParsed a as = true → ExtHasIf b a as
  | no : ∀ a as, ExtHasIf false a as

/-- An operand that `typeOf` skips (short-circuited, or the untaken branch of an `if`), so it
    need not be well typed. It must still meet the syntactic conditions the flags `decl` and
    `syn` select. -/
inductive DeadOperand (decl syn : Bool) : TypeEnv → Expr → Prop where
  | mk : ∀ env x, DeclIf decl env.ets env.acts x → ParserImageIf syn x → DeadOperand decl syn env x

/-! ## The typing relation -/

mutual

/-- `HasType decl syn x c env ty cout`: `x` has type `ty` and earns `cout` under `c`. -/
inductive HasType (decl syn : Bool) : Expr → Capabilities → TypeEnv → CedarType → Capabilities → Prop where
  /- ### Literals -/
  | litBoolTrue :
    ∀ c ets acts reqty,
    HasType decl syn (.lit (.bool true)) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  | litBoolFalse :
    ∀ c ets acts reqty,
    HasType decl syn (.lit (.bool false)) c ⟨ets, acts, reqty⟩ (.bool .ff) []
  | litInt :
    ∀ i c ets acts reqty,
    HasType decl syn (.lit (.int i)) c ⟨ets, acts, reqty⟩ .int []
  | litString :
    ∀ s c ets acts reqty,
    HasType decl syn (.lit (.string s)) c ⟨ets, acts, reqty⟩ .string []
  | litEntity :
    ∀ ety eid c ets acts reqty,
    ValidEntityUID ety eid ets acts →
    HasType decl syn (.lit (.entityUID ⟨ety, eid⟩)) c ⟨ets, acts, reqty⟩ (.entity ety) []

  /- ### Variables -/
  | varPrincipal :
    ∀ c ets acts princ action resource ctx,
    HasType decl syn (.var .principal) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ (.entity princ) []
  | varAction :
    ∀ c ets acts princ actionTy actionEid resource ctx,
    HasType decl syn (.var .action) c ⟨ets, acts, ⟨princ, ⟨actionTy, actionEid⟩, resource, ctx⟩⟩ (.entity actionTy) []
  | varResource :
    ∀ c ets acts princ action resource ctx,
    HasType decl syn (.var .resource) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ (.entity resource) []
  | varContext :
    ∀ c ets acts princ action resource ctx,
    HasType decl syn (.var .context) c ⟨ets, acts, ⟨princ, action, resource, ctx⟩⟩ (.record ctx) []

  /- ### Unary: not -/
  | unaryAppNotTt :
    ∀ x₁ c env,
    HasType decl syn x₁ c env (.bool .tt) oc1 →
    HasType decl syn (.unaryApp .not x₁) c env (.bool .ff) []
  | unaryAppNotFf :
    ∀ x₁ c env,
    HasType decl syn x₁ c env (.bool .ff) oc2 →
    HasType decl syn (.unaryApp .not x₁) c env (.bool .tt) []
  | unaryAppNotAny :
    ∀ x₁ c env,
    HasType decl syn x₁ c env (.bool .anyBool) oc3 →
    HasType decl syn (.unaryApp .not x₁) c env (.bool .anyBool) []

  /- ### Unary: neg -/
  | unaryAppNeg :
    ∀ x₁ c env,
    HasType decl syn x₁ c env .int oc4 →
    HasType decl syn (.unaryApp .neg x₁) c env .int []

  /- ### Unary: isEmpty -/
  | unaryAppIsEmpty :
    ∀ x₁ c env elemTy,
    HasType decl syn x₁ c env (.set elemTy) oc5 →
    HasType decl syn (.unaryApp .isEmpty x₁) c env (.bool .anyBool) []

  /- ### Unary: like -/
  | unaryAppLike :
    ∀ pat x₁ c env,
    HasType decl syn x₁ c env .string oc6 →
    HasType decl syn (.unaryApp (.like pat) x₁) c env (.bool .anyBool) []

  /- ### Unary: is (true) -/
  | unaryAppIsTrue :
    ∀ ety x₁ c env,
    IsTargetOf decl env ety →
    HasType decl syn x₁ c env (.entity ety) oc7 →
    HasType decl syn (.unaryApp (.is ety) x₁) c env (.bool .tt) []

  /- ### Unary: is (false) -/
  -- `typeOf` does not require the tested type `ety₁` to be declared, but `validate` runs
  -- `checkEntities` first, which rejects `x is ety₁` for an undeclared `ety₁` (`IsTargetOf`).
  | unaryAppIsFalse :
    ∀ ety₁ ety₂ x₁ c env,
    ValidEntityType ety₂ env.ets env.acts →
    IsTargetOf decl env ety₁ →
    ety₁ ≠ ety₂ →
    HasType decl syn x₁ c env (.entity ety₂) oc8 →
    HasType decl syn (.unaryApp (.is ety₁) x₁) c env (.bool .ff) []

  /- ### Binary: eq on literals -/
  | binaryAppEqLitSame :
    ∀ p c env ty,
    HasType decl syn (.lit p) c env ty oc9 →
    HasType decl syn (.binaryApp .eq (.lit p) (.lit p)) c env (.bool .tt) []
  | binaryAppEqLitDiff :
    ∀ p₁ p₂ c env ty₁ ty₂,
    PrimNeq p₁ p₂ →
    HasType decl syn (.lit p₁) c env ty₁ oc10 →
    HasType decl syn (.lit p₂) c env ty₂ oc11 →
    HasType decl syn (.binaryApp .eq (.lit p₁) (.lit p₂)) c env (.bool .ff) []

  /- ### Binary: eq non-literal (lub exists) -/
  | binaryAppEqNonLitLub :
    ∀ x₁ x₂ c env t₁ t₂ lubTy,
    Lub t₁ t₂ lubTy →
    HasType decl syn x₁ c env t₁ oc12 →
    HasType decl syn x₂ c env t₂ oc13 →
    ¬ BothLit x₁ x₂ →
    HasType decl syn (.binaryApp .eq x₁ x₂) c env (.bool .anyBool) []

  /- ### Binary: eq entity-entity different -/
  | binaryAppEqEntityDiff :
    ∀ x₁ x₂ c env ety₁ ety₂,
    ValidEntityType ety₁ env.ets env.acts →
    ValidEntityType ety₂ env.ets env.acts →
    ety₁ ≠ ety₂ →
    HasType decl syn x₁ c env (.entity ety₁) oc14 →
    HasType decl syn x₂ c env (.entity ety₂) oc15 →
    ¬ BothLit x₁ x₂ →
    HasType decl syn (.binaryApp .eq x₁ x₂) c env (.bool .ff) []

  /- ### Binary: arithmetic -/
  | binaryAppLessInt :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env .int oc16 →
    HasType decl syn x₂ c env .int oc17 →
    HasType decl syn (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessDatetime :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env (.ext .datetime) oc18 →
    HasType decl syn x₂ c env (.ext .datetime) oc19 →
    HasType decl syn (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessDuration :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env (.ext .duration) oc20 →
    HasType decl syn x₂ c env (.ext .duration) oc21 →
    HasType decl syn (.binaryApp .less x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqInt :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env .int oc22 →
    HasType decl syn x₂ c env .int oc23 →
    HasType decl syn (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqDatetime :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env (.ext .datetime) oc24 →
    HasType decl syn x₂ c env (.ext .datetime) oc25 →
    HasType decl syn (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppLessEqDuration :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env (.ext .duration) oc26 →
    HasType decl syn x₂ c env (.ext .duration) oc27 →
    HasType decl syn (.binaryApp .lessEq x₁ x₂) c env (.bool .anyBool) []
  | binaryAppAdd :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env .int oc28 →
    HasType decl syn x₂ c env .int oc29 →
    HasType decl syn (.binaryApp .add x₁ x₂) c env .int []
  | binaryAppSub :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env .int oc30 →
    HasType decl syn x₂ c env .int oc31 →
    HasType decl syn (.binaryApp .sub x₁ x₂) c env .int []
  | binaryAppMul :
    ∀ x₁ x₂ c env,
    HasType decl syn x₁ c env .int oc32 →
    HasType decl syn x₂ c env .int oc33 →
    HasType decl syn (.binaryApp .mul x₁ x₂) c env .int []

  /- ### Binary: set operations -/
  | binaryAppContains :
    ∀ x₁ x₂ c env t₂ elemTy,
    LubCompat t₂ elemTy →
    HasType decl syn x₁ c env (.set elemTy) oc34 →
    HasType decl syn x₂ c env t₂ oc35 →
    HasType decl syn (.binaryApp .contains x₁ x₂) c env (.bool .anyBool) []
  | binaryAppContainsAll :
    ∀ x₁ x₂ c env elemTy₁ elemTy₂,
    LubCompat elemTy₁ elemTy₂ →
    HasType decl syn x₁ c env (.set elemTy₁) oc36 →
    HasType decl syn x₂ c env (.set elemTy₂) oc37 →
    HasType decl syn (.binaryApp .containsAll x₁ x₂) c env (.bool .anyBool) []
  | binaryAppContainsAny :
    ∀ x₁ x₂ c env elemTy₁ elemTy₂,
    LubCompat elemTy₁ elemTy₂ →
    HasType decl syn x₁ c env (.set elemTy₁) oc38 →
    HasType decl syn x₂ c env (.set elemTy₂) oc39 →
    HasType decl syn (.binaryApp .containsAny x₁ x₂) c env (.bool .anyBool) []

  /- ### Binary: mem (generic — excludes action-literal cases) -/
  -- The `ValidEntityType` premises are implied by the operand typings (see `ValidEntityType`).
  | binaryAppMemEntityEntity :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    DescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc40 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) oc41 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySame :
    ∀ x₁ x₂ c ets acts reqty ety,
    ValidEntityType ety ets acts →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc42 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.entity ety) oc43 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySet :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    DescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc44 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc45 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []
  | binaryAppMemEntitySetSame :
    ∀ x₁ x₂ c ets acts reqty ety,
    ValidEntityType ety ets acts →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc46 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety)) oc47 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) []

  /- ### Binary: mem — false (not descendent, excludes action-literal cases) -/
  | binaryAppMemEntityEntityFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    ValidEntityType ety₂ ets acts →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc48 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) oc49 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []
  | binaryAppMemEntitySetFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    ValidEntityType ety₁ ets acts →
    ValidEntityType ety₂ ets acts →
    NotDescendentOf ets acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc50 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc51 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — false (action-typed operand, non-literal) -/
  -- For an operand type `ety₁` absent from `ets` (an action type), `typeOfInₑ`/`typeOfInₛ`
  -- fall back to `maybeDescendentOf`: `x₁ in x₂` is `.ff` unless some action of type `ety₁`
  -- has an ancestor of type `ety₂`. `NotDescendentOf` walks `ets` entries only, so these are
  -- separate rules.
  | binaryAppMemActionEntityFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    MapNotContainsKey ety₁ ets →
    ety₁ ≠ ety₂ →
    ¬ MaybeActionDescendentOf acts ety₁ ety₂ →
    ¬ IsActionLitMem x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc103 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.entity ety₂) oc104 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []
  | binaryAppMemActionSetFf :
    ∀ x₁ x₂ c ets acts reqty ety₁ ety₂,
    MapNotContainsKey ety₁ ets →
    ety₁ ≠ ety₂ →
    ¬ MaybeActionDescendentOf acts ety₁ ety₂ →
    ¬ IsActionLitMemSet x₁ x₂ acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety₁) oc105 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc106 →
    HasType decl syn (.binaryApp .mem x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — true (known action literal hierarchy) -/
  | binaryAppMemActionLitTt :
    ∀ uid₁ uid₂ c ets acts reqty,
    ActionDescendentOf acts uid₁ uid₂ →
    HasType decl syn (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc52 →
    HasType decl syn (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ (.entity uid₂.ty) oc53 →
    HasType decl syn (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  | binaryAppMemActionLitFf :
    ∀ uid₁ uid₂ c ets acts reqty,
    NotActionDescendentOf acts uid₁ uid₂ →
    HasType decl syn (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc54 →
    HasType decl syn (.lit (.entityUID uid₂)) c ⟨ets, acts, reqty⟩ (.entity uid₂.ty) oc55 →
    HasType decl syn (.binaryApp .mem (.lit (.entityUID uid₁)) (.lit (.entityUID uid₂))) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Binary: mem — action literal in set of entity literals (tt if any descendent) -/
  | binaryAppMemActionLitSetTt :
    ∀ uid₁ xs c ets acts reqty ety₂,
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ActionInSet acts uid₁ xs →
    HasType decl syn (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc56 →
    HasType decl syn (.set xs) c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc57 →
    HasType decl syn (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ (.bool .tt) []
  /- ### Binary: mem — action literal in set of entity literals (ff if no descendent) -/
  | binaryAppMemActionLitSetFf :
    ∀ uid₁ xs c ets acts reqty ety₂,
    IsActionLitMemSet (.lit (.entityUID uid₁)) (.set xs) acts →
    ¬ ActionInSet acts uid₁ xs →
    HasType decl syn (.lit (.entityUID uid₁)) c ⟨ets, acts, reqty⟩ (.entity uid₁.ty) oc58 →
    HasType decl syn (.set xs) c ⟨ets, acts, reqty⟩ (.set (.entity ety₂)) oc59 →
    HasType decl syn (.binaryApp .mem (.lit (.entityUID uid₁)) (.set xs)) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasAttr — record (attribute found) -/
  | hasAttrRecord :
    ∀ x₁ a c env rty ty caps,
    HasType decl syn x₁ c env (.record rty) oc60 →
    HasAttrInRecord rty x₁ a c true ty caps →
    HasType decl syn (.hasAttr x₁ a) c env ty caps

  /- ### hasAttr — record (attribute not found) -/
  | hasAttrRecordNotFound :
    ∀ x₁ a c env rty,
    HasType decl syn x₁ c env (.record (.mk rty)) oc61 →
    MapNotContainsKey a (.mk rty) →
    HasType decl syn (.hasAttr x₁ a) c env (.bool .ff) []

  /- ### hasAttr — entity (attribute found) -/
  | hasAttrEntity :
    ∀ x₁ a c ets acts reqty ety ty caps rty,
    MapContainsAttrs ety rty ets →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc62 →
    HasAttrInRecord rty x₁ a c false ty caps →
    HasType decl syn (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ ty caps

  /- ### hasAttr — entity (attribute not found) -/
  | hasAttrEntityNotFound :
    ∀ x₁ a c ets acts reqty ety rty,
    MapContainsAttrs ety rty ets →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc63 →
    MapNotContainsKey a rty →
    HasType decl syn (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasAttr — enum entity (no attributes) -/
  -- `EntitySchema.attrs?` gives the empty record for an enumerated entity type, so `hasAttr`
  -- on an enum-typed operand is `.bool .ff`.
  | hasAttrEnum :
    ∀ x₁ a c ets acts reqty ety eids,
    MapContainsEnum ety eids ets →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc64 →
    HasType decl syn (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasAttr — action-typed entity (no attributes) -/
  -- An action type is absent from `ets`, so `typeOfHasAttr` takes its `actionType?` branch:
  -- `hasAttr` on an action-typed operand is `.bool .ff` (action attributes not allowed).
  | hasAttrActionFf :
    ∀ x₁ a c ets acts reqty ety eid entry,
    MapNotContainsKey ety ets →
    MapContainsPairKey ety eid entry acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc109 →
    HasType decl syn (.hasAttr x₁ a) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### Extended has: `x₁ has a.as` -/
  | extHasAttr :
    ∀ x₁ a as c env ty₁ oc b cout,
    HasType decl syn x₁ c env ty₁ oc →
    ExtHasAttrChain env ty₁ x₁ a as c b cout →
    ExtHasIf syn a as →
    HasType decl syn (.extHasAttr x₁ a as) c env (.bool b) cout

  /- ### getAttr — record -/
  | getAttrRecord :
    ∀ x₁ a c env rty ty,
    HasType decl syn x₁ c env (.record rty) oc65 →
    GetAttrInRecord rty x₁ a c ty →
    HasType decl syn (.getAttr x₁ a) c env ty []

  /- ### getAttr — entity -/
  | getAttrEntity :
    ∀ x₁ a c ets acts reqty ety ty rty,
    MapContainsAttrs ety rty ets →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc66 →
    GetAttrInRecord rty x₁ a c ty →
    HasType decl syn (.getAttr x₁ a) c ⟨ets, acts, reqty⟩ ty []

  /- ### hasTag — entity has tags, not in capabilities -/
  -- `typeOfHasTag` gives `.tt` when the capability `(x₁, .tag x₂)` is available (`hasTagTt`).
  | hasTagAnyBool :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    HasTagSchema ets ety ty →
    ¬ CapTagMem x₁ x₂ c →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc67 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ .string oc68 →
    HasType decl syn (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .anyBool) [(x₁, .tag x₂)]

  /- ### hasTag — entity has tags, already in capabilities -/
  | hasTagTt :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    CapTagMem x₁ x₂ c →
    HasTagSchema ets ety ty →
    HasType decl syn (id x₁) c ⟨ets, acts, reqty⟩ (.entity ety) oc69 →
    HasType decl syn (id x₂) c ⟨ets, acts, reqty⟩ .string oc70 →
    HasType decl syn (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .tt) []

  /- ### hasTag — entity has no tags -/
  | hasTagFf :
    ∀ x₁ x₂ c ets acts reqty ety,
    NoTags ets ety →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc71 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ .string oc72 →
    HasType decl syn (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### hasTag — action-typed entity (no tags) -/
  -- An action type is absent from `ets`, so `typeOfHasTag` takes its `actionType?` branch:
  -- `hasTag` on an action-typed operand is `.bool .ff` (action tags not allowed).
  | hasTagActionFf :
    ∀ x₁ x₂ c ets acts reqty ety eid entry,
    MapNotContainsKey ety ets →
    MapContainsPairKey ety eid entry acts →
    HasType decl syn x₁ c ⟨ets, acts, reqty⟩ (.entity ety) oc107 →
    HasType decl syn x₂ c ⟨ets, acts, reqty⟩ .string oc108 →
    HasType decl syn (.binaryApp .hasTag x₁ x₂) c ⟨ets, acts, reqty⟩ (.bool .ff) []

  /- ### getTag — entity with tags, capability present -/
  | getTag :
    ∀ x₁ x₂ c ets acts reqty ety ty,
    CapTagMem x₁ x₂ c →
    HasTagSchema ets ety ty →
    HasType decl syn (id x₁) c ⟨ets, acts, reqty⟩ (.entity ety) oc73 →
    HasType decl syn (id x₂) c ⟨ets, acts, reqty⟩ .string oc74 →
    HasType decl syn (.binaryApp .getTag x₁ x₂) c ⟨ets, acts, reqty⟩ ty []

  /- ### ite — condition true (`typeOf` skips the untaken branch `x₃`) -/
  | iteTt :
    ∀ x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ cout,
    HasType decl syn x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env t₂ c₂ →
    CapMerge c₁ c₂ cout →
    DeadOperand decl syn env x₃ →
    HasType decl syn (.ite x₁ x₂ x₃) c env t₂ cout

  /- ### ite — condition false (`typeOf` skips the untaken branch `x₂`) -/
  | iteFf :
    ∀ x₁ x₂ x₃ c env c₁ t₃ c₃,
    HasType decl syn x₁ c env (.bool .ff) c₁ →
    HasType decl syn x₃ c env t₃ c₃ →
    DeadOperand decl syn env x₂ →
    HasType decl syn (.ite x₁ x₂ x₃) c env t₃ c₃

  /- ### ite — condition anyBool -/
  | iteAnyBool :
    ∀ x₁ x₂ x₃ c env c₁ c_c₁ t₂ c₂ t₃ c₃ lubTy c₁₂,
    HasType decl syn x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env t₂ c₂ →
    HasType decl syn x₃ c env t₃ c₃ →
    Lub t₂ t₃ lubTy →
    CapMerge c₁ c₂ c₁₂ →
    HasType decl syn (.ite x₁ x₂ x₃) c env lubTy (capIntersect c₁₂ c₃)

  /- ### and — short-circuit (`typeOf` skips `x₂`) -/
  | andShort :
    ∀ x₁ x₂ c env c₁,
    HasType decl syn x₁ c env (.bool .ff) c₁ →
    DeadOperand decl syn env x₂ →
    HasType decl syn (.and x₁ x₂) c env (.bool .ff) []

  /- ### and — tt then ff -/
  | andTtFf :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂,
    HasType decl syn x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env (.bool .ff) c₂ →
    HasType decl syn (.and x₁ x₂) c env (.bool .ff) []

  /- ### and — tt then tt -/
  | andTtTt :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType decl syn x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env (.bool .tt) c₂ →
    CapMerge c₁ c₂ cout →
    HasType decl syn (.and x₁ x₂) c env (.bool .tt) cout

  /- ### and — tt then anyBool -/
  | andTtAny :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType decl syn x₁ c env (.bool .tt) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env (.bool .anyBool) c₂ →
    CapMerge c₁ c₂ cout →
    HasType decl syn (.and x₁ x₂) c env (.bool .anyBool) cout

  /- ### and — anyBool then ff -/
  | andAnyFf :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂,
    HasType decl syn x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env (.bool .ff) c₂ →
    HasType decl syn (.and x₁ x₂) c env (.bool .ff) []

  /- ### and — anyBool then tt -/
  | andAnyTt :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType decl syn x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env (.bool .tt) c₂ →
    CapMerge c₁ c₂ cout →
    HasType decl syn (.and x₁ x₂) c env (.bool .anyBool) cout

  /- ### and — anyBool then anyBool -/
  | andAnyAny :
    ∀ x₁ x₂ c env c₁ c_c₁ c₂ cout,
    HasType decl syn x₁ c env (.bool .anyBool) c₁ →
    CapMerge c c₁ c_c₁ →
    HasType decl syn x₂ c_c₁ env (.bool .anyBool) c₂ →
    CapMerge c₁ c₂ cout →
    HasType decl syn (.and x₁ x₂) c env (.bool .anyBool) cout

  /- ### or — short-circuit (`typeOf` skips `x₂`) -/
  | orShort :
    ∀ x₁ x₂ c env c₁,
    HasType decl syn x₁ c env (.bool .tt) c₁ →
    DeadOperand decl syn env x₂ →
    HasType decl syn (.or x₁ x₂) c env (.bool .tt) []

  /- ### or — ff then b₂ -/
  | orFfThen :
    ∀ x₁ x₂ c env c₁ b₂ c₂,
    HasType decl syn x₁ c env (.bool .ff) c₁ →
    HasType decl syn x₂ c env (.bool b₂) c₂ →
    HasType decl syn (.or x₁ x₂) c env (.bool b₂) c₂

  /- ### or — anyBool then tt -/
  | orAnyTt :
    ∀ x₁ x₂ c env c₁ c₂,
    HasType decl syn x₁ c env (.bool .anyBool) c₁ →
    HasType decl syn x₂ c env (.bool .tt) c₂ →
    HasType decl syn (.or x₁ x₂) c env (.bool .tt) []

  /- ### or — anyBool then ff -/
  | orAnyFf :
    ∀ x₁ x₂ c env c₁ c₂,
    HasType decl syn x₁ c env (.bool .anyBool) c₁ →
    HasType decl syn x₂ c env (.bool .ff) c₂ →
    HasType decl syn (.or x₁ x₂) c env (.bool .anyBool) c₁

  /- ### or — anyBool then anyBool -/
  | orAnyAny :
    ∀ x₁ x₂ c env c₁ c₂,
    HasType decl syn x₁ c env (.bool .anyBool) c₁ →
    HasType decl syn x₂ c env (.bool .anyBool) c₂ →
    HasType decl syn (.or x₁ x₂) c env (.bool .anyBool) (capIntersect c₁ c₂)

  /- ### Set literal -/
  | set :
    ∀ x xs c env ty tyList lubTy,
    HasType decl syn x c env ty oc75 →
    HasTypeList decl syn xs c env tyList →
    AllLub ty tyList lubTy →
    HasType decl syn (.set (x :: xs)) c env (.set lubTy) []

  /- ### Record literal -/
  -- `RecordTypeOf` is indexed by `syn`: distinct keys are required exactly when `syn` is set.
  | record :
    ∀ axs c env rty,
    RecordTypeOf decl syn syn axs c env rty →
    HasType decl syn (.record axs) c env (.record rty) []

  /- ### Extension function call -/
  | callExt : ∀ xfn args c env ty,
    HasTypeExtCall decl syn xfn args c env ty →
    HasType decl syn (.call xfn args) c env ty []

/-- Typing a list of expressions. -/
inductive HasTypeList (decl syn : Bool) : List Expr → Capabilities → TypeEnv → List CedarType → Prop where
  | nil :
    ∀ c env,
    HasTypeList decl syn [] c env []
  | cons :
    ∀ x xs c env ty tys,
    HasType decl syn x c env ty oc76 →
    HasTypeList decl syn xs c env tys →
    HasTypeList decl syn (x :: xs) c env (ty :: tys)

/-- Typing a record's attributes in strictly increasing key order. -/
inductive HasTypeRecord (decl syn : Bool) : Option Attr → List (Attr × Expr) → Capabilities → TypeEnv → List (Attr × QualifiedType) → Prop where
  | nil :
    ∀ lb c env,
    HasTypeRecord decl syn lb [] c env []
  | cons :
    ∀ lb a x axs c env ty atyList,
    KeyAbove lb a →
    HasType decl syn x c env ty oc77 →
    HasTypeRecord decl syn (some a) axs c env atyList →
    HasTypeRecord decl syn lb ((a, x) :: axs) c env ((a, .required ty) :: atyList)

/-- `typeOfCall`: the type of an extension function call. Constructors take a string literal
    that parses (`ValidDecimal`, ...); for the other functions each argument type is stated
    as a `HasType` premise. -/
inductive HasTypeExtCall (decl syn : Bool) : ExtFun → List Expr → Capabilities → TypeEnv → CedarType → Prop where
  /- Construction: fn applied to a string literal. -/
  | decimal  : ∀ s c env, ValidDecimal s  → HasTypeExtCall decl syn .decimal [.lit (.string s)] c env (.ext .decimal)
  | ip       : ∀ s c env, ValidIP s       → HasTypeExtCall decl syn .ip [.lit (.string s)] c env (.ext .ipAddr)
  | datetime : ∀ s c env, ValidDatetime s → HasTypeExtCall decl syn .datetime [.lit (.string s)] c env (.ext .datetime)
  | duration : ∀ s c env, ValidDuration s → HasTypeExtCall decl syn .duration [.lit (.string s)] c env (.ext .duration)
  /- Methods: argument types stated directly as `HasType` premises. -/
  | lessThan : ∀ a b c env,
    HasType decl syn a c env (.ext .decimal) oc96 → HasType decl syn b c env (.ext .decimal) oc78 →
    HasTypeExtCall decl syn .lessThan [a, b] c env (.bool .anyBool)
  | lessThanOrEqual : ∀ a b c env,
    HasType decl syn a c env (.ext .decimal) oc97 → HasType decl syn b c env (.ext .decimal) oc79 →
    HasTypeExtCall decl syn .lessThanOrEqual [a, b] c env (.bool .anyBool)
  | greaterThan : ∀ a b c env,
    HasType decl syn a c env (.ext .decimal) oc98 → HasType decl syn b c env (.ext .decimal) oc80 →
    HasTypeExtCall decl syn .greaterThan [a, b] c env (.bool .anyBool)
  | greaterThanOrEqual : ∀ a b c env,
    HasType decl syn a c env (.ext .decimal) oc99 → HasType decl syn b c env (.ext .decimal) oc81 →
    HasTypeExtCall decl syn .greaterThanOrEqual [a, b] c env (.bool .anyBool)
  | isIpv4 : ∀ a c env,
    HasType decl syn a c env (.ext .ipAddr) oc82 →
    HasTypeExtCall decl syn .isIpv4 [a] c env (.bool .anyBool)
  | isIpv6 : ∀ a c env,
    HasType decl syn a c env (.ext .ipAddr) oc83 →
    HasTypeExtCall decl syn .isIpv6 [a] c env (.bool .anyBool)
  | isLoopback : ∀ a c env,
    HasType decl syn a c env (.ext .ipAddr) oc84 →
    HasTypeExtCall decl syn .isLoopback [a] c env (.bool .anyBool)
  | isMulticast : ∀ a c env,
    HasType decl syn a c env (.ext .ipAddr) oc85 →
    HasTypeExtCall decl syn .isMulticast [a] c env (.bool .anyBool)
  /- `isInRange` takes an address and one or more ranges. The range types are chosen
     first (`IpAddrTypes`) and the ranges typed against them. -/
  | isInRange : ∀ a xs c env tys,
    HasType decl syn a c env (.ext .ipAddr) oc100 → IpAddrTypes tys → HasTypeList decl syn xs c env (id tys) →
    HasTypeExtCall decl syn .isInRange (a :: xs) c env (.bool .anyBool)
  | offset : ∀ a b c env,
    HasType decl syn a c env (.ext .datetime) oc101 → HasType decl syn b c env (.ext .duration) oc87 →
    HasTypeExtCall decl syn .offset [a, b] c env (.ext .datetime)
  | durationSince : ∀ a b c env,
    HasType decl syn a c env (.ext .datetime) oc102 → HasType decl syn b c env (.ext .datetime) oc88 →
    HasTypeExtCall decl syn .durationSince [a, b] c env (.ext .duration)
  | toDate : ∀ a c env,
    HasType decl syn a c env (.ext .datetime) oc89 →
    HasTypeExtCall decl syn .toDate [a] c env (.ext .datetime)
  | toTime : ∀ a c env,
    HasType decl syn a c env (.ext .datetime) oc90 →
    HasTypeExtCall decl syn .toTime [a] c env (.ext .duration)
  | toMilliseconds : ∀ a c env,
    HasType decl syn a c env (.ext .duration) oc91 →
    HasTypeExtCall decl syn .toMilliseconds [a] c env .int
  | toSeconds : ∀ a c env,
    HasType decl syn a c env (.ext .duration) oc92 →
    HasTypeExtCall decl syn .toSeconds [a] c env .int
  | toMinutes : ∀ a c env,
    HasType decl syn a c env (.ext .duration) oc93 →
    HasTypeExtCall decl syn .toMinutes [a] c env .int
  | toHours : ∀ a c env,
    HasType decl syn a c env (.ext .duration) oc94 →
    HasTypeExtCall decl syn .toHours [a] c env .int
  | toDays : ∀ a c env,
    HasType decl syn a c env (.ext .duration) oc95 →
    HasTypeExtCall decl syn .toDays [a] c env .int

/-- `RecordTypeOf`: the record literal `axs` has type `rty`, typed in key order (`sorted`) or in
    source order (`lax`, only when `b = false`). -/
inductive RecordTypeOf (decl syn : Bool) : Bool → List (Attr × Expr) → Capabilities → TypeEnv →
    RecordType → Prop where
  | sorted :
    ∀ b axs axs' c env atyList,
    SortsTo axs axs' →
    HasTypeRecord decl syn none axs' c env atyList →
    RecordTypeOf decl syn b axs c env (.mk atyList)
  | lax :
    ∀ axs c env atys,
    HasTypeFields decl syn axs c env atys →
    RecordTypeOf decl syn false axs c env (Map.make atys)

/-- Typing the attributes of a record literal in source order, duplicate keys included, as
    `typeOf` does (`mapM₂`): each attribute `a` with type `ty` contributes `(a, .required ty)`. -/
inductive HasTypeFields (decl syn : Bool) : List (Attr × Expr) → Capabilities → TypeEnv →
    List (Attr × QualifiedType) → Prop where
  | nil :
    ∀ c env,
    HasTypeFields decl syn [] c env []
  | cons :
    ∀ a x axs c env ty atys,
    HasType decl syn x c env ty oc110 →
    HasTypeFields decl syn axs c env atys →
    HasTypeFields decl syn ((a, x) :: axs) c env ((a, .required ty) :: atys)

end

end Cedar.Validation.Relational
