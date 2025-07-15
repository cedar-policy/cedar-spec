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

import Cedar.SymCC.Tags

/-!
This file defines the ADTs that represent the symbolic environment.
The environment consists of a symbolic request, entity store, and action store.
A symbolic environment is _literal_ when it consists of literal terms and
interpreted functions (UDFs).
-/

namespace Cedar.SymCC

open Cedar.Data Cedar.Spec Cedar.Validation Factory

-- A symbolic request is analogous to a concrete request. It binds
-- request variables to Terms.
structure SymRequest where
  principal : Term
  action : Term
  resource : Term
  context : Term

def SymRequest.isLiteral (req : SymRequest) : Bool :=
  req.principal.isLiteral &&
  req.action.isLiteral &&
  req.resource.isLiteral &&
  req.context.isLiteral

deriving instance Repr, Inhabited, DecidableEq for SymRequest

/-
A symbolic entity store is analogous to the concrete entity store. The concrete
entity store is a map from EntityUIDs to Record values. The symbolic entity
store partitions this map into multiple maps:  one for each entity type. These
maps are represented as unary functions from entities to records. The functions
can be uninterpreted or defined. The type-based partition is required for
reduction to SMT. The symbolic store also carries a representation of the
`entityIn` relation on entities. The symbolic store partitions this relation
into multiple maps, one for each pair of an entity type and its ancestor type.
-/

structure SymEntityData where
  attrs : UnaryFunction
  ancestors : Map EntityType UnaryFunction
  members : Option (Set String) -- specifies EIDs of enum members, if applicable
  tags : Option SymTags         -- specifies tags, if applicable

def SymTags.isLiteral (τs : SymTags) : Bool :=
  τs.keys.isLiteral &&
  τs.vals.isLiteral

def SymEntityData.isLiteral (δ : SymEntityData) : Bool :=
  δ.attrs.isLiteral &&
  (δ.ancestors.toList.all λ (_, f) => f.isLiteral) &&
  (δ.tags.all SymTags.isLiteral)

deriving instance Repr, Inhabited, DecidableEq for SymEntityData

abbrev SymEntities := Map EntityType SymEntityData

deriving instance Repr, Inhabited, DecidableEq for SymEntities

def SymEntities.attrs (εs : SymEntities) (ety : EntityType) : Option UnaryFunction := do
  (← εs.find? ety).attrs

def SymEntities.ancestors (εs : SymEntities) (ety : EntityType) : Option (Map EntityType UnaryFunction) := do
  (← εs.find? ety).ancestors

def SymEntities.ancestorsOfType (εs : SymEntities) (ety ancTy : EntityType) : Option UnaryFunction := do
  (← εs.ancestors ety).find? ancTy

def SymEntities.isValidEntityType (εs : SymEntities) (ety : EntityType) : Bool :=
  εs.contains ety

def SymEntities.isValidEntityUID (εs : SymEntities) (uid : EntityUID) : Bool :=
  match εs.find? uid.ty with
  | .some d => if let .some eids := d.members then eids.contains uid.eid else true
  | .none   => false

def SymEntities.tags (εs : SymEntities) (ety : EntityType) : Option (Option SymTags) := do
  (εs.find? ety).map SymEntityData.tags

def SymEntities.isLiteral (es : SymEntities) : Bool :=
  es.toList.all λ (_, d) => d.isLiteral

structure SymEnv where
  request  : SymRequest
  entities : SymEntities

def SymEnv.isLiteral (env : SymEnv) : Bool :=
  env.request.isLiteral && env.entities.isLiteral

deriving instance Repr, Inhabited, DecidableEq for SymEnv

----- Functions for constructing symbolic input from a schema -----

def UUF.attrs_id (ety : EntityType) : String :=
  s!"attrs[{toString ety}]"

def UUF.ancs_id (ety : EntityType) (ancTy : EntityType) : String :=
  s!"ancs[{toString ety}, {toString ancTy}]"

def UUF.tag_keys_id (ety : EntityType) : String :=
  s!"tagKeys[{toString ety}]"

def UUF.tag_vals_id (ety : EntityType) : String :=
  s!"tagVals[{toString ety}]"

def SymEntityData.ofStandardEntityType (ety : EntityType) (sch : StandardSchemaEntry) : SymEntityData :=
  {
    attrs := attrsUUF,
    ancestors := Map.make (sch.ancestors.toList.map λ ancTy => (ancTy, ancsUUF ancTy)),
    members := .none,
    tags := sch.tags.map symTags
  }
where
  attrsUUF : UnaryFunction :=
    .uuf {
      id  := UUF.attrs_id ety,
      arg := TermType.ofType (.entity ety),
      out := TermType.ofType (.record sch.attrs)
    }
  ancsUUF (ancTy : EntityType) : UnaryFunction :=
    .uuf {
      id  := UUF.ancs_id ety ancTy,
      arg := TermType.ofType (.entity ety),
      out := TermType.ofType (.set (.entity ancTy))
    }
  symTags (tagTy : CedarType) : SymTags :=
    {
      keys := .uuf {
        id  := UUF.tag_keys_id ety,
        arg := TermType.ofType (.entity ety),
        out := TermType.ofType (.set .string) },
      vals := .uuf {
        id  := UUF.tag_vals_id ety,
        arg := TermType.tagFor ety, -- record representing the pair type (ety, .string)
        out := TermType.ofType tagTy
      }
    }

def SymEntityData.emptyAttrs (ety : EntityType) : UnaryFunction :=
  .udf {
    arg := TermType.ofType (.entity ety),
    out := TermType.record Map.empty,
    table := Map.empty,
    default := Term.record Map.empty
  }

def SymEntityData.ofEnumEntityType (ety : EntityType) (eids : Set String) : SymEntityData :=
  {
    attrs := SymEntityData.emptyAttrs ety,
    ancestors := Map.empty,
    members := .some eids,
    tags := .none
  }

def SymEntityData.ofEntityType (ety : EntityType) : EntitySchemaEntry → SymEntityData
  | .standard sch => SymEntityData.ofStandardEntityType ety sch
  | .enum eids    => SymEntityData.ofEnumEntityType ety eids

def SymEntityData.ofActionType (actTy : EntityType) (actTys : List EntityType) (sch : ActionSchema) : SymEntityData :=
  {
    attrs := SymEntityData.emptyAttrs actTy,
    ancestors := Map.make (actTys.map λ ancTy => (ancTy, ancsUDF ancTy)),
    members := .some (Set.make acts),
    tags := .none
  }
where
  termOfType? (ety : EntityType) (uid : EntityUID) : Option Term :=
    if uid.ty = ety then .some (.prim (.entity uid)) else .none
  ancsTerm (ancTy : EntityType) (ancs : List EntityUID) : Term :=
    setOf (ancs.filterMap (termOfType? ancTy)) (TermType.ofType (.entity ancTy))
  ancsUDF (ancTy : EntityType) : UnaryFunction :=
    .udf {
      arg := TermType.ofType (.entity actTy),
      out := TermType.ofType (.set (.entity ancTy)),
      table := Map.make (sch.toList.filterMap λ (uid, entry) => do
        (← termOfType? actTy uid, ancsTerm ancTy entry.ancestors.toList)),
      default := .set .empty (TermType.ofType (.entity ancTy))
    }
  acts := sch.toList.filterMap λ (uid, _) => if uid.ty = actTy then .some uid.eid else .none

/--
Creates symbolic entities for the given schema. This function assumes that the
schemas are well-formed in the following sense:
* All entity types that appear in the attributes or ancestors fields of `ets` are
  declared either in `ets` or `acts`.
* All entity types that appear in the ancestors fields of `acts` are declared in `acts`.
An entity type is declared in `ets` if it's a key in the underlying map; it's
declared in `acts` if it's the type of a key in the underlying map. This
function also assumes `ets` and `ats` declare disjoint sets of types.
This function assumes that no entity types have tags, and that action types
have no attributes.
-/
def SymEntities.ofSchema (ets : EntitySchema) (acts : ActionSchema) : SymEntities :=
  let eData := ets.toList.map λ (ety, sch) => (ety, SymEntityData.ofEntityType ety sch)
  let actTys := (acts.toList.map λ (act, _) => act.ty).eraseDups
  let aData := actTys.map λ actTy => (actTy, SymEntityData.ofActionType actTy actTys acts)
  Map.make (eData ++ aData)

/--
Creates a symbolic request for the given request type.
-/
def SymRequest.ofRequestType (reqTy : RequestType) : SymRequest :=
  {
    principal := .var ⟨"principal", TermType.ofType (.entity reqTy.principal)⟩,
    action    := .prim (.entity reqTy.action),
    resource  := .var ⟨"resource", TermType.ofType (.entity reqTy.resource)⟩,
    context   := .var ⟨"context", TermType.ofType (.record reqTy.context)⟩
  }

/--
Returns a symbolic environment that conforms to the given
type environment.
-/
def SymEnv.ofEnv (tyEnv : TypeEnv) : SymEnv :=
  {
    request  := SymRequest.ofRequestType tyEnv.reqty,
    entities := SymEntities.ofSchema tyEnv.ets tyEnv.acts
  }

end Cedar.SymCC
