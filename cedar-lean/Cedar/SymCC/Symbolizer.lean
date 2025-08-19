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

import Cedar.SymCC.Env
import Cedar.SymCC.Concretizer
import Cedar.SymCC.Decoder
import Cedar.Validation.Types

/-!
This file contains functions to encode a concrete `Env`
into a `SymEnv`, which can also be thought of as an "inverse"
of concretization.
-/

namespace Cedar.Spec

open Data Spec SymCC Validation

def Prim.symbolize : Prim → Term
  | .bool b         => .prim (.bool b)
  | .int i          => .prim (.bitvec i.toBitVec)
  | .string s       => .prim (.string s)
  | .entityUID euid => .prim (.entity euid)

/-- Encodes a `Value` as a `Term` assuming it is of a certain type -/
def Value.symbolize? (v : Value) (ty : CedarType) : Option Term :=
  match v, ty with
  | .prim p, _ => .some (Prim.symbolize p)
  | .set s, .set ty => do
    let elems := ← s.toList.mapM₁ (λ ⟨v, _⟩ => v.symbolize? ty)
    .some (.set (Set.make elems) (TermType.ofType ty))
  | .record rec, .record rty => do
    let elems := ← rty.toList.mapM (λ (a, qty) => symbolizeAttr? rec a qty)
    .some (Term.record (Map.mk elems))
  | .ext e, _ => .some ↑e
  | _, _ => .none
termination_by sizeOf v
decreasing_by
  · cases s
    rename_i h
    have h := List.sizeOf_lt_of_mem h
    simp only [Set.toList, Set.elts] at h
    simp only [set.sizeOf_spec, Set.mk.sizeOf_spec, gt_iff_lt]
    omega
  · simp only [record.sizeOf_spec, Nat.lt_add_left_iff_pos, Nat.lt_add_one]
where
  symbolizeAttr? (rec : Map Attr Value) (a : Attr) (qty : QualifiedType) : Option (Attr × Term) :=
    match _h : rec.find? a with
    | .none => .some (a, .none (TermType.ofType qty.getType))
    | .some v =>
      match qty with
      | .optional ty => do .some (a, .some (← v.symbolize? ty))
      | .required ty => do .some (a, ← v.symbolize? ty)
  termination_by sizeOf rec
  decreasing_by
    all_goals
      have := Map.find?_mem_toList _h
      have := List.sizeOf_lt_of_mem this
      cases rec
      simp [Map.toList, Map.kvs] at this ⊢
      omega

/--
The variable ids here should match the variables in `SymRequest.ofRequestType`.
-/
def Request.symbolize? (req : Request) (Γ : TypeEnv) (var : TermVar) : Option Term :=
  if var == { id := "principal", ty := TermType.ofType (.entity Γ.reqty.principal) } then
    Value.symbolize? ↑req.principal (.entity Γ.reqty.principal)
  else if var == { id := "action", ty := TermType.ofType (.entity Γ.reqty.action.ty) } then
    Value.symbolize? ↑req.action (.entity Γ.reqty.action.ty)
  else if var == { id := "resource", ty := TermType.ofType (.entity Γ.reqty.resource) } then
    Value.symbolize? ↑req.resource (.entity Γ.reqty.resource)
  else if var == { id := "context", ty := TermType.ofType (.record Γ.reqty.context) } then
    Value.symbolize? ↑req.context (.record Γ.reqty.context)
  else
    .none

def defaultEidOf (Γ : TypeEnv) (ety : EntityType) : String :=
  -- TODO: Improve performance by looking up in `Γ` directly
  Decoder.eidOfForEntities (SymEnv.ofEnv Γ).entities ety

def defaultLitWithDefaultEid (Γ : TypeEnv) (ty : TermType) : Term :=
  Decoder.defaultLit (defaultEidOf Γ) ty

/--
Generates an interpretation of the attribute map.
-/
def Entities.symbolizeAttrs?
  (entities : Entities) (Γ : TypeEnv)
  (ety : EntityType) (entry : EntitySchemaEntry)
  (uuf : UUF) : Option UDF :=
  if uuf == {
    id := UUF.attrsId ety,
    arg := TermType.ofType (.entity ety),
    out := TermType.ofType (.record entry.attrs)
  } then
    .some udf
  else
    .none
where
  udf :=
    let outTy := (.record entry.attrs)
    {
      arg := TermType.ofType (.entity ety),
      out := TermType.ofType outTy,
      -- Collect concrete attributes of every entity of type `ety`
      table := Map.make (entities.toList.filterMap λ (euid, data) => do
        if euid.ty = ety then
          .some (↑euid, ← Value.symbolize? data.attrs outTy)
        else
          .none),
      default := defaultLitWithDefaultEid Γ (TermType.ofType outTy),
    }

/--
Generates interpretations for the tag key and value maps.
-/
def Entities.symbolizeTags?
  (entities : Entities) (Γ : TypeEnv)
  (ety : EntityType) (entry : EntitySchemaEntry)
  (uuf : UUF) : Option UDF := do
  let tagTy := ← entry.tags?
  if uuf == {
    id := UUF.tagKeysId ety,
    arg := TermType.ofType (.entity ety),
    out := TermType.ofType (.set .string),
  } then
    .some keysUDF
  else if uuf == {
    id := UUF.tagValsId ety,
    arg := TermType.tagFor ety,
    out := TermType.ofType tagTy,
  } then
    .some (valsUDF tagTy)
  else
    .none
where
  keysUDF := {
    arg := TermType.ofType (.entity ety),
    out := TermType.ofType (.set .string),
    -- Collect concrete tag keys of every entity of type `ety`
    table := Map.make (entities.toList.filterMap λ (euid, data) => do
      if euid.ty = ety then
        .some (↑euid, .set (Set.make (data.tags.keys.toList.map λ k => .prim (.string k))) .string)
      else
        .none),
    default := defaultLitWithDefaultEid Γ (TermType.ofType (.set .string)),
  }
  valsUDF tagTy := {
    arg := TermType.tagFor ety,
    out := TermType.ofType tagTy,
    -- Collect concrete tag values of every entity of type `ety`
    -- i.e. a map from (entity, tag key) to tag value
    table := Map.make (entities.toList.filterMap λ (uid, data) => do
      if uid.ty = ety then
        data.tags.toList.mapM λ (tag, value) => do
          .some (
            .record (Map.mk [
              ("entity", .prim (.entity uid)),
              ("tag", .prim (.string tag)),
            ]),
            ← Value.symbolize? value tagTy,
          )
      else
        .none).flatten,
    default := defaultLitWithDefaultEid Γ (TermType.ofType tagTy),
  }

/--
Generates an interpretation for the ancestor map.
-/
def Entities.symbolizeAncs?
  (entities : Entities) (Γ : TypeEnv)
  (ety : EntityType) (entry : EntitySchemaEntry)
  (uuf : UUF) : Option UDF :=
  entry.ancestors.toList.findSome? λ ancTy =>
    if uuf == {
      id := UUF.ancsId ety ancTy,
      arg := TermType.ofType (.entity ety),
      out := TermType.ofType (.set (.entity ancTy)),
    } then
      .some (udf ancTy)
    else
      .none
where
  udf ancTy := {
    arg := TermType.ofType (.entity ety),
    out := TermType.ofType (.set (.entity ancTy)),
    table := Map.make (entities.toList.filterMap λ (uid, data) => do
    if uid.ty = ety then
      .some (↑uid,
        .set
          (Set.make (data.ancestors.toList.filterMap λ anc =>
            if anc.ty = ancTy then
              .some (.prim (.entity anc))
            else
              .none))
          (.entity ancTy))
    else
      .none),
    default := defaultLitWithDefaultEid Γ (TermType.ofType (.set (.entity ancTy))),
  }

/--
Symbolizes a concrete `Entities` into (part of) an `Interpretation` of `SymEnv.ofEnv Γ`.
The `UUF` ids here should match those in `SymEntityData.ofStandardEntityType`.
-/
def Entities.symbolize? (entities : Entities) (Γ : TypeEnv) (uuf : UUF) : Option UDF :=
  Γ.ets.toList.findSome? λ (ety, entry) =>
    entities.symbolizeAttrs? Γ ety entry uuf <|>
    entities.symbolizeTags? Γ ety entry uuf <|>
    entities.symbolizeAncs? Γ ety entry uuf

/--
Converts an `Env` (assumed to be a well-typed instance of `TypeEnv`) into
an `Interpretation` of `SymEnv.ofEnv Γ`.
-/
def Env.symbolize? (env : Env) (Γ : TypeEnv) : Interpretation :=
  {
    vars := λ var =>
      match Request.symbolize? env.request Γ var with
      | .some term => term
      | .none => defaultLitWithDefaultEid Γ var.ty,
    funs := λ uuf =>
      match Entities.symbolize? env.entities Γ uuf with
      | .some udf => udf
      | .none => Decoder.defaultUDF (defaultEidOf Γ) uuf,
    partials := λ t => defaultLitWithDefaultEid Γ t.typeOf,
  }

end Cedar.Spec
