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

def Prim.symbolize (p : Prim) : Term :=
  match p with
  | .bool b => .prim (.bool b)
  | .int i => .prim (.bitvec i.toBitVec)
  | .string s => .prim (.string s)
  | .entityUID euid => .prim (.entity euid)

/-- Encodes a `Value` as a `Term` assuming it is of a certain type -/
def Value.symbolize? (v : Value) (ty : CedarType) : Option Term :=
  match v, ty with
  | .prim p, _ => .some (Prim.symbolize p)
  | .set s, .set ty => do
    let elems := ← s.toList.mapM₁ (λ ⟨v, _⟩ => v.symbolize? ty)
    .some (.set (Set.make elems) (TermType.ofType ty))
  | .record rec, .record rty => do
    let elems := ← rec.toList.mapM₂ λ ⟨⟨a, v⟩, _⟩ => do
      match ← rty.find? a with
      | .optional ty => .some (a, .some (← v.symbolize? ty))
      | .required ty => .some (a, ← v.symbolize? ty)
    .some (Term.record (Map.make elems))
  | .ext e, _ => .some ↑e
  | _, _ => .none
termination_by sizeOf v
decreasing_by
  all_goals {
    simp_wf
    rename_i h
    try cases rec
    try cases s
    try replace h := List.sizeOf_lt_of_mem h
    simp [Set.toList, Set.elts, Map.toList, Map.kvs] at h
    simp [h]
    omega
  }

/--
The variable ids here should match the variables in `SymRequest.ofRequestType`.
-/
def Request.symbolize? (req : Request) (Γ : TypeEnv) (var : TermVar) : Option Term :=
  match var.id with
  | "principal" => Value.symbolize? ↑req.principal (.entity Γ.reqty.principal)
  | "action" => Value.symbolize? ↑req.action (.entity Γ.reqty.action.ty)
  | "resource" => Value.symbolize? ↑req.resource (.entity Γ.reqty.resource)
  | "context" => Value.symbolize? ↑req.context (.record Γ.reqty.context)
  | _ => .none

def defaultEidOf (Γ : TypeEnv) (ety : EntityType) : String :=
  match Γ.ets.find? ety with
  | .some (.enum (.mk (eid :: _))) => eid
  | _ => ""

def defaultLit' (Γ : TypeEnv) (ty : TermType) : Term :=
  Decoder.defaultLit (defaultEidOf Γ) ty

/--
Generates an interpretation of the attribute map.
-/
def Entities.symbolizeAttrs?
  (entities : Entities) (Γ : TypeEnv)
  (ety : EntityType) (entry : EntitySchemaEntry)
  (uuf : UUF) : Option UDF :=
  if uuf.id == s!"attrs[{toString ety}]" then
    let outTy := (.record entry.attrs)
    .some {
      arg := TermType.ofType (.entity ety),
      out := TermType.ofType outTy,
      -- Collect concrete attributes of every entity of type `ety`
      table := Map.make (entities.toList.filterMap λ (euid, data) => do
        if euid.ty = ety then
          .some (↑euid, ← Value.symbolize? data.attrs outTy)
        else
          .none),
      default := defaultLit' Γ (TermType.ofType outTy),
    }
  else
    .none

/--
Generates interpretations for the tag key and value maps.
-/
def Entities.symbolizeTags?
  (entities : Entities) (Γ : TypeEnv)
  (ety : EntityType) (entry : EntitySchemaEntry)
  (uuf : UUF) : Option UDF := do
  let tagTy := ← entry.tags?
  if uuf.id == s!"tagKeys[{toString ety}]" then
    .some {
      arg := TermType.ofType (.entity ety),
      out := TermType.ofType (.set .string),
      -- Collect concrete tag keys of every entity of type `ety`
      table := Map.make (entities.toList.filterMap λ (euid, data) => do
        if euid.ty = ety then
          .some (↑euid, ← Value.symbolize?
            (.set (Set.make (data.tags.keys.toList.map λ k => .prim (.string k))))
            (.set .string))
        else
          .none),
      default := defaultLit' Γ (TermType.ofType (.set .string)),
    }
  else if uuf.id == s!"tagVals[{toString ety}]" then
    .some {
      arg := TermType.tagFor ety,
      out := TermType.ofType tagTy,
      -- Collect concrete tag values of every entity of type `ety`
      -- i.e. a map from (entity, tag key) to tag value
      table := Map.make (entities.toList.filterMap λ (euid, data) => do
        if euid.ty = ety then
          data.tags.toList.mapM λ (tag, value) => do
            .some (
              .record (Map.mk [
                ("entity", .prim (.entity euid)),
                ("tag", .prim (.string tag)),
              ]),
              ← Value.symbolize? value tagTy,
            )
        else
          .none).flatten,
      default := defaultLit' Γ (TermType.ofType (.set .string)),
    }
  else
    .none

/--
Generates an interpretation for the ancestor map.
-/
def Entities.symbolizeAncs?
  (entities : Entities) (Γ : TypeEnv)
  (ety : EntityType) (entry : EntitySchemaEntry)
  (uuf : UUF) : Option UDF :=
  entry.ancestors.toList.findSome? λ ancTy =>
    if uuf.id == s!"ancs[{toString ety}, {toString ancTy}]" then
      .some {
        arg := TermType.ofType (.entity ety),
        out := TermType.ofType (.set (.entity ancTy)),
        table := Map.make (entities.toList.filterMap λ (euid, data) => do
        if euid.ty = ety then
          .some (↑euid, ← Value.symbolize?
            (.set (Set.make (data.ancestors.toList.map λ anc => .prim (.entityUID anc))))
            (.set (.entity ancTy)))
        else
          .none),
        default := defaultLit' Γ (.set (.entity ancTy)),
      }
    else
      .none

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
      | .none => defaultLit' Γ var.ty,
    funs := λ uuf =>
      match Entities.symbolize? env.entities Γ uuf with
      | .some udf => udf
      | .none => Decoder.defaultUDF (defaultEidOf Γ) uuf,
    partials := λ t => defaultLit' Γ t.typeOf,
  }

end Cedar.Spec
