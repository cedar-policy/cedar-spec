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

def Request.symbolize? (req : Request) (Γ : TypeEnv) : Option SymRequest := do
  .some {
    principal := ← Value.symbolize? ↑req.principal (.entity Γ.reqty.principal),
    action := ← Value.symbolize? ↑req.action (.entity Γ.reqty.action.ty),
    resource := ← Value.symbolize? ↑req.resource (.entity Γ.reqty.resource),
    context := ← Value.symbolize? ↑req.context (.record Γ.reqty.context),
  }

def Entities.symbolize? (entities : Entities) (Γ : TypeEnv) : Option SymEntities := do
  let etys := (Γ.ets.toList.map Prod.fst ++
              Γ.acts.toList.map λ entry => entry.1.ty).eraseDups
  let data := ← etys.mapM₁ λ ⟨ety, _⟩ => do .some (ety, ← symbolizeForEntityType? ety)
  .some (Map.make data)
where
  eidOf ety :=
    match Γ.ets.find? ety with
    | .some (.enum (.mk (eid :: _))) => eid
    | _ => ""
  attrRecordType ety :=
    match Γ.ets.find? ety with
    | .some data => data.attrs
    | .none => Map.empty
  members ety :=
    match Γ.ets.find? ety with
    | .some (.enum s) => .some s
    | _ => .none
  symbolizeForEntityType? ety := do
    .some {
      attrs := ← attrsUDF ety,
      ancestors := ← ancsUDF ety,
      members := members ety,
      tags := sorry,
    }
  attrsUDF ety :=
    let outTy := (.record (attrRecordType ety))
    .some (.udf {
      arg := TermType.ofType (.entity ety),
      out := TermType.ofType outTy,
      table := Map.make (entities.toList.filterMap λ (euid, data) => do
        if euid.ty = ety then
          .some (↑euid, ← Value.symbolize? data.attrs outTy)
        else
          .none),
      default := Decoder.defaultLit eidOf (TermType.ofType outTy),
    })
  ancsUDF ety := sorry

/--
Converts an `Env` (assumed to be a well-typed instance of `TypeEnv`) into a `SymEnv`.
-/
def Env.symbolize? (env : Env) (Γ : TypeEnv) : Option SymEnv := do
  .some {
    request := ← env.request.symbolize? Γ,
    entities := ← env.entities.symbolize? Γ,
  }

end Cedar.Spec
