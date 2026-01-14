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

/-!
# Concretizing symbolic environments

This file defines functions for concretizing a literal symbolic environment
(`SymEnv`) into a corresponding concrete environment (`Env`). This functionality
is needed for extracting counterexamples from models returned by the solver and
also for proving that Cedar's reduction to SMT (`Cedar.SymCC.compile`) is
complete.

See Cedar.Thm.SymbolicCompilation for a statement of the completeness theorem.
-/

namespace Cedar.Spec

open Data Spec

def Prim.entityUIDs : Prim → Set EntityUID
  | .entityUID uid => Set.singleton uid
  | _              => Set.empty

def Value.entityUIDs : Value → Set EntityUID
  | .prim p              => p.entityUIDs
  | .set (Set.mk vs)     => vs.mapUnion₁ (λ ⟨v, _⟩ => v.entityUIDs)
  | .record (Map.mk avs) => avs.mapUnion₃ (λ ⟨(_, v), _⟩ => v.entityUIDs)
  | .ext _               => Set.empty

def Value.entityUID? : Value → Option EntityUID
  | .prim (.entityUID uid) => .some uid
  | _                      => .none

def Value.record? : Value → Option (Map Attr Value)
  | .record r => .some r
  | _         => .none

def Request.entityUIDs (r : Request) : Set EntityUID :=
  (Set.singleton r.principal) ∪
  (Set.singleton r.action) ∪
  (Set.singleton r.resource) ∪
  (Value.record r.context).entityUIDs

def EntityData.entityUIDs (d : EntityData) : Set EntityUID :=
  d.ancestors ∪ (Value.record d.attrs).entityUIDs ∪ (Value.record d.tags).entityUIDs

def Entities.entityUIDs (es : Entities) : Set EntityUID :=
  es.kvs.mapUnion (λ (uid, d) => (Set.singleton uid) ∪ d.entityUIDs)

structure Env where
  request : Request
  entities : Entities
deriving Repr, DecidableEq

def Env.entityUIDs (env : Env) : Set EntityUID :=
  env.request.entityUIDs ∪ env.entities.entityUIDs

def Expr.entityUIDs : Expr → Set EntityUID
  | .lit p             => p.entityUIDs
  | .var _             => Set.empty
  | .ite x₁ x₂ x₃      => x₁.entityUIDs ∪ x₂.entityUIDs ∪ x₃.entityUIDs
  | .and x₁ x₂
  | .or x₁ x₂
  | .binaryApp _ x₁ x₂ => x₁.entityUIDs ∪ x₂.entityUIDs
  | .unaryApp _ x₁
  | .getAttr x₁ _
  | .hasAttr x₁ _      => x₁.entityUIDs
  | .set xs
  | .call _ xs         => xs.mapUnion₁ (λ ⟨x, _⟩ => x.entityUIDs)
  | .record axs        => axs.mapUnion₂ (λ ⟨(_, x), _⟩ => x.entityUIDs)

end Cedar.Spec

namespace Cedar.SymCC

open Data Factory Spec

def BitVec.int64? {n} (bv : BitVec n) : Option Int64 :=
  if n = 64
  then .some (Int64.ofInt bv.toInt)
  else .none

def TermPrim.value? : TermPrim → Option Value
  | .bool b     => .some b
  | .bitvec bv  => BitVec.int64? bv
  | .string s   => .some s
  | .entity uid => .some uid
  | .ext xv     => .some xv

def Term.value? : Term → Option Value
  | .prim p => p.value?
  | .set (.mk ts) _ => do
    let vs ← ts.mapM₁ λ ⟨tᵢ, _⟩ => tᵢ.value?
    .some (.set (Set.make vs))
  | .record (.mk ats) => do
    let avs? ← ats.mapM₂ λ ⟨(aᵢ, tᵢ), _⟩ => attrValue? aᵢ tᵢ
    let avs := avs?.filterMap λ (aᵢ, vᵢ?) => vᵢ?.map (Prod.mk aᵢ)
    .some (.record (Map.mk avs))
  | _ => .none
termination_by t => sizeOf t
decreasing_by
  all_goals {
    simp_wf
    rename_i h
    try replace h := List.sizeOf_lt_of_mem h
    simp only at h
    omega
  }
where
  attrValue? (a : Attr) : Term → Option (Attr × Option Value)
    | .some t => do .some (a, .some (← t.value?))
    | .none _ => .some (a, .none)
    | t       => do .some (a, .some (← t.value?))
  termination_by t => sizeOf t + 1
  decreasing_by
    all_goals simp_wf
    omega

def Term.recordValue? (t : Term) : Option (Map Attr Value) :=
  t.value? >>= Value.record?

def TermPrim.entityUIDs : TermPrim → Set EntityUID
  | .entity uid => Set.singleton uid
  | _           => Set.empty

def Term.entityUIDs : Term → Set EntityUID
  | .var _
  | .none _              => Set.empty
  | .prim p              => p.entityUIDs
  | .some t              => t.entityUIDs
  | .set (Set.mk ts) _   => ts.mapUnion₁ (λ ⟨t, _⟩ => t.entityUIDs)
  | .record (Map.mk ats) => ats.mapUnion₃ (λ ⟨(_, t), _⟩ => t.entityUIDs)
  | .app _ ts _          => ts.mapUnion₁ (λ ⟨t, _⟩ => t.entityUIDs)

def Term.entityUID? : Term → Option EntityUID
  | .prim (.entity uid) => .some uid
  | _                   => .none

def Term.setOfEntityUIDs? : Term → Option (Set EntityUID)
  | .set (Set.mk ts) _  => do .some (Set.make (← ts.mapM Term.entityUID?))
  | _                   => .none

def Term.tag? : Term → Option Tag
  | .prim (.string tag) => .some tag
  | _                   => .none

def Term.setOfTags? : Term → Option (Set Tag)
  | .set (Set.mk ts) _ => do .some (Set.make (← ts.mapM Term.tag?))
  | _                  => .none

def SymRequest.entityUIDs (ρ : SymRequest) : Set EntityUID :=
  ρ.principal.entityUIDs ∪
  ρ.action.entityUIDs ∪
  ρ.resource.entityUIDs ∪
  ρ.context.entityUIDs

def UDF.entityUIDs (f : UDF) : Set EntityUID :=
  f.default.entityUIDs ∪
  f.table.kvs.mapUnion (λ (tᵢ, tₒ) => tᵢ.entityUIDs ∪ tₒ.entityUIDs)

def UnaryFunction.entityUIDs : UnaryFunction → Set EntityUID
  | .uuf _ => Set.empty
  | .udf f => f.entityUIDs

def SymEntityData.entityUIDs (ety : EntityType) (δ : SymEntityData) : Set EntityUID :=
  mems ∪ attrs ∪ ancs ∪ tags
where
  mems  := match δ.members with
    | .none      => Set.empty
    | .some eids => Set.make (eids.elts.map (EntityUID.mk ety))
  attrs := δ.attrs.entityUIDs
  ancs  := δ.ancestors.kvs.mapUnion (λ (_, f) => f.entityUIDs)
  tags  := match δ.tags with
    | .none      => Set.empty
    | .some τs   => τs.vals.entityUIDs

def SymEntities.entityUIDs (εs : SymEntities) : Set EntityUID :=
  εs.kvs.mapUnion λ (ety, δ) => δ.entityUIDs ety

def SymEnv.entityUIDs (εnv : SymEnv) : Set EntityUID :=
  εnv.request.entityUIDs ∪ εnv.entities.entityUIDs

def SymRequest.concretize? (ρ : SymRequest) : Option Request := do
  .some {
    principal := ← ρ.principal.entityUID?,
    action    := ← ρ.action.entityUID?,
    resource  := ← ρ.resource.entityUID?,
    context   := ← ρ.context.recordValue?
  }

def SymEntityData.concretize? (uid : EntityUID) (δ : SymEntityData) : Option EntityData := do
  let tuid  ← if isValidEntityUID then .some (Term.entity uid) else .none
  let attrs ← (app δ.attrs tuid).recordValue?
  let ancs  ← δ.ancestors.kvs.mapM (λ (_, f) => (app f tuid).setOfEntityUIDs?)
  .some ⟨attrs, ancs.mapUnion id, ← (tags tuid)⟩
  where
    isValidEntityUID :=
      if let .some eids := δ.members
      then eids.contains uid.eid
      else true
    taggedValueFor (τs : SymTags) (tuid : Term) (tag : Tag)  :=
      do .some (tag, ← (τs.getTag! tuid (.string tag)).value?)
    tags (tuid : Term) := match δ.tags with
      | .none    => .some Map.empty
      | .some τs => do
        let keys ← (app τs.keys tuid).setOfTags?
        let vals ← keys.elts.mapM (taggedValueFor τs tuid)
        .some (Map.mk vals)

def SymEntities.concretize? (uids : Set EntityUID) (εs : SymEntities) : Option Entities := do
  let ⟨dom⟩ := uids ∪ εs.entityUIDs
  Map.make (← dom.mapM entityData?)
  where
    entityData? (uid : EntityUID) : Option (EntityUID × EntityData) := do
      .some (uid, ← (← εs.find? uid.ty).concretize? uid)

def SymEnv.concretize? (x : Expr) (εnv : SymEnv) : Option Env := do
  let ⟨ρ, εs⟩ := εnv
  .some ⟨← ρ.concretize?, ← εs.concretize? (x.entityUIDs ∪ ρ.entityUIDs)⟩

end Cedar.SymCC
