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

import Cedar.Partial.Entities
import Cedar.Partial.Expr
import Cedar.Partial.Request
import Cedar.Partial.Value
import Cedar.Spec.Evaluator
import Cedar.Spec.ExtFun
import Cedar.Spec.Value

/-! This file defines the semantics of Cedar partial evaluation. -/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Attr BinaryOp EntityUID Result UnaryOp intOrErr)
open Cedar.Spec.Error

/-- Analogous to Spec.inₑ but for partial entities -/
def inₑ (uid₁ uid₂ : EntityUID) (es : Partial.Entities) : Bool :=
  uid₁ == uid₂ || (es.ancestorsOrEmpty uid₁).contains uid₂

/-- Analogous to Spec.inₛ but for partial entities -/
def inₛ (uid : EntityUID) (vs : Set Spec.Value) (es : Partial.Entities) : Result Spec.Value := do
  let uids ← vs.mapOrErr Spec.Value.asEntityUID .typeError
  .ok (uids.any (Partial.inₑ uid · es))

/-- Analogous to Spec.apply₂ but for partial entities -/
def apply₂ (op₂ : BinaryOp) (v₁ v₂ : Spec.Value) (es : Partial.Entities) : Result Partial.Value :=
  match op₂, v₁, v₂ with
  | .eq, _, _                                              => .ok (.value (v₁ == v₂))
  | .less,   .prim (.int i), .prim (.int j)                => .ok (.value ((i < j): Bool))
  | .lessEq, .prim (.int i), .prim (.int j)                => .ok (.value ((i ≤ j): Bool))
  | .add,    .prim (.int i), .prim (.int j)                => intOrErr (i.add? j) >>= λ x => .ok (.value x)
  | .sub,    .prim (.int i), .prim (.int j)                => intOrErr (i.sub? j) >>= λ x => .ok (.value x)
  | .mul,    .prim (.int i), .prim (.int j)                => intOrErr (i.mul? j) >>= λ x => .ok (.value x)
  | .contains,    .set vs₁, _                              => .ok (.value (vs₁.contains v₂))
  | .containsAll, .set vs₁, .set vs₂                       => .ok (.value (vs₂.subset vs₁))
  | .containsAny, .set vs₁, .set vs₂                       => .ok (.value (vs₁.intersects vs₂))
  | .mem, .prim (.entityUID uid₁), .prim (.entityUID uid₂) => .ok (.value (Partial.inₑ uid₁ uid₂ es))
  | .mem, .prim (.entityUID uid₁), .set (vs)               => Partial.inₛ uid₁ vs es >>= λ x => .ok (.value x)
  | _, _, _                                                => .error .typeError

/-- Analogous to Spec.attrsOf but for lookup functions that return partial values -/
def attrsOf (v : Spec.Value) (lookup : EntityUID → Result (Map Attr Partial.Value)) : Result (Map Attr Partial.Value) :=
  match v with
  | .record r              => .ok (r.mapOnValues Partial.Value.value)
  | .prim (.entityUID uid) => lookup uid
  | _                      => .error typeError

/-- Analogous to Spec.hasAttr but for partial entities -/
def hasAttr (v : Spec.Value) (a : Attr) (es : Partial.Entities) : Result Spec.Value := do
  let r ← Partial.attrsOf v (fun uid => .ok (es.attrsOrEmpty uid))
  .ok (r.contains a)

/-- Analogous to Spec.getAttr but for partial entities -/
def getAttr (v : Spec.Value) (a : Attr) (es : Partial.Entities) : Result Partial.Value := do
  let r ← Partial.attrsOf v es.attrs
  r.findOrErr a attrDoesNotExist

/-- Analogous to Spec.bindAttr but for partial values -/
def bindAttr (a : Attr) (res : Result Partial.Value) : Result (Attr × Partial.Value) := do
  let v ← res
  .ok (a, v)

/-- Analogous to Spec.evaluate but performs partial evaluation on partial expr/request/entities -/
def evaluate (x : Partial.Expr) (req : Partial.Request) (es : Partial.Entities) : Result Partial.Value :=
  match x with
  | .lit l          => .ok (.value l)
  | .var .principal => .ok req.principal
  | .var .action    => .ok req.action
  | .var .resource  => .ok req.resource
  | .var .context   => match req.context.kvs.mapM fun (k, v) => match v with | .value v => some (k, v) | .residual _ => none with
    | some kvs      => .ok (.value (Map.make kvs))
    | none          => .ok (.residual (Partial.Expr.record (req.context.kvs.map fun (k, v) => (k, v.asPartialExpr))))
  | .ite x₁ x₂ x₃   => do
    let pval ← Partial.evaluate x₁ req es
    match pval with
    | .value v => do
      let b ← v.asBool
      if b then Partial.evaluate x₂ req es else Partial.evaluate x₃ req es
    | .residual r => .ok (.residual (Partial.Expr.ite r x₂ x₃))
  | .and x₁ x₂      => do
    let pval ← Partial.evaluate x₁ req es
    match pval with
    | .value v => do
      let b ← v.asBool
      if !b then .ok (.value b) else do
        let pval ← Partial.evaluate x₂ req es
        match pval with
        | .value v => do
          let b ← v.asBool
          .ok (.value b)
        | .residual r => .ok (.residual r)
    | .residual r => .ok (.residual (Partial.Expr.and r x₂))
  | .or x₁ x₂       => do
    let pval ← Partial.evaluate x₁ req es
    match pval with
    | .value v => do
      let b ← v.asBool
      if b then .ok (.value b) else do
        let pval ← Partial.evaluate x₂ req es
        match pval with
        | .value v => do
          let b ← v.asBool
          .ok (.value b)
        | .residual r => .ok (.residual r)
    | .residual r => .ok (.residual (Partial.Expr.or r x₂))
  | .unaryApp op₁ x₁ => do
    let pval ← Partial.evaluate x₁ req es
    match pval with
    | .value v₁ => do
      let val ← Spec.apply₁ op₁ v₁
      .ok (.value val)
    | .residual r => .ok (.residual (Partial.Expr.unaryApp op₁ r))
  | .binaryApp op₂ x₁ x₂ => do
    let pval₁ ← Partial.evaluate x₁ req es
    let pval₂ ← Partial.evaluate x₂ req es
    match (pval₁, pval₂) with
    | (.value v₁, .value v₂) => Partial.apply₂ op₂ v₁ v₂ es
    | (.value v₁, .residual r₂) => .ok (.residual (Partial.Expr.binaryApp op₂ v₁.asPartialExpr r₂))
    | (.residual r₁, .value v₂) => .ok (.residual (Partial.Expr.binaryApp op₂ r₁ v₂.asPartialExpr))
    | (.residual r₁, .residual r₂) => .ok (.residual (Partial.Expr.binaryApp op₂ r₁ r₂))
  | .hasAttr x₁ a   => do
    let pval₁ ← Partial.evaluate x₁ req es
    match pval₁ with
    | .value v₁ => do
      let val ← Partial.hasAttr v₁ a es
      .ok (.value val)
    | .residual r => .ok (.residual (Partial.Expr.hasAttr r a)) -- TODO more precise: even though pval₁ is a residual we may know concretely whether it contains the particular attr we care about
  | .getAttr x₁ a   => do
    let pval₁ ← Partial.evaluate x₁ req es
    match pval₁ with
    | .value v₁ => Partial.getAttr v₁ a es
    | .residual r => .ok (.residual (Partial.Expr.getAttr r a)) -- TODO more precise: pval₁ will be a .residual if it contains any unknowns, but we might have a concrete value for the particular attr we care about
  | .set xs         => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => Partial.evaluate x₁ req es)
    match vs.mapM (fun pval => match pval with | .value v => some v | .residual _ => none) with
    | some vs => .ok (.value (Set.make vs))
    | none    => .ok (.residual (Partial.Expr.set (vs.map Partial.Value.asPartialExpr)))
  | .record axs     => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => Partial.bindAttr a₁ (Partial.evaluate x₁ req es))
    match avs.mapM (fun (a, pval) => match pval with | .value v => some (a, v) | .residual _ => none) with
    | some avs => .ok (.value (Map.make avs))
    | none     => .ok (.residual (Partial.Expr.record (avs.map fun (a, v) => (a, v.asPartialExpr))))
  | .call xfn xs    => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => Partial.evaluate x₁ req es)
    match vs.mapM (fun pval => match pval with | .value v => some v | .residual _ => none) with
    | some vs => do
      let val ← Spec.call xfn vs
      .ok (.value val)
    | none    => .ok (.residual (Partial.Expr.call xfn (vs.map Partial.Value.asPartialExpr)))
  | .unknown u      => .ok (.residual (Partial.Expr.unknown u))
