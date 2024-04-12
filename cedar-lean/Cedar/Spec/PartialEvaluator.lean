/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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

import Cedar.Spec.Evaluator
import Cedar.Spec.PartialEntities
import Cedar.Spec.PartialExpr
import Cedar.Spec.PartialRequest
import Cedar.Spec.PartialValue
import Cedar.Spec.Value

/-! This file defines the semantics of Cedar partial evaluation. -/

namespace Cedar.Spec

open Cedar.Data
open Error

def partialInₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) : Bool :=
  uid₁ == uid₂ || (es.ancestorsOrEmpty uid₁).contains uid₂

def partialInₛ (uid : EntityUID) (vs : Set Value) (es : PartialEntities) : Result Value := do
  let uids ← vs.mapOrErr Value.asEntityUID .typeError
  .ok (uids.any (partialInₑ uid · es))

def partialApply₂ (op₂ : BinaryOp) (v₁ v₂ : Value) (es : PartialEntities) : Result PartialValue :=
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
  | .mem, .prim (.entityUID uid₁), .prim (.entityUID uid₂) => .ok (.value (partialInₑ uid₁ uid₂ es))
  | .mem, .prim (.entityUID uid₁), .set (vs)               => partialInₛ uid₁ vs es >>= λ x => .ok (.value x)
  | _, _, _                                                => .error .typeError

def partialAttrsOf (v : Value) (lookup : EntityUID → Result (Map Attr RestrictedPartialValue)) : Result (Map Attr RestrictedPartialValue) :=
  match v with
  | .record r              => .ok (r.mapOnValues RestrictedPartialValue.value)
  | .prim (.entityUID uid) => lookup uid
  | _                      => .error typeError

def partialHasAttr (v : Value) (a : Attr) (es : PartialEntities) : Result Value := do
  let r ← partialAttrsOf v (fun uid => .ok (es.attrsOrEmpty uid))
  .ok (r.contains a)

def partialGetAttr (v : Value) (a : Attr) (es : PartialEntities) : Result RestrictedPartialValue := do
  let r ← partialAttrsOf v es.attrs
  r.findOrErr a attrDoesNotExist

def partialBindAttr (a : Attr) (res : Result PartialValue) : Result (Attr × PartialValue) := do
  let v ← res
  .ok (a, v)

def partialEvaluate (x : PartialExpr) (req : PartialRequest) (es : PartialEntities) : Result PartialValue :=
  match x with
  | .lit l          => .ok (.value l)
  | .var .principal => .ok req.principal
  | .var .action    => .ok req.action
  | .var .resource  => .ok req.resource
  | .var .context   => match req.context.kvs.mapM fun (k, v) => match v with | .value v => some (k, v) | .residual _ => none with
    | some kvs      => .ok (.value (Map.make kvs))
    | none          => .ok (.residual (PartialExpr.record (req.context.kvs.map fun (k, v) => (k, v.asPartialExpr))))
  | .ite x₁ x₂ x₃   => do
    let pval ← partialEvaluate x₁ req es
    match pval with
    | .value v => do
      let b ← v.asBool
      if b then partialEvaluate x₂ req es else partialEvaluate x₃ req es
    | .residual r => .ok (.residual (PartialExpr.ite r x₂ x₃))
  | .and x₁ x₂      => do
    let pval ← partialEvaluate x₁ req es
    match pval with
    | .value v => do
      let b ← v.asBool
      if !b then .ok (.value b) else do
        let pval ← partialEvaluate x₂ req es
        match pval with
        | .value v => do
          let b ← v.asBool
          .ok (.value b)
        | .residual r => .ok (.residual r)
    | .residual r => .ok (.residual (PartialExpr.and r x₂))
  | .or x₁ x₂       => do
    let pval ← partialEvaluate x₁ req es
    match pval with
    | .value v => do
      let b ← v.asBool
      if b then .ok (.value b) else do
        let pval ← partialEvaluate x₂ req es
        match pval with
        | .value v => do
          let b ← v.asBool
          .ok (.value b)
        | .residual r => .ok (.residual r)
    | .residual r => .ok (.residual (PartialExpr.or r x₂))
  | .unaryApp op₁ x₁ => do
    let pval ← partialEvaluate x₁ req es
    match pval with
    | .value v₁ => do
      let val ← apply₁ op₁ v₁
      .ok (.value val)
    | .residual r => .ok (.residual (PartialExpr.unaryApp op₁ r))
  | .binaryApp op₂ x₁ x₂ => do
    let pval₁ ← partialEvaluate x₁ req es
    let pval₂ ← partialEvaluate x₂ req es
    match (pval₁, pval₂) with
    | (.value v₁, .value v₂) => partialApply₂ op₂ v₁ v₂ es
    | (.value v₁, .residual r₂) => .ok (.residual (PartialExpr.binaryApp op₂ v₁.asPartialExpr r₂))
    | (.residual r₁, .value v₂) => .ok (.residual (PartialExpr.binaryApp op₂ r₁ v₂.asPartialExpr))
    | (.residual r₁, .residual r₂) => .ok (.residual (PartialExpr.binaryApp op₂ r₁ r₂))
  | .hasAttr x₁ a   => do
    let pval₁ ← partialEvaluate x₁ req es
    match pval₁ with
    | .value v₁ => do
      let val ← partialHasAttr v₁ a es
      .ok (.value val)
    | .residual r => .ok (.residual (PartialExpr.hasAttr r a)) -- TODO more precise: even though pval₁ is a residual we may know concretely whether it contains the particular attr we care about
  | .getAttr x₁ a   => do
    let pval₁ ← partialEvaluate x₁ req es
    match pval₁ with
    | .value v₁ => (partialGetAttr v₁ a es).map RestrictedPartialValue.asPartialValue
    | .residual r => .ok (.residual (PartialExpr.getAttr r a)) -- TODO more precise: pval₁ will be a .residual if it contains any unknowns, but we might have a concrete value for the particular attr we care about
  | .set xs         => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => partialEvaluate x₁ req es)
    match vs.mapM (fun pval => match pval with | .value v => some v | .residual _ => none) with
    | some vs => .ok (.value (Set.make vs))
    | none    => .ok (.residual (PartialExpr.set (vs.map PartialValue.asPartialExpr)))
  | .record axs     => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => partialBindAttr a₁ (partialEvaluate x₁ req es))
    match avs.mapM (fun (a, pval) => match pval with | .value v => some (a, v) | .residual _ => none) with
    | some avs => .ok (.value (Map.make avs))
    | none     => .ok (.residual (PartialExpr.record (avs.map fun (a, v) => (a, v.asPartialExpr))))
  | .call xfn xs    => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => partialEvaluate x₁ req es)
    match vs.mapM (fun pval => match pval with | .value v => some v | .residual _ => none) with
    | some vs => do
      let val ← ExtFun.call xfn vs
      .ok (.value val)
    | none    => .ok (.residual (PartialExpr.call xfn (vs.map PartialValue.asPartialExpr)))
  | .unknown name   => .ok (.residual (PartialExpr.unknown name))