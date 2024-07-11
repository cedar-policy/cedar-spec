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
import Cedar.Partial.Request
import Cedar.Partial.Value
import Cedar.Spec.Evaluator
import Cedar.Spec.ExtFun
import Cedar.Spec.Value

/-! This file defines the semantics of Cedar partial evaluation. -/

namespace Cedar.Partial

open Cedar.Data
open Cedar.Spec (Attr BinaryOp EntityUID Expr ExtFun Result UnaryOp Var intOrErr)
open Cedar.Spec.Error

/--
  Partial-evaluate `op₁ pv₁`. No analogue in Spec.Evaluator; this logic (that
  sits between `Partial.evaluate` and `Spec.apply₁`) is not needed in the
  equivalent Spec.Evaluator position
-/
def evaluateUnaryApp (op₁ : UnaryOp) : Partial.Value → Result Partial.Value
  | .value v₁ => do
    let val ← Spec.apply₁ op₁ v₁
    .ok (.value val)
  | pv => .ok (.residual (.unaryApp op₁ pv))

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
  | .add,    .prim (.int i), .prim (.int j)                => do .ok (.value (← intOrErr (i.add? j)))
  | .sub,    .prim (.int i), .prim (.int j)                => do .ok (.value (← intOrErr (i.sub? j)))
  | .mul,    .prim (.int i), .prim (.int j)                => do .ok (.value (← intOrErr (i.mul? j)))
  | .contains,    .set vs₁, _                              => .ok (.value (vs₁.contains v₂))
  | .containsAll, .set vs₁, .set vs₂                       => .ok (.value (vs₂.subset vs₁))
  | .containsAny, .set vs₁, .set vs₂                       => .ok (.value (vs₁.intersects vs₂))
  | .mem, .prim (.entityUID uid₁), .prim (.entityUID uid₂) => .ok (.value (Partial.inₑ uid₁ uid₂ es))
  | .mem, .prim (.entityUID uid₁), .set (vs)               => do .ok (.value (← Partial.inₛ uid₁ vs es))
  | _, _, _                                                => .error .typeError

/--
  Partial-evaluate `op₂ pv₁ pv₂`. No analogue in Spec.Evaluator; this logic
  (that sits between `Partial.evaluate` and `Partial.apply₂`) is not needed in
  the equivalent Spec.Evaluator position
-/
def evaluateBinaryApp (op₂ : BinaryOp) (pv₁ pv₂ : Partial.Value) (es : Partial.Entities) : Result Partial.Value :=
  match (pv₁, pv₂) with
  | (.value v₁, .value v₂) => Partial.apply₂ op₂ v₁ v₂ es
  | (pv₁, pv₂) => .ok (.residual (.binaryApp op₂ pv₁ pv₂))

/-- Analogous to Spec.attrsOf but for lookup functions that return partial values -/
def attrsOf (v : Spec.Value) (lookup : EntityUID → Result (Map Attr Partial.Value)) : Result (Map Attr Partial.Value) :=
  match v with
  | .record r              => .ok (r.mapOnValues Partial.Value.value)
  | .prim (.entityUID uid) => lookup uid
  | _                      => .error typeError

/-- Analogous to Spec.hasAttr but for partial entities -/
def hasAttr (v : Spec.Value) (a : Attr) (es : Partial.Entities) : Result Spec.Value := do
  let r ← Partial.attrsOf v (λ uid => .ok (es.attrsOrEmpty uid))
  .ok (r.contains a)

/--
  Partial-evaluate `pv has a`. No analogue in Spec.Evaluator; this logic (that
  sits between `Partial.evaluate` and `Partial.hasAttr`) is not needed in the
  equivalent Spec.Evaluator position
-/
def evaluateHasAttr (pv : Partial.Value) (a : Attr) (es : Partial.Entities) : Result Partial.Value := do
  match pv with
  | .value v₁ => do
    let val ← Partial.hasAttr v₁ a es
    .ok (.value val)
  | .residual r => .ok (.residual (.hasAttr (.residual r) a)) -- TODO more precise: even though pv is a residual we may know concretely whether it contains the particular attr we care about

/-- Analogous to Spec.getAttr but for partial entities -/
def getAttr (v : Spec.Value) (a : Attr) (es : Partial.Entities) : Result Partial.Value := do
  let r ← Partial.attrsOf v es.attrs
  r.findOrErr a attrDoesNotExist

/--
  Partial-evaluate `pv[a]`. No analogue in Spec.Evaluator; this logic (that sits
  between `Partial.evaluate` and `Partial.getAttr`) is not needed in the equivalent
  Spec.Evaluator position
-/
def evaluateGetAttr (pv : Partial.Value) (a : Attr) (es : Partial.Entities) : Result Partial.Value := do
  match pv with
  | .value v₁ => Partial.getAttr v₁ a es
  | .residual r => .ok (.residual (.getAttr (.residual r) a)) -- TODO more precise: pv will be a .residual if it contains any unknowns, but we might have a concrete value for the particular attr we care about

/-- Analogous to Spec.bindAttr but for partial values -/
def bindAttr (a : Attr) (res : Result Partial.Value) : Result (Attr × Partial.Value) := do
  let v ← res
  .ok (a, v)

/-- Partial-evaluate a Var. No analogue in Spec.Evaluator; Spec.evaluate handles the `.var` case inline -/
def evaluateVar (v : Var) (req : Partial.Request) : Result Partial.Value :=
  match v with
  | .principal => .ok req.principal
  | .action    => .ok req.action
  | .resource  => .ok req.resource
  | .context   => match req.context.mapMOnValues λ v => match v with | .value v => some v | .residual _ => none with
    | some m   => .ok (.value m)
    | none     => .ok (.residual (.record req.context.kvs))

/-- Call an extension function with partial values as arguments -/
def evaluateCall (xfn : ExtFun) (args : List Partial.Value) : Result Partial.Value :=
  match args.mapM (λ pval => match pval with | .value v => some v | .residual _ => none) with
  | some vs => do
    let val ← Spec.call xfn vs
    .ok (.value val)
  | none    => .ok (.residual (.call xfn args))

/-- Analogous to Spec.evaluate but performs partial evaluation given partial request/entities -/
def evaluate (x : Expr) (req : Partial.Request) (es : Partial.Entities) : Result Partial.Value :=
  match x with
  | .lit l           => .ok (.value l)
  | .var v           => evaluateVar v req
  | .ite x₁ x₂ x₃    => do
    let pval ← Partial.evaluate x₁ req es
    match pval with
    | .value v => do
      let b ← v.asBool
      if b then Partial.evaluate x₂ req es else Partial.evaluate x₃ req es
    | .residual r => .ok (.residual (.ite (.residual r) (x₂.substToPartialValue req) (x₃.substToPartialValue req)))
  | .and x₁ x₂       => do
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
    | .residual r => .ok (.residual (.and (.residual r) (x₂.substToPartialValue req)))
  | .or x₁ x₂        => do
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
    | .residual r => .ok (.residual (.or (.residual r) (x₂.substToPartialValue req)))
  | .unaryApp op₁ x₁  => do
    let pval ← Partial.evaluate x₁ req es
    evaluateUnaryApp op₁ pval
  | .binaryApp op₂ x₁ x₂ => do
    let pval₁ ← Partial.evaluate x₁ req es
    let pval₂ ← Partial.evaluate x₂ req es
    evaluateBinaryApp op₂ pval₁ pval₂ es
  | .hasAttr x₁ a    => do
    let pval₁ ← Partial.evaluate x₁ req es
    evaluateHasAttr pval₁ a es
  | .getAttr x₁ a    => do
    let pval₁ ← Partial.evaluate x₁ req es
    evaluateGetAttr pval₁ a es
  | .set xs          => do
    let pvs ← xs.mapM₁ (λ ⟨x₁, _⟩ => Partial.evaluate x₁ req es)
    match pvs.mapM (λ pval => match pval with | .value v => some v | .residual _ => none) with
    | some vs => .ok (.value (Set.make vs))
    | none    => .ok (.residual (.set pvs))
  | .record axs      => do
    let apvs ← axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => Partial.bindAttr a₁ (Partial.evaluate x₁ req es))
    match apvs.mapM (λ (a, pval) => match pval with | .value v => some (a, v) | .residual _ => none) with
    | some avs => .ok (.value (Map.make avs))
    | none     => .ok (.residual (.record apvs))
  | .call xfn xs     => do
    let pvs ← xs.mapM₁ (λ ⟨x₁, _⟩ => Partial.evaluate x₁ req es)
    evaluateCall xfn pvs

mutual

/--
  Evaluate a `Partial.Value`, possibly reducing it. For instance, `3 + 5` will
  evaluate to `8`. This can be relevant if a substitution was recently made on
  the `Partial.Value`.
-/
def evaluateValue (pv : Partial.Value) (es : Partial.Entities) : Result Partial.Value :=
  match pv with
  | .value v => .ok (.value v)
  | .residual r => evaluateResidual r es

/--
  Evaluate a `ResidualExpr`, possibly reducing it. For instance, `3 + 5` will
  evaluate to `8`. This can be relevant if a substitution was recently made on
  the `ResidualExpr`.
-/
def evaluateResidual (x : Partial.ResidualExpr) (es : Partial.Entities) : Result Partial.Value :=
  match x with
  | .unknown u => .ok u
  | .ite pv₁ pv₂ pv₃ => do
    let pv₁' ← Partial.evaluateValue pv₁ es
    match pv₁' with
    | .value v₁' => do
      let b ← v₁'.asBool
      if b then Partial.evaluateValue pv₂ es else Partial.evaluateValue pv₃ es
    | .residual r₁' => .ok (.residual (.ite (.residual r₁') pv₂ pv₃))
  | .and pv₁ pv₂ => do
    let pv₁' ← Partial.evaluateValue pv₁ es
    match pv₁' with
    | .value v₁' => do
      let b ← v₁'.asBool
      if !b then .ok (.value b) else do
        let pv₂' ← Partial.evaluateValue pv₂ es
        match pv₂' with
        | .value v₂' => do
          let b ← v₂'.asBool
          .ok (.value b)
        | .residual r₂' => .ok (.residual r₂')
    | .residual r₁' => .ok (.residual (.and (.residual r₁') pv₂))
  | .or pv₁ pv₂ => do
    let pv₁' ← Partial.evaluateValue pv₁ es
    match pv₁' with
    | .value v₁' => do
      let b ← v₁'.asBool
      if b then .ok (.value b) else do
        let pv₂' ← Partial.evaluateValue pv₂ es
        match pv₂' with
        | .value v₂' => do
          let b ← v₂'.asBool
          .ok (.value b)
        | .residual r₂' => .ok (.residual r₂')
    | .residual r₁' => .ok (.residual (.or (.residual r₁') pv₂))
  | .unaryApp op₁ pv₁ => do
    let pv₁' ← Partial.evaluateValue pv₁ es
    evaluateUnaryApp op₁ pv₁'
  | .binaryApp op₂ pv₁ pv₂ => do
    let pv₁' ← Partial.evaluateValue pv₁ es
    let pv₂' ← Partial.evaluateValue pv₂ es
    evaluateBinaryApp op₂ pv₁' pv₂' es
  | .hasAttr pv₁ a => do
    let pv₁' ← Partial.evaluateValue pv₁ es
    evaluateHasAttr pv₁' a es
  | .getAttr pv₁ a => do
    let pv₁' ← Partial.evaluateValue pv₁ es
    evaluateGetAttr pv₁' a es
  | .set pvs => do
    let pvs' ← pvs.mapM₁ (λ ⟨pv, _⟩ => Partial.evaluateValue pv es)
    match pvs'.mapM (λ pv => match pv with | .value v => some v | .residual _ => none) with
    | some vs => .ok (.value (Set.make vs))
    | none    => .ok (.residual (.set pvs'))
  | .record apvs => do
    let apvs' ← apvs.mapM₂ (λ ⟨(a, pv), _⟩ => Partial.bindAttr a (Partial.evaluateValue pv es))
    match apvs'.mapM (λ (a, pv) => match pv with | .value v => some (a, v) | .residual _ => none) with
    | some avs => .ok (.value (Map.make avs))
    | none     => .ok (.residual (.record apvs'))
  | .call xfn pvs => do
    let pvs' ← pvs.mapM₁ (λ ⟨pv, _⟩ => Partial.evaluateValue pv es)
    evaluateCall xfn pvs'

end

end Cedar.Partial
