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

import Cedar.TPE.Input

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

inductive Error where
  | evaluation (err : Spec.Error)
  | invalidPolicy (err : TypeError)
  | noValidEnvironment

instance : Coe Spec.Error Error where
  coe := Error.evaluation

partial def tpeExpr (x : Residual)
    (req : PartialRequest)
    (es : PartialEntities)
    : Except Spec.Error Residual :=
  match x with
  | .prim _ _ | .val _ _ => .ok x
  | .var .principal ty =>
    match req.principal.asEntityUID with
    | .some uid => .ok $ .prim (.entityUID uid) ty
    | .none => .ok $ .var .principal ty
  | .var .resource ty =>
    match req.resource.asEntityUID with
    | .some uid => .ok $ .prim (.entityUID uid) ty
    | .none => .ok $ .var .resource ty
  | .var .action ty => .ok $ .prim (.entityUID req.action) ty
  | .var .context ty => sorry
  | .ite c t e ty => do
    let c ← tpeExpr c req es
    match c with
    | .prim (.bool b) ty₁ =>
      if b then tpeExpr t req es else tpeExpr e req es
    | _ =>
      let t ← tpeExpr t req es
      let e ← tpeExpr e req es
      .ok $ .ite c t e ty
  | .and l r ty => do
    let l ← tpeExpr l req es
    match l with
    | .prim (.bool b) ty₁ =>
      if b then tpeExpr r req es else .ok $ .prim (.bool b) (.bool .ff)
    | _ =>
      let r ← tpeExpr r req es
      .ok $ .and l r ty
  | .or l r ty => do
    let l ← tpeExpr l req es
    match l with
    | .prim (.bool b) ty₁ =>
      if !b then tpeExpr r req es else .ok $ .prim (.bool b) (.bool .tt)
    | _ =>
      let r ← tpeExpr r req es
      .ok $ .or l r ty
  | .call f args ty => do
    let rs ← args.mapM₁ (fun ⟨x₁, _⟩ => tpeExpr x₁ req es)
    match rs.mapM Residual.asValue with
    | .some vs => (Spec.call f vs).map λ v ↦ .val v ty
    | .none => .ok $ .call f rs ty
  | .unaryApp op e ty => do
    let r ← tpeExpr e req es
    match r.asValue with
    | .some v => (apply₁ op v).map λ v ↦ .val v ty
    | .none => .ok $ .unaryApp op r ty
  | .binaryApp op x y ty => do
    let x ← tpeExpr x req es
    let y ← tpeExpr y req es

    .ok $ .binaryApp op x y ty
  | .getAttr e a ty => do
    let r ← tpeExpr e req es
    sorry
  | .set xs ty => do
    let rs ← xs.mapM₁ (fun ⟨x₁, _⟩ => tpeExpr x₁ req es)
    match rs.mapM Residual.asValue with
    | .some vs => .ok $ .val (.set (Set.mk vs)) ty
    | .none => .ok $ .set rs ty
  | .record m ty => do
    let m₁ ← m.mapM₁ (fun ⟨(a, x₁), _⟩ => do
      let v ← tpeExpr x₁ req es
      pure (a, v))
    match m₁.mapM λ (a, r₁) ↦ do
      let v₁ ← r₁.asValue
      pure (a, v₁) with
    | .some xs => .ok $ .val (.record (Map.mk xs)) ty
    | .none => .ok $ .record m₁ ty
  | .hasAttr e a ty => sorry

def tpePolicy (schema : Schema)
  (p : Policy)
  (req : PartialRequest)
  (es : PartialEntities)
  : Except Error Residual :=
  match findMatchingEnv schema req es with
    | .some env => do
      let expr := substituteAction env.reqty.action p.toExpr
      let (te, _) ← (typeOf expr ∅ env).mapError Error.invalidPolicy
      (tpeExpr te req es).mapError Error.evaluation
    | .none => .error Error.noValidEnvironment

end Cedar.TPE
