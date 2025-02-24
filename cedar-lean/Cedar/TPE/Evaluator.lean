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
import Cedar.TPE.Residual

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

inductive Error where
  | evaluation (err : Spec.Error)
  | invalidPolicy (err : TypeError)
  | noValidEnvironment
  | invalidRequestOrEntities

instance : Coe Spec.Error Error where
  coe := Error.evaluation

def inₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) (ty : CedarType): Residual :=
  if uid₁ = uid₂
    then .val true ty
    else
    match es.find? uid₁ with
    | .some ⟨_, .some uids, _⟩ => .val (uids.contains uid₂) ty
    | .some ⟨_, .none, _⟩ => .binaryApp .mem (.val (.prim (.entityUID uid₁)) (.entity uid₁.ty)) (.val (.prim (.entityUID uid₂)) (.entity uid₂.ty)) ty
    | .none => .val false ty

def apply₂ (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType): Result Residual :=
  let self : Result Residual := .ok $ .binaryApp op₂ r₁ r₂ ty
  match op₂, r₁, r₂ with
  | .eq, (.val v₁ _), (.val v₂ _) => .ok $ .val (v₁ == v₂) ty
  | .less, (.val (.prim (.int i)) _), (.val (.prim (.int j)) _) =>
    .ok $ .val ((i < j): Bool) ty
  | .lessEq, (.val (.prim (.int i)) _), (.val (.prim (.int j)) _) =>
    .ok $ .val ((i ≤ j): Bool) ty
  | .add, (.val (.prim (.int i)) _), (.val (.prim (.int j)) _) =>
    (intOrErr (i.add? j)).map (Value.toResidual · ty)
  | .sub, (.val (.prim (.int i)) _), (.val (.prim (.int j)) _) =>
    (intOrErr (i.sub? j)).map (Value.toResidual · ty)
  | .mul, (.val (.prim (.int i)) _), (.val (.prim (.int j)) _) =>
    (intOrErr (i.mul? j)).map (Value.toResidual · ty)
  | .contains, (.val (.set vs₁) _), (.val v₂ _) =>
    .ok $ .val (vs₁.contains v₂) ty
  | .containsAll, (.val (.set vs₁) _), (.val (.set vs₂) _) =>
    .ok $ .val (vs₂.subset vs₁) ty
  | .containsAny, (.val (.set vs₁) _), (.val (.set vs₂) _) =>
    .ok $ .val (vs₁.intersects vs₂) ty
  | .mem, (.val (.prim (.entityUID uid₁)) _), (.val (.prim (.entityUID uid₂)) _) =>
    .ok $ inₑ uid₁ uid₂ es ty
  | .mem, (.val (.prim (.entityUID uid₁)) _), (.val (.set vs) _) => do
    let uids ← vs.mapOrErr Value.asEntityUID .typeError
    let rs := uids.toList.map λ uid ↦ inₑ uid₁ uid es ty
    if rs.any λ r ↦ match r with
      | .val (.prim (.bool _)) _ => false
      | _ => true
    then self
    else .ok $ (.val (.prim (.bool (rs.any λ r ↦ match r with
      | .val (.prim (.bool true)) _ => true
      | _ => false
    ))) ty)
  | .hasTag, (.val (.prim (.entityUID uid₁)) _), (.val (.prim (.string tag)) _) =>
    match es.find? uid₁ with
    | .some ⟨_, _, .some m⟩ => .ok $ .val (m.contains tag) ty
    | .some ⟨_, _, .none⟩ => self
    | .none => .ok $ .val false ty
  | .getTag, (.val (.prim (.entityUID uid₁)) _), (.val (.prim (.string tag)) _) =>
    match es.find? uid₁ with
    | .some ⟨_, _, .some m⟩ => (m.findOrErr tag .tagDoesNotExist).map (Value.toResidual · ty)
    | .some ⟨_, _, .none⟩ => self
    | .none => .error .entityDoesNotExist
  | _, _, _ => self

def tpeExpr (x : TypedExpr)
    (req : PartialRequest)
    (es : PartialEntities)
    : Result Residual :=
  match x with
  | .lit p ty => .ok $ .val p ty
  | .var .principal ty =>
    match req.principal.asEntityUID with
    | .some uid => .ok $ .prim (.entityUID uid) ty
    | .none => .ok x
  | .var .resource ty =>
    match req.resource.asEntityUID with
    | .some uid => .ok $ .prim (.entityUID uid) ty
    | .none => .ok x
  | .var .action ty => .ok $ .prim (.entityUID req.action) ty
  | .var .context ty =>
    match req.context with
    | .some m => .ok (.val (.record m) ty)
    | .none => .ok x
  | .ite c t e ty => do
    let c ← tpeExpr c req es
    match c with
    | .prim (.bool b) _ =>
      if b then tpeExpr t req es else tpeExpr e req es
    | _ =>
      let t ← tpeExpr t req es
      let e ← tpeExpr e req es
      .ok $ .ite c t e ty
  | .and l r ty => do
    let l ← tpeExpr l req es
    match l with
    | .prim (.bool b) _ =>
      if b then tpeExpr r req es else .ok $ .prim (.bool b) (.bool .ff)
    | _ =>
      let r ← tpeExpr r req es
      .ok $ .and l r ty
  | .or l r ty => do
    let l ← tpeExpr l req es
    match l with
    | .prim (.bool b) _ =>
      if !b then tpeExpr r req es else .ok $ .prim (.bool b) (.bool .tt)
    | _ =>
      let r ← tpeExpr r req es
      .ok $ .or l r ty
  | .call f args ty => do
    let rs ← args.mapM₁ (λ ⟨x₁, _⟩ ↦ tpeExpr x₁ req es)
    match rs.mapM Residual.asValue with
    | .some vs => (Spec.call f vs).map (Value.toResidual · ty)
    | .none => .ok $ .call f rs ty
  | .unaryApp op e ty => do
    let r ← tpeExpr e req es
    match r.asValue with
    | .some v => (apply₁ op v).map (Value.toResidual · ty)
    | .none => .ok $ .unaryApp op r ty
  | .binaryApp op x y ty => do
    let x ← tpeExpr x req es
    let y ← tpeExpr y req es
    apply₂ op x y es ty
  | .getAttr e a ty => do
    let r ← tpeExpr e req es
    match r with
    | .val (.record xs) _ =>
      (xs.findOrErr a .attrDoesNotExist).map
        (Value.toResidual · ty)
    | .val (.prim (.entityUID uid)) _ =>
      let data ← es.findOrErr uid .entityDoesNotExist
      match data.attrs with
      | .some m =>
        (m.findOrErr a .attrDoesNotExist).map
          (Value.toResidual · ty)
      | .none => .ok $ .getAttr r a ty
    | _ => .ok $ .getAttr r a ty
  | .set xs ty => do
    let rs ← xs.mapM₁ (λ ⟨x₁, _⟩ ↦ tpeExpr x₁ req es)
    match rs.mapM Residual.asValue with
    | .some vs => .ok $ .val (.set (Set.mk vs)) ty
    | .none => .ok $ .set rs ty
  | .record m ty => do
    let m₁ ← m.mapM₁ (λ ⟨(a, x₁), _⟩ ↦ do
      let v ← tpeExpr x₁ req es
      pure (a, v))
    match m₁.mapM λ (a, r₁) ↦ do
      let v₁ ← r₁.asValue
      pure (a, v₁) with
    | .some xs => .ok $ .val (.record (Map.mk xs)) ty
    | .none => .ok $ .record m₁ ty
  | .hasAttr e a ty => do
    let r ← tpeExpr e req es
    match r with
    | .val (.record xs) _ =>
      .ok $ .val (xs.contains a) ty
    | .val (.prim (.entityUID uid)) _ =>
      match es.find? uid with
      | .some ⟨ .some m, _ , _⟩  =>
        .ok $ .val (m.contains a) ty
      | .some ⟨ .none, _ , _⟩  => .ok $ .hasAttr r a ty
      | .none => .ok $ .val false ty
    | _ => .ok $ .getAttr r a ty
termination_by x
decreasing_by
  all_goals
    simp_wf
    try omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    have h₁ := List.sizeOf_lt_of_mem h
    simp at h₁
    omega

def tpePolicy (schema : Schema)
  (p : Policy)
  (req : PartialRequest)
  (es : PartialEntities)
  : Except Error Residual :=
  match schema.getEnvironment req.principal.ty req.resource.ty req.action with
    | .some env => if RequestAndEntitiesIsValid env req es then
      do
        let expr := substituteAction env.reqty.action p.toExpr
        let (te, _) ← (typeOf expr ∅ env).mapError Error.invalidPolicy
        (tpeExpr te req es).mapError Error.evaluation
      else .error .invalidRequestOrEntities
    | .none => .error Error.noValidEnvironment

end Cedar.TPE
