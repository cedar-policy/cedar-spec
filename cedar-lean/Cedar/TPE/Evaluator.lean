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
  | inValidEnvironment
  | invalidRequestOrEntities
deriving Repr

instance : Coe Spec.Error Error where
  coe := Error.evaluation

def varₚ (req : PartialRequest) (var : Var) (ty : CedarType) : Residual :=
  match var with
  | .principal => varₒ req.principal.asEntityUID .principal ty
  | .resource => varₒ req.resource.asEntityUID .resource ty
  | .action => varₒ (req.action) .action ty
  | .context => varₒ (req.context.map (.record ·)) .context ty
where varₒ (val : Option Value) var ty :=
  match val with
  | .some v => .val v ty
  | .none   => .var var ty

def ite (c t e : Residual)(ty : CedarType) : Residual :=
  match c with
    | .val (.prim (.bool b)) _ =>
      if b then t else e
    | _ =>
      .ite c t e ty

def and (l r : Residual)(ty : CedarType) : Residual :=
  match l, r with
  | .val true _, _ => r
  | .val false _, _ => false
  | _, .val true _ => l
  | _, _ => .and l r ty

def or (l r : Residual)(ty : CedarType) : Residual :=
  match l, r with
  | .val true _, _ => true
  | .val false _, _ => r
  | _, .val false _ => l
  | _, _ => .and l r ty

def apply₁ (op₁ : UnaryOp) (r : Residual) (ty : CedarType) : Residual :=
  match r.asValue with
  | .some v => match (Spec.apply₁ op₁ v).map (Value.toResidual · ty) with
    | .ok v => v
    | .error _ => .error ty
  | .none => .unaryApp op₁ r ty

def inₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) : Option Bool :=
  if uid₁ = uid₂
  then
    pure true
  else
    ((es.ancestors uid₁).map
      λ ancestors ↦ ancestors.contains uid₂)

def inₛ (uid₁ : EntityUID) (vs : Set Value) (es : PartialEntities): Result (Option Bool) :=
  (vs.mapOrErr Value.asEntityUID .typeError).map λ uids ↦
    uids.foldl disjunction (.some false)
where disjunction accum uid₂ := do
  let l ← inₑ uid₁ uid₂ es
  let r ← accum
  pure (l || r)

def hasTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Option Bool :=
  (es.tags uid).map λ tags ↦ tags.contains tag

def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) (ty : CedarType) : Option Residual :=
  (es.tags uid).map (λ tags ↦
    ((tags.find? tag).map (.val · ty)).getD (.error ty))

def apply₂ (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType) : Residual :=
  match op₂, r₁, r₂ with
  | .eq, .val v₁ _, .val v₂ _ =>
    .val (v₁ == v₂) ty
  | .less, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .val (i < j : Bool) ty
  | .lessEq, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .val (i ≤ j : Bool) ty
  | .add, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    ((i.add? j).map (Value.toResidual · ty)).getD error
  | .sub, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    ((i.sub? j).map (Value.toResidual · ty)).getD error
  | .mul, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    ((i.mul? j).map (Value.toResidual · ty)).getD error
  | .contains, .val (.set vs₁) _, .val v₂ _ =>
    .val (vs₁.contains v₂) ty
  | .containsAll, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .val (vs₂.subset vs₁) ty
  | .containsAny, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .val (vs₁.intersects vs₂) ty
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.prim (.entityUID uid₂)) _ =>
    ((inₑ uid₁ uid₂ es).map Coe.coe).getD self
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.set vs) _ =>
    match inₛ uid₁ vs es with
    | .ok (.some b) => b
    | .ok .none => self
    | .error _ => error
  | .hasTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    ((hasTag uid₁ tag es).map Coe.coe).getD self
  | .getTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    (getTag uid₁ tag es ty).getD self
  | _, _, _ =>
    self
where
  self := .binaryApp op₂ r₁ r₂ ty
  error := .error ty

def hasAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
    | .val (.record m) _ => m.contains a
    | .val (.prim (.entityUID uid)) _ =>
      match es.attrs uid with
      | .some m  => m.contains a
      | .none => self
    | _ => self
where self := .hasAttr r a ty

def getAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .val (.record xs) _ =>
    ((xs.find? a).map (Value.toResidual · ty)).getD (.error ty)
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some m  =>
      ((m.find? a).map (Value.toResidual · ty)).getD (.error ty)
    | .none => self
  | _ => self
where self := .getAttr r a ty

def set (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some vs => .val (.set (Set.make vs)) ty
  | .none => .set rs ty

def bindAttr [Monad m] (a : Attr) (res : m α) : m (Attr × α) := do
  let v ← res
  pure (a, v)

def record (m : List (Attr × Residual)) (ty : CedarType) : Residual :=
  match m.mapM λ (a, r₁) ↦ bindAttr a r₁.asValue with
  | .some xs => .val (.record (Map.make xs)) ty
  | .none => .record m ty

def call (f : ExtFun) (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
    | .some vs => match (Spec.call f vs).map (Value.toResidual · ty) with
      | .ok v => v
      | .error _ => .error ty
    | .none => .call f rs ty

def tpeExpr (x : TypedExpr)
    (req : PartialRequest)
    (es : PartialEntities)
    : Residual :=
  match x with
  | .lit p ty => .val p ty
  | .var v ty => varₚ req v ty
  | .ite c t e ty =>
    let c := tpeExpr c req es
    let t := tpeExpr t req es
    let e := tpeExpr e req es
    ite c t e ty
  | .and l r ty =>
    let l := tpeExpr l req es
    let r := tpeExpr r req es
    and l r ty
  | .or l r ty =>
    let l := tpeExpr l req es
    let r := tpeExpr r req es
    or l r ty
  | .unaryApp op₁ e ty =>
    let r := tpeExpr e req es
    apply₁ op₁ r ty
  | .binaryApp op₂ x y ty =>
    let x := tpeExpr x req es
    let y := tpeExpr y req es
    apply₂ op₂ x y es ty
  | .hasAttr e a ty =>
    let r := tpeExpr e req es
    hasAttr r a es ty
  | .getAttr e a ty =>
    let r := tpeExpr e req es
    getAttr r a es ty
  | .set xs ty =>
    let rs := xs.map₁ (λ ⟨x₁, _⟩ ↦ tpeExpr x₁ req es)
    set rs ty
  | .record m ty =>
    let m := m.map₁ (λ ⟨(a, x₁), _⟩ ↦ (a, (tpeExpr x₁ req es)))
    record m ty
  | .call f args ty =>
    let rs := args.map₁ (λ ⟨x₁, _⟩ ↦ tpeExpr x₁ req es)
    call f rs ty
termination_by x
decreasing_by
  all_goals
    simp_wf
    try omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    have h₁ := List.sizeOf_lt_of_mem h
    simp at h₁
    omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega

def tpePolicy (schema : Schema)
  (p : Policy)
  (req : PartialRequest)
  (es : PartialEntities)
  : Except Error Residual :=
  match schema.environment? req.principal.ty req.resource.ty req.action with
    | .some env => if requestAndEntitiesIsValid env req es then
      do
        let expr := substituteAction env.reqty.action p.toExpr
        let (te, _) ← (typeOf expr ∅ env).mapError Error.invalidPolicy
        .ok (tpeExpr te req es)
      else .error .invalidRequestOrEntities
    | .none => .error .inValidEnvironment

end Cedar.TPE
