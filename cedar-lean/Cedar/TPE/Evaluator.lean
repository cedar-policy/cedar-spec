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

def apply₁ (op₁ : UnaryOp) (r : Residual) (ty : CedarType) : Result Residual :=
  match r.asValue with
  | .some v => (Spec.apply₁ op₁ v).map (Value.toResidual · ty)
  | .none => .ok (.unaryApp op₁ r ty)

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
   ((es.tags uid).map
      λ tags ↦ tags.contains tag)

def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Result (Option Value) := do
  match es.tags uid with
  | .some tags =>
    match tags.find? tag with
    | .some val => .ok $ .some val
    | .none => .error .tagDoesNotExist
  | .none => .ok .none

def apply₂ (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType) : Result Residual :=
  match op₂, r₁, r₂ with
  | .eq, .val v₁ _, .val v₂ _ =>
    .ok (.val (v₁ == v₂) ty)
  | .less, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .ok (.val (i < j : Bool) ty)
  | .lessEq, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .ok (.val (i ≤ j : Bool) ty)
  | .add, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    (intOrErr (i.add? j)).map (Value.toResidual · ty)
  | .sub, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    (intOrErr (i.sub? j)).map (Value.toResidual · ty)
  | .mul, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    (intOrErr (i.mul? j)).map (Value.toResidual · ty)
  | .contains, .val (.set vs₁) _, .val v₂ _ =>
    .ok (.val (vs₁.contains v₂) ty)
  | .containsAll, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .ok (.val (vs₂.subset vs₁) ty)
  | .containsAny, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .ok (.val (vs₁.intersects vs₂) ty)
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.prim (.entityUID uid₂)) _ =>
    .ok (((inₑ uid₁ uid₂ es).map Coe.coe).getD self)
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.set vs) _ =>
    (inₛ uid₁ vs es).map (λ b => (b.map Coe.coe).getD self)
  | .hasTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    .ok (((hasTag uid₁ tag es).map Coe.coe).getD self)
  | .getTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    (getTag uid₁ tag es).map (λ v => (v.map λ v => (.val v ty)).getD self)
  | _, _, _ =>
    .ok self
where self := .binaryApp op₂ r₁ r₂ ty

def hasAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Result Residual :=
  match r with
    | .val (.record m) _ => .ok (m.contains a)
    | .val (.prim (.entityUID uid)) _ =>
      match es.attrs uid with
      | .some m  => .ok (m.contains a)
      | .none => .ok (.hasAttr r a ty)
    | _ => .ok (.hasAttr r a ty)

def getAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Result Residual :=
  match r with
  | .val (.record xs) _ =>
    (xs.findOrErr a .attrDoesNotExist).map
      (Value.toResidual · ty)
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some m  => (m.findOrErr a .attrDoesNotExist).map
      (Value.toResidual · ty)
    | .none => .ok (.getAttr r a ty)
  | _ => .ok (.getAttr r a ty)

def set (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some vs => .val (Value.set (Set.make vs)) ty
  | .none => Residual.set rs ty

def bindAttr [Monad m] (a : Attr) (res : m α) : m (Attr × α) := do
  let v ← res
  pure (a, v)

def record (m : List (Attr × Residual)) (ty : CedarType) : Residual :=
  match m.mapM λ (a, r₁) ↦ bindAttr a r₁.asValue with
  | .some xs => .val (.record (Map.make xs)) ty
  | .none => .record m ty

def call (f : ExtFun) (rs : List Residual) (ty : CedarType) : Result Residual :=
  match rs.mapM Residual.asValue with
    | .some vs => (Spec.call f vs).map (Value.toResidual · ty)
    | .none => .ok (.call f rs ty)

def tpeExpr (x : TypedExpr)
    (req : PartialRequest)
    (es : PartialEntities)
    : Result Residual :=
  match x with
  | .lit p ty => .ok $ .val p ty
  | .var .principal ty =>
    match req.principal.asEntityUID with
    | .some uid => .ok $ .val (.prim (.entityUID uid)) ty
    | .none => .ok $ .var .principal ty
  | .var .resource ty =>
    match req.resource.asEntityUID with
    | .some uid => .ok $ .val (.prim (.entityUID uid)) ty
    | .none => .ok $ .var .resource ty
  | .var .action ty => .ok $ .val (.prim (.entityUID req.action)) ty
  | .var .context ty =>
    match req.context with
    | .some m => .ok (.val (.record m) ty)
    | .none => .ok $ .var .context ty
  | .ite c t e ty => do
    let c ← tpeExpr c req es
    match c with
    | .val (.prim (.bool b)) _ =>
      if b then tpeExpr t req es else tpeExpr e req es
    | _ =>
      let t ← tpeExpr t req es
      let e ← tpeExpr e req es
      .ok $ .ite c t e ty
  | .and l r ty => do
    let l ← tpeExpr l req es
    match l with
    | .val (.prim (.bool b)) _ =>
      if b then tpeExpr r req es else .ok $ .val (.prim (.bool b)) (.bool .ff)
    | _ =>
      let r ← tpeExpr r req es
      match r with
      | .val true _ => .ok l
      | _ => .ok $ .and l r ty
  | .or l r ty => do
    let l ← tpeExpr l req es
    match l with
    | .val (.prim (.bool b)) _ =>
      if !b then tpeExpr r req es else .ok $ .val (.prim (.bool b)) (.bool .tt)
    | _ =>
      let r ← tpeExpr r req es
      match r with
      | .val false _ => .ok l
      | _ => .ok $ .or l r ty
  | .unaryApp op₁ e ty => do
    let r ← tpeExpr e req es
    apply₁ op₁ r ty
  | .binaryApp op₂ x y ty => do
    let x ← tpeExpr x req es
    let y ← tpeExpr y req es
    apply₂ op₂ x y es ty
  | .hasAttr e a ty => do
    let r ← tpeExpr e req es
    hasAttr r a es ty
  | .getAttr e a ty => do
    let r ← tpeExpr e req es
    getAttr r a es ty
  | .set xs ty => do
    let rs ← xs.mapM₁ (λ ⟨x₁, _⟩ ↦ tpeExpr x₁ req es)
    .ok (set rs ty)
  | .record m ty => do
    let m ← m.mapM₁ (λ ⟨(a, x₁), _⟩ ↦ bindAttr a (tpeExpr x₁ req es))
    .ok (record m ty)
  | .call f args ty => do
    let rs ← args.mapM₁ (λ ⟨x₁, _⟩ ↦ tpeExpr x₁ req es)
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
        (tpeExpr te req es).mapError Error.evaluation
      else .error .invalidRequestOrEntities
    | .none => .error .inValidEnvironment

end Cedar.TPE
