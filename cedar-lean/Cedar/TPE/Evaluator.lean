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
  | invalidEnvironment
  | invalidRequestOrEntities
deriving Repr, Inhabited, DecidableEq

instance : Coe Spec.Error Error where
  coe := Error.evaluation

def optionValueToResidual (v : Option Value) (ty : CedarType) : Residual :=
  match v with
  | .some v => .val v ty
  | .none => .error ty

def varₚ (req : PartialRequest) (var : Var) (ty : CedarType) : Residual :=
  match var with
  | .principal => varₒ req.principal.asEntityUID .principal ty
  | .resource => varₒ req.resource.asEntityUID .resource ty
  | .action => varₒ req.action .action ty
  | .context => varₒ (req.context.map (.record ·)) .context ty
where varₒ (val : Option Value) var ty :=
  match val with
  | .some v => .val v ty
  | .none   => .var var ty

def ite (c t e : Residual) (ty : CedarType) : Residual :=
  match c with
  | .val (.prim (.bool b)) _ => if b then t else e
  | _ => .ite c t e ty

def and (l r : Residual) (ty : CedarType) : Residual :=
  match l, r with
  | .val true _, _ => r
  | .val false _, _ => false
  | _, .val true _ => l
  | _, _ => .and l r ty

def or (l r : Residual) (ty : CedarType) : Residual :=
  match l, r with
  | .val true _, _ => true
  | .val false _, _ => r
  | _, .val false _ => l
  | _, _ => .and l r ty

def apply₁ (op₁ : UnaryOp) (r : Residual) (ty : CedarType) : Residual :=
  match r.asValue with
  | .some v =>
    match (Spec.apply₁ op₁ v).map (Value.toResidual · ty) with
    | .ok v => v
    | .error _ => .error ty
  | .none => .unaryApp op₁ r ty

def inₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) : Option Bool :=
  if uid₁ = uid₂ then .some true else (es.ancestors uid₁).map (Set.contains · uid₂)

def inₛ (uid : EntityUID) (vs : Set Value) (es : PartialEntities): Option Bool := do
  let uids ← vs.toList.mapM (Except.toOption ∘ Value.asEntityUID)
  uids.anyM (inₑ uid · es)

def hasTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Option Bool :=
  (es.tags uid).map (Map.contains · tag)

def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) (ty : CedarType) : Option Residual := do
  let tags ← es.tags uid
  match tags.find? tag with
  | .some v => .some (.val v ty)
  | .none => .some (.error ty)

def apply₂ (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType) : Residual :=
  match op₂, r₁, r₂ with
  | .eq, .val v₁ _, .val v₂ _ =>
    .val (v₁ == v₂) ty
  | .less, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .val (i < j : Bool) ty
  | .lessEq, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .val (i ≤ j : Bool) ty
  | .add, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    optionValueToResidual (i.add? j) ty
  | .sub, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    optionValueToResidual (i.sub? j) ty
  | .mul, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    optionValueToResidual (i.mul? j) ty
  | .contains, .val (.set vs₁) _, .val v₂ _ =>
    .val (vs₁.contains v₂) ty
  | .containsAll, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .val (vs₂.subset vs₁) ty
  | .containsAny, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .val (vs₁.intersects vs₂) ty
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.prim (.entityUID uid₂)) _ =>
    ((inₑ uid₁ uid₂ es).map Coe.coe).getD self
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.set vs) _ =>
    ((inₛ uid₁ vs es).map Coe.coe).getD self
  | .hasTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    ((hasTag uid₁ tag es).map Coe.coe).getD self
  | .getTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    (getTag uid₁ tag es ty).getD self
  | _, _, _ =>
    self
where
  self := .binaryApp op₂ r₁ r₂ ty

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
    optionValueToResidual (xs.find? a) ty
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some m  =>
      optionValueToResidual (m.find? a) ty
    | .none => self
  | _ => self
where self := .getAttr r a ty

def set (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some vs => .val (.set (Set.make vs)) ty
  | .none => .set rs ty

def record (m : List (Attr × Residual)) (ty : CedarType) : Residual :=
  match m.mapM λ (a, r₁) => bindAttr a r₁.asValue with
  | .some xs => .val (.record (Map.make xs)) ty
  | .none => .record m ty

def call (f : ExtFun) (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some vs => optionValueToResidual (Spec.call f vs).toOption ty
  | .none => .call f rs ty

def evaluate
  (x : TypedExpr)
  (req : PartialRequest)
  (es : PartialEntities) : Residual :=
  match x with
  | .lit l ty => .val l ty
  | .var v ty => varₚ req v ty
  | .ite x₁ x₂ x₃ ty =>
    ite (evaluate x₁ req es) (evaluate x₂ req es) (evaluate x₃ req es) ty
  | .and x₁ x₂ ty =>
    and (evaluate x₁ req es) (evaluate x₂ req es) ty
  | .or x₁ x₂ ty =>
    or (evaluate x₁ req es) (evaluate x₂ req es) ty
  | .unaryApp op₁ x₁ ty =>
    apply₁ op₁ (evaluate x₁ req es) ty
  | .binaryApp op₂ x₁ x₂ ty =>
    apply₂ op₂ (evaluate x₁ req es) (evaluate x₂ req es) es ty
  | .hasAttr x₁ a ty =>
    hasAttr (evaluate x₁ req es) a es ty
  | .getAttr x₁ a ty =>
    getAttr (evaluate x₁ req es) a es ty
  | .set xs ty =>
    set (xs.map₁ (λ ⟨x₁, _⟩ => evaluate x₁ req es)) ty
  | .record axs ty =>
    record (axs.map₁ (λ ⟨(a, x₁), _⟩ => (a, (evaluate x₁ req es)))) ty
  | .call xfn xs ty =>
    call xfn (xs.map₁ (λ ⟨x₁, _⟩ => evaluate x₁ req es)) ty
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

def evaluatePolicy (schema : Schema)
  (p : Policy)
  (req : PartialRequest)
  (es : PartialEntities)
  : Except Error Residual :=
  match schema.environment? req.principal.ty req.resource.ty req.action with
    | .some env =>
      if requestAndEntitiesIsValid env req es
      then
        do
          let expr := substituteAction env.reqty.action p.toExpr
          let (te, _) ← (typeOf expr ∅ env).mapError Error.invalidPolicy
          .ok (evaluate te req es)
      else .error .invalidRequestOrEntities
    | .none => .error .invalidEnvironment

end Cedar.TPE
