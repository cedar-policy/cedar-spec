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

/- Convert an optional value to a residual: Return `.error ty` when it's none -/
def someOrError : Option Value → CedarType → Residual
  | .some v, ty => .val v ty
  | .none,   ty => .error ty

/- Convert an optional value to a residual: Return `self` when it's none -/
def someOrSelf : Option Value → CedarType → Residual → Residual
  | .some v, ty, _   => .val v ty
  | .none,   _, self => self

def varₚ (req : PartialRequest) (var : Var) (ty : CedarType) : Residual :=
  match var with
  | .principal => varₒ req.principal.asEntityUID
  | .resource  => varₒ req.resource.asEntityUID
  | .action    => varₒ req.action
  | .context   => varₒ (req.context.map (.record ·))
where
  varₒ := (someOrSelf · ty (.var var ty))

def ite (c t e : Residual) (ty : CedarType) : Residual :=
  match c with
  | .val (.prim (.bool b)) _ => if b then t else e
  | .error _                 => .error ty
  | _                        => .ite c t e ty

def and : Residual → Residual → CedarType → Residual
  | .val true  _, r, _ => r
  | .val false _, _, _ => false
  | .error _, _, ty    => .error ty
  | l, .val true _, _  => l
  | l, r, ty           => .and l r ty

def or : Residual → Residual → CedarType → Residual
  | .val true  _, _, _ => true
  | .val false _, r, _ => r
  | .error _, _, ty    => .error ty
  | l, .val false _, _ => l
  | l, r, ty           => .and l r ty

def apply₁ (op₁ : UnaryOp) (r : Residual) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | _ =>
    match r.asValue with
    | .some v => someOrError (Spec.apply₁ op₁ v).toOption ty
    | .none   => .unaryApp op₁ r ty

def inₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) : Option Bool :=
  if uid₁ = uid₂ then .some true else (es.ancestors uid₁).map (Set.contains · uid₂)

def inₛ (uid : EntityUID) (vs : Set Value) (es : PartialEntities): Option Bool := do
  (← vs.toList.mapM (Except.toOption ∘ Value.asEntityUID)).anyM (inₑ uid · es)

def hasTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Option Bool :=
  (es.tags uid).map (Map.contains · tag)

def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) (ty : CedarType) : Residual :=
  match es.tags uid with
  | .some tags => someOrError (tags.find? tag) ty
  | .none => .binaryApp .getTag uid tag ty

def apply₂ (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType) : Residual :=
  match op₂, r₁, r₂ with
  | .eq, .val v₁ _, .val v₂ _ =>
    .val (v₁ == v₂) ty
  | .less, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .val (i < j : Bool) ty
  | .less, .val (.ext (.datetime d₁)) _, .val (.ext (.datetime d₂)) _ =>
    .val (d₁ < d₂: Bool) ty
  | .less, .val (.ext (.duration d₁)) _, .val (.ext (.duration d₂)) _ =>
    .val (d₁ < d₂: Bool) ty
  | .lessEq, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    .val (i ≤ j : Bool) ty
  | .lessEq, .val (.ext (.datetime d₁)) _, .val (.ext (.datetime d₂)) _ =>
    .val (d₁ ≤ d₂: Bool) ty
  | .lessEq, .val (.ext (.duration d₁)) _, .val (.ext (.duration d₂)) _ =>
    .val (d₁ ≤ d₂: Bool) ty
  | .add, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    someOrError (i.add? j) ty
  | .sub, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    someOrError (i.sub? j) ty
  | .mul, .val (.prim (.int i)) _, .val (.prim (.int j)) _ =>
    someOrError (i.mul? j) ty
  | .contains, .val (.set vs₁) _, .val v₂ _ =>
    .val (vs₁.contains v₂) ty
  | .containsAll, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .val (vs₂.subset vs₁) ty
  | .containsAny, .val (.set vs₁) _, .val (.set vs₂) _ =>
    .val (vs₁.intersects vs₂) ty
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.prim (.entityUID uid₂)) _ =>
    someOrSelf (inₑ uid₁ uid₂ es) ty self
  | .mem, .val (.prim (.entityUID uid₁)) _, .val (.set vs) _ =>
    someOrSelf (inₛ uid₁ vs es) ty self
  | .hasTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    someOrSelf (hasTag uid₁ tag es) ty self
  | .getTag, .val (.prim (.entityUID uid₁)) _, .val (.prim (.string tag)) _ =>
    getTag uid₁ tag es ty
  | _, .error _, _ | _, _, .error _ => .error ty
  | _, _, _ => self
where
  self := .binaryApp op₂ r₁ r₂ ty

def attrsOf (r : Residual) (lookup : EntityUID → Option (Map Attr Value)) : Option (Map Attr Value) :=
  match r with
  | .val (.record m) _              => .some m
  | .val (.prim (.entityUID uid)) _ => lookup uid
  | _                               => none

def hasAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | _ =>
    match attrsOf r es.attrs with
    | .some m => m.contains a
    | .none   => .hasAttr r a ty

def getAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | _ =>
    match attrsOf r es.attrs with
    | .some m => someOrError (m.find? a) ty
    | .none   => .getAttr r a ty

def set (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some xs => .val (.set (Set.make xs)) ty
  | .none    => if rs.any Residual.isError then .error ty else .set rs ty

def record (m : List (Attr × Residual)) (ty : CedarType) : Residual :=
  match m.mapM λ (a, r₁) => bindAttr a r₁.asValue with
  | .some xs => .val (.record (Map.make xs)) ty
  | .none    => if m.any λ (_, r₁) => r₁.isError then .error ty else .record m ty

def call (xfn : ExtFun) (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some xs => someOrError (Spec.call xfn xs).toOption ty
  | .none    => if rs.any Residual.isError then .error ty else .call xfn rs ty

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
  any_goals
    rename_i h
    replace h := List.sizeOf_lt_of_mem h
    try simp at h
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
          -- let expr := substituteAction env.reqty.action p.toExpr
          let (te, _) ← (typeOf p.toExpr ∅ env).mapError Error.invalidPolicy
          .ok (evaluate te req es)
      else .error .invalidRequestOrEntities
    | .none => .error .invalidEnvironment

end Cedar.TPE
