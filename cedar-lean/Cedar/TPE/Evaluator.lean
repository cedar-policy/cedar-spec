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

/--
Reduce a resolved attribute state to a residual
-/
def stateToResidual (s : AttrState) (ty : CedarType) (self : Residual) : Residual :=
  match s with
  | .value v => .val v ty
  | .absent  => .error ty
  | .partialRecord r =>
    match ty with
    | .record rty => someOrSelf ((PartialRecord.asValues? r rty).map Value.record) ty self
    | _           => self
  | .present
  | .unknown => self

def varₚ (req : PartialRequest) (var : Var) (ty : CedarType) : Residual :=
  match var with
  | .principal => varₒ req.principal.asEntityUID
  | .resource  => varₒ req.resource.asEntityUID
  | .action    => varₒ req.action
  | .context   =>
    match req.context with
    | .some r => stateToResidual (.partialRecord r) ty (.var var ty)
    | .none   => .var var ty
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
  | l, .val false rty, ty  =>
    if l.errorFree then false else .and l (.val false rty) ty
  | l, r, ty           => .and l r ty

def or : Residual → Residual → CedarType → Residual
  | .val true  _, _, _ => true
  | .val false _, r, _ => r
  | .error _, _, ty    => .error ty
  | l, .val false _, _ => l
  | l, .val true rty, ty  =>
    if l.errorFree then true else .or l (.val true rty) ty
  | l, r, ty           => .or l r ty

/-  Given a unary operation applied to a non-value residual, reduce it to a value if possible -/
def tryDecideResidual₁ (op₁ : UnaryOp) (r : Residual) : Option Value :=
  if r.errorFree then
    match op₁, r.typeOf with
    | .is ety₁, .entity ety₂ => .some (ety₁ == ety₂)
    | _, _ => .none
  else .none

def apply₁ (op₁ : UnaryOp) (r : Residual) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | _ =>
  match tryDecideResidual₁ op₁ r with
  | .some v => .val v ty
  | .none =>
  match r.asValue with
  | .some v => someOrError (Spec.apply₁ op₁ v).toOption ty
  | .none => .unaryApp op₁ r ty

def inₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) : Option Bool :=
  if uid₁ = uid₂ then .some true else (es.ancestors uid₁).map (Set.contains · uid₂)

def inₛ (uid : EntityUID) (vs : Set Value) (es : PartialEntities): Option Bool := do
  (← vs.toList.mapM (Except.toOption ∘ Value.asEntityUID)).ternaryAny (inₑ uid · es)

def hasTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Option Bool :=
  match entityTag es uid tag with
  | .value _
  | .partialRecord _
  | .present => .some true
  | .absent  => .some false
  | .unknown => .none

def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) (ty : CedarType) : Residual :=
  stateToResidual (entityTag es uid tag) ty (.binaryApp .getTag uid tag ty)

/- Given a unary operation applied to a non-value residuals, reduce it to a value if possible -/
def tryDecideResidual₂ (env : TypeEnv) (op₂ : BinaryOp) (r₁ r₂ : Residual) : Option Value :=
  if r₁.errorFree && r₂.errorFree then
    match op₂, r₁.typeOf, r₂.typeOf with
    | .mem, .entity ety₁, .entity ety₂
    | .mem, .entity ety₁, .set (.entity ety₂) => if !env.descendentOf ety₁ ety₂ then .some false else none
    | .eq,  .entity ety₁, .entity ety₂        => if ety₁ != ety₂ then .some false else none
    | .hasTag, .entity ety, .string           => if env.ets.tags? ety == some .none then .some false else none
    | _, _, _                                 => .none
  else .none

def apply₂ (env : TypeEnv) (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r₁, r₂ with
  | .error _, _ | _, .error _ => .error ty
  | _, _ =>
  match tryDecideResidual₂ env op₂ r₁ r₂ with
  | .some v => .val v ty
  | .none =>
  match r₁.asValue, r₂.asValue with
  | .some v₁, .some v₂ =>
    match op₂, v₁, v₂ with
    | .eq, _, _ =>
      .val (v₁ == v₂) ty
    | .less, .prim (.int i), .prim (.int j) =>
      .val (i < j : Bool) ty
    | .less, .ext (.datetime d₁), .ext (.datetime d₂) =>
      .val (d₁ < d₂: Bool) ty
    | .less, .ext (.duration d₁), .ext (.duration d₂) =>
      .val (d₁ < d₂: Bool) ty
    | .lessEq, .prim (.int i), .prim (.int j) =>
      .val (i ≤ j : Bool) ty
    | .lessEq, .ext (.datetime d₁), .ext (.datetime d₂) =>
      .val (d₁ ≤ d₂: Bool) ty
    | .lessEq, .ext (.duration d₁), .ext (.duration d₂) =>
      .val (d₁ ≤ d₂: Bool) ty
    | .add, .prim (.int i), .prim (.int j) =>
      someOrError (i.add? j) ty
    | .sub, .prim (.int i), .prim (.int j) =>
      someOrError (i.sub? j) ty
    | .mul, .prim (.int i), .prim (.int j) =>
      someOrError (i.mul? j) ty
    | .contains, .set vs₁, _ =>
      .val (vs₁.contains v₂) ty
    | .containsAll, .set vs₁, .set vs₂ =>
      .val (vs₂.subset vs₁) ty
    | .containsAny, .set vs₁, .set vs₂ =>
      .val (vs₁.intersects vs₂) ty
    | .mem, .prim (.entityUID uid₁), .prim (.entityUID uid₂) =>
      someOrSelf (inₑ uid₁ uid₂ es) ty self
    | .mem, .prim (.entityUID uid₁), .set vs =>
      someOrSelf (inₛ uid₁ vs es) ty self
    | .hasTag, .prim (.entityUID uid₁), .prim (.string tag) =>
      someOrSelf (hasTag uid₁ tag es) ty self
    | .getTag, .prim (.entityUID uid₁), .prim (.string tag) =>
      getTag uid₁ tag es ty
    | _, _, _ => .error ty
  | _, _ => self
  where
  self := .binaryApp op₂ r₁ r₂ ty


/- Given a `has` expression applied to a non-value residuals, reduce it to a value if possible -/
def tryDecideHasResidual (env : TypeEnv) (r : Residual) (a : Attr) : Option Value :=
  if r.errorFree then
    match r.typeOf with
    | .record rty =>
      if (rty.find? a).isNone then .some false else .none
    | .entity ety =>
      match env.ets.attrs? ety with
      | .some rty =>
        if (rty.find? a).isNone then .some false else none
      | .none => .none
    | _ => .none
  else .none

def hasAttr (env : TypeEnv) (req : PartialRequest) (r : Residual) (a : Attr)
  (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | _ =>
  match tryDecideHasResidual env r a with
  | .some v => .val v ty
  | .none =>
  match attrStateAt env req es r a with
  | .value _
  | .partialRecord _
  | .present => .val true ty
  | .absent  => .val false ty
  | .unknown => .hasAttr r a ty

def getAttr (env : TypeEnv) (req : PartialRequest) (r : Residual) (a : Attr)
  (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | _ => stateToResidual (attrStateAt env req es r a) ty (.getAttr r a ty)

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
  (env : TypeEnv)
  (x : Residual)
  (req : PartialRequest)
  (es : PartialEntities) : Residual :=
  match x with
  | .val l ty => .val l ty
  | .var v ty => varₚ req v ty
  | .error ty => .error ty
  | .ite x₁ x₂ x₃ ty =>
    ite (evaluate env x₁ req es) (evaluate env x₂ req es) (evaluate env x₃ req es) ty
  | .and x₁ x₂ ty =>
    and (evaluate env x₁ req es) (evaluate env x₂ req es) ty
  | .or x₁ x₂ ty =>
    or (evaluate env x₁ req es) (evaluate env x₂ req es) ty
  | .unaryApp op₁ x₁ ty =>
    apply₁ op₁ (evaluate env x₁ req es) ty
  | .binaryApp op₂ x₁ x₂ ty =>
    apply₂ env op₂ (evaluate env x₁ req es) (evaluate env x₂ req es) es ty
  | .hasAttr x₁ a ty =>
    hasAttr env req (evaluate env x₁ req es) a es ty
  | .getAttr x₁ a ty =>
    getAttr env req (evaluate env x₁ req es) a es ty
  | .set xs ty =>
    set (xs.map₁ (λ ⟨x₁, _⟩ => evaluate env x₁ req es)) ty
  | .record axs ty =>
    record (axs.map₁ (λ ⟨(a, x₁), _⟩ => (a, (evaluate env x₁ req es)))) ty
  | .call xfn xs ty =>
    call xfn (xs.map₁ (λ ⟨x₁, _⟩ => evaluate env x₁ req es)) ty
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

open Cedar.Spec Cedar.Validation

/-- Partially evaluating a policy.
Note that this function actually evaluates a type-lifted version of `TypedExpr`
produced by the type checker, as opposed to evaluating the expression directly.
This design is to simplify proofs otherwise we need to prove theorems that
state type-lifting (i.e, `TypedExpr.liftBoolTypes`) do not change the results
of evaluating residuals. The soundness theorem still holds. That is,
reauthorizing the residuals produces the same outcome as authorizing the input
expressions with consistent requests/entities. It is just that the types in the
residuals are all lifted. We essentially trade efficiency for ease of proofs,
which I (Shaobo) think is fine because the Lean model is a reference model not
used in production.
-/
def evaluatePolicy (schema : Schema)
  (p : Policy)
  (req : PartialRequest)
  (es : PartialEntities)
  : Except Error Residual :=
  match validatePartialRequest schema req with
    | .ok env =>
      if entitiesIsValid env.schema es
      then
        do
          checkEntities schema p.toExpr|>.mapError .invalidPolicy
          let expr := substituteAction env.reqty.action p.toExpr
          let (te, _) ← (typeOf expr ∅ env).mapError Error.invalidPolicy
          .ok (evaluate env te.liftBoolTypes.toResidual req es)
      else .error .invalidRequestOrEntities
    | .error _ => .error .invalidEnvironment

end Cedar.TPE
