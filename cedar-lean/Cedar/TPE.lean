import Cedar.Spec.Value
import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Validation.TypedExpr
import Cedar.Validation.Validator
import Cedar.Validation.Typechecker
import Cedar.Validation.RequestEntityValidator
import Cedar.Thm.Data.List

namespace Cedar.TPE

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

structure PartialEntityUID where
  ty : EntityType                    -- Entity type is always known,
  id : Option String                 -- but entity id may not be.

def PartialEntityUID.asEntityUID (self : PartialEntityUID) : Option EntityUID :=
  self.id.map λ x ↦ ⟨ self.ty, x⟩

-- The result produced by TPE
-- We do not need `unknown`s because they can be represented by entity dereferences
inductive Residual where
  | val (v : Value) (ty : CedarType)
  | prim (p : Prim) (ty : CedarType)
  | var (v : Var)  (ty : CedarType)
  | ite (cond : Residual) (thenExpr : Residual) (elseExpr : Residual)  (ty : CedarType)
  | and (a : Residual) (b : Residual)  (ty : CedarType)
  | or (a : Residual) (b : Residual)  (ty : CedarType)
  | unaryApp (op : UnaryOp) (expr : Residual)  (ty : CedarType)
  | binaryApp (op : BinaryOp) (a : Residual) (b : Residual)  (ty : CedarType)
  | getAttr (expr : Residual) (attr : Attr)  (ty : CedarType)
  | hasAttr (expr : Residual) (attr : Attr)  (ty : CedarType)
  | set (ls : List Residual)  (ty : CedarType)
  | record (map : List (Attr × Residual))  (ty : CedarType)
  | call (xfn : ExtFun) (args : List Residual) (ty : CedarType)

def TypedExpr.toResidual : TypedExpr → Residual
  | .lit p ty => .prim p ty
  | .var v ty => .var v ty
  | .ite c x y ty => .ite (toResidual c) (toResidual x) (toResidual y) ty
  | .and a b ty => .and (toResidual a) (toResidual b) ty
  | .or a b ty => .or (toResidual a) (toResidual b) ty
  | .unaryApp op e ty => .unaryApp op (toResidual e) ty
  | .binaryApp op a b ty => .binaryApp op (toResidual a) (toResidual b) ty
  | .getAttr e a ty => .getAttr (toResidual e) a ty
  | .hasAttr e a ty => .hasAttr (toResidual e) a ty
  | .set s ty => .set (s.map₁ λ ⟨x, _⟩ ↦ toResidual x) ty
  | .record m ty => .record (m.map₁ λ ⟨(a, x), _⟩ ↦ (a, toResidual x)) ty
  | .call f args ty => .call f (args.map₁ λ ⟨x, _⟩ ↦ toResidual x) ty
decreasing_by
  all_goals
    simp_wf
    try omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    replace h := List.sizeOf_lt_of_mem h
    have h₁ : sizeOf (a, x) >= sizeOf x := by
      simp_arith
    omega
  case _ h =>
    replace h := List.sizeOf_lt_of_mem h
    omega

instance : Coe TypedExpr Residual where
  coe := TypedExpr.toResidual


def Residual.asValue : Residual → Option Value
  | .prim p _ => .some p
  | .val v _ => .some v
  | .set s _ =>
    (s.mapM₁ (fun ⟨x₁, _⟩ => x₁.asValue)).map λ x ↦ Set.mk x
  | .record m _ =>
    (m.mapM₁ (fun ⟨(a₁, x₁), _⟩ =>
      do
        let v ← x₁.asValue
        pure (a₁, v))).map λ x ↦ Map.mk x
  | _ => .none
decreasing_by
  all_goals
    simp_wf
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    have h₁ := List.sizeOf_lt_of_mem h
    simp at h₁
    omega

-- The interpreter of `Residual` that defines its semantics
def Residual.evaluate (x : Residual) (req : Request) (es: Entities) : Result Value :=
  match x with
  | .val v _ => .ok v
  | .prim p _ => .ok $ .prim p
  | .var (.principal) _ => .ok req.principal
  | .var (.resource) _ => .ok req.resource
  | .var (.action) _ => .ok req.action
  | .var (.context) _ => .ok req.context
  | .ite c x y _ => do
    let c ← c.evaluate req es
    let b ← c.asBool
    if b then x.evaluate req es else y.evaluate req es
  | .and x y _ => do
    let b ← (x.evaluate req es).as Bool
    if !b then .ok b else (y.evaluate req es).as Bool
  | .or x y _ => do
    let b ← (x.evaluate req es).as Bool
    if b then .ok b else (y.evaluate req es).as Bool
  | .unaryApp op e _ => do
    let v ← e.evaluate req es
    apply₁ op v
  | .binaryApp op x y _ => do
    let v₁ ← evaluate x req es
    let v₂ ← evaluate y req es
    apply₂ op v₁ v₂ es
  | .hasAttr e a _ => do
    let v ← e.evaluate req es
    Cedar.Spec.hasAttr v a es
  | .getAttr e a _ => do
    let v ← e.evaluate req es
    Cedar.Spec.hasAttr v a es
  | .set xs _ => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    .ok (Set.make vs)
  | .record axs _ => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => bindAttr a₁ (evaluate x₁ req es))
    .ok (Map.make avs)
  | .call xfn xs _ => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    Cedar.Spec.call xfn vs
termination_by x
decreasing_by
  all_goals
    simp_wf
    try omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega
  case _ h =>
    simp at h
    omega
  case _ h =>
    have := List.sizeOf_lt_of_mem h
    omega

structure PartialRequest where
  principal : PartialEntityUID
  action : EntityUID                 -- Action is always known.
  resource : PartialEntityUID
  context :  Option (Map Attr Residual)          -- Unknown context is omitted.

structure PartialEntityData where
  attrs : Option (Map Attr Residual)              -- Attributes fully known or fully unknown.
  ancestors : Option (Set EntityUID) -- Ancestors fully known or fully unknown.
  tags : Option (Map Attr Residual)   -- Tags are fully known or fully unknown.

abbrev PartialEntities := Map EntityUID PartialEntityData

inductive Error where
  | evaluation (err : Spec.Error)
  | invalidPolicy (err : TypeError)
  | noValidEnvironment

instance : Coe Spec.Error Error where
  coe := Error.evaluation

def findMatchingEnv (schema : Schema) (req : PartialRequest) (es : PartialEntities) : Option Environment :=
  do
    let entry ← schema.acts.find? req.action
    let reqType ← (entry.toRequestTypes req.action).find? matchRequestType
    -- TODO: check validity of `es`
    pure ⟨ schema.ets, schema.acts, reqType ⟩
  where
    matchRequestType rt :=
      instanceOfEntityType rt.principal req.principal schema.ets.entityTypeMembers? &&
      instanceOfEntityType rt.resource req.resource schema.ets.entityTypeMembers?
      -- TODO: also check context
    instanceOfEntityType ty pe (eids: EntityType → Option (Set String)) :=
      ty == pe.ty && match (pe.id, eids ty) with
        | (.some id, .some eids) => eids.contains id
        | _ => true

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
    -- TODO reduction
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
