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
  | prim (p : Prim) (ty : CedarType)
  | ext (e : Ext) (ty : CedarType)
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

partial def Residual.asWellFormedInput (r : Residual) (env : Environment) : Bool :=
  match r with
  | .prim (.bool _) (.bool .anyBool) => true
  | .prim (.int _) .int => true
  | .prim (.string _) .string => true
  | .prim (.entityUID uid) (.entity ety) => instanceOfEntityType uid ety env.ets.entityTypeMembers?
  | .ext (.ipaddr _) (.ext .ipAddr) => true
  | .ext (.decimal _) (.ext .decimal) => true
  | .set s (.set ty) => s.all λ x ↦ x.asWellFormedInput env
  | .record m (.record rty) => m.all λ (a, x) ↦ x.asWellFormedInput env
  | _ => false

-- The interpreter of `Residual` that defines its semantics
def Residual.evaluate (x : Residual) (req : Request) (es: Entities) : Result Value :=
  match x with
  | .prim p _ => .ok $ .prim p
  | .ext e _ => .ok $ .ext e
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
  context :  Option (Map Attr TypedResidual)          -- Unknown context is omitted.

structure PartialEntityData where
  attrs : Option (Map Attr TypedResidual)              -- Attributes fully known or fully unknown.
  ancestors : Option (Set EntityUID) -- Ancestors fully known or fully unknown.
  tags : Option (Map Attr TypedResidual)   -- Tags are fully known or fully unknown.

abbrev PartialEntities := Map EntityUID PartialEntityData

-- These are possible errors after validation and
-- hence should be the possible errors thrown by TPE
inductive EvalError where
  | typeError
  | entityDoesNotExist
  | arithBoundsError
  | extensionError

inductive Error where
  | evaluation (err : EvalError)
  | invalidPolicy (err : TypeError)
  | noValidEnvironment

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

def tpeExpr (x : Residual)
    (req : PartialRequest)
    (es : PartialEntities)
    : Except EvalError Residual :=
  match x with
  | .prim _ _ => .ok x
  | .var .principal ty =>
    match req.principal.asEntityUID with
    | .some uid => .ok $ .prim (.entityUID uid) ty
    | .none => .ok $ .var .principal ty
  | .var .resource ty =>
    match req.resource.asEntityUID with
    | .some uid => .ok $ .prim (.entityUID uid) ty
    | .none => .ok $ .var .resource ty
  | .var .action ty => .ok $ .prim (.entityUID req.action) ty
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
  | _ => sorry

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
