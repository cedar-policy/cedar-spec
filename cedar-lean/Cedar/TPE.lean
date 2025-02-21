import Cedar.Spec.Value
import Cedar.Spec.Expr
import Cedar.Spec.Request
import Cedar.Validation.TypedExpr
import Cedar.Validation.Validator
import Cedar.Validation.Typechecker
import Cedar.Validation.RequestEntityValidator

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
  sorry

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

def tpeExpr (x : TypedExpr)
    (req : PartialRequest)
    (es : PartialEntities)
    : Except EvalError Residual :=
  match x with
  | .lit p ty => .ok $ .prim p ty
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
