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

abbrev Record := (Map Attr Value)
abbrev PartialContext := Option Record

structure PartialEntityUID where
  ty : EntityType                    -- Entity type is always known,
  id : Option String                 -- but entity id may not be.

-- TODO: enumerated entities also play a role here
def PartialEntityUID.concretize (this : PartialEntityUID) (id : Option String) : Option EntityUID :=
  sorry

-- Copy-paste from the RFC
structure PartialRequest where
  principal : PartialEntityUID
  action : EntityUID                 -- Action is always known.
  resource : PartialEntityUID
  context :  PartialContext          -- Unknown context is omitted.

-- TODO: enumerated entities also play a role here
def PartialRequest.concretize (this : PartialRequest) (principal_id : Option String) (resource_id : Option String) (context : PartialContext) : Option Request :=
  sorry

structure PartialEntityData where
  attrs : Option Record              -- Attributes fully known or fully unknown.
  ancestors : Option (Set EntityUID) -- Ancestors fully known or fully unknown.
  tags : Option Record   -- Tags are fully known or fully unknown.

-- TODO: enumerated entities also play a role here
def PartialEntityData.concretize (this : PartialEntityData) (other : PartialEntityData) : Option EntityData :=
  sorry

abbrev PartialEntities := Map EntityUID PartialEntityData

-- TODO: enumerated entities also play a role here
def PartialEntities.concretize (this : PartialEntities) (other : PartialEntities) : Option Entities :=
  sorry

-- The result produced by TPE
-- We do not need `unknown`s because they can be represented by entity dereferences
-- Question: Does Residual need to be typed like `TypedExpr`
inductive Residual where
  | val (v : Value)  (ty : CedarType)
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

-- The interpreter of `Residual` that defines its semantics
def Residual.evaluate (x : Residual) (req : Request) (es: Entities) : Result Value :=
  sorry

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
      instanceOfEntityType rt.resource req.resource schema.ets.entityTypeMembers? &&
      instanceOfType rt.context req.context
    instanceOfEntityType ty pe (eids: EntityType → Option (Set String)) :=
      ty == pe.ty && match (pe.id, eids ty) with
        | (.some id, .some eids) => eids.contains id
        | _ => true
    instanceOfType ty pc :=
      match pc with
        | .some ctx => Cedar.Validation.instanceOfType ctx (.record ty) schema.ets
        | .none => true


def tpeExpr (x : TypedExpr)
    (req : PartialRequest)
    (es : PartialEntities)
    -- (h₀ : ∃ env, MatchesEnvironment req res env)
    -- (h₁ : x.isWellFormed, i.e., ⊢ x : x.ty )
    -- (h₁ : ∃ p, typeCheckPolicy p env = .ok x)
    : Except EvalError Residual :=
  match x with
  | .lit l ty => .ok $ .val l ty
  | .var .principal ty =>
    match req.principal.concretize none with
    | .some uid => .ok $ .val (.prim (.entityUID uid)) ty
    | .none => .ok $ .var .principal ty
  | .var .resource ty =>
    match req.resource.concretize none with
    | .some uid => .ok $ .val (.prim (.entityUID uid)) ty
    | .none => .ok $ .var .resource ty
  | .var .action ty => .ok $ .val (.prim (.entityUID req.action)) ty
  | .ite c t e ty => do
    let c ← tpeExpr c req es
    match c with
    | .val v ty₁ =>
      -- Question: can type error exist here? I doubt it
      -- a simple proof is based on that `tpeExpr req es` should produce the same value as `evaluate req' es'` ∀ req', res' => req.concretize = .ok req' ∧ es.concretize = .ok es', if the former does return a value
      let b ← v.asBool.mapError λ _ => EvalError.typeError
      if b then tpeExpr t req es else tpeExpr e req es
    | _ =>
      let t ← tpeExpr t req es
      let e ← tpeExpr e req es
      .ok $ .ite c t e ty
  | .and l r ty => do
    let l ← tpeExpr l req es
    match l with
    | .val v ty₁ =>
      let b ← v.asBool.mapError λ _ => EvalError.typeError
      if b then tpeExpr r req es else .ok $ .val (.prim (.bool b)) $ CedarType.bool .ff
    | _ =>
      let r ← tpeExpr r req es
      match r with
      | .val v ty₁ =>
        let b ← v.asBool.mapError λ _ => EvalError.typeError
        if b then .ok l else .ok $ .and l (.val (.prim (.bool b)) $ CedarType.bool .ff) ty
      | _ => .ok $ .and l r ty
  | _ => sorry

-- soundness theorem is something like
-- let .ok res = tpePolicy schema p req es
-- req' = req.concretize
-- es' = es.concretize
-- res.evaluate req' es' = evaluate p req' es'
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
