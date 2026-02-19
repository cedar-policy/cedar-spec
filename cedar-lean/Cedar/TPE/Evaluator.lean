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

def PartialValue.asResidual (pv : PartialValue) (ty : CedarType) : Residual := .val pv ty

-- Invariant `pv.instanceOfType tgt.typeOf` for relevant type env
-- It might be better to represent `tgt` with some more restricted structure.
-- Something like
-- inductive AccessPath where
--  | context
--  | entityUID (uid : EntityUID)
--  | getAttr (p : AccessPath) (a : Attr)
--  | getTag (p : AccessPath) (t : Tag)
-- partial def PartialValue.asResidual (pv : PartialValue) (tgt : Residual) : Residual :=
--   match pv with
--   | prim p => .val p tgt.typeOf
--   | set s => .val s tgt.typeOf
--   | ext x => .val x tgt.typeOf
--   | record as => .record (as.kvs.map₁ λ kv => (kv.val.1,
--     match kv.val.2 with
--     | .present v =>
--       -- Using `.bool .anyBool` as a junk value. Case should be impossible for well-typed policies and requests
--       let aty := match tgt.typeOf with
--         | .record rty => rty.find? kv.val.fst|>.map Qualified.getType|>.getD (.bool .anyBool)
--         | _ => (.bool .anyBool)
--       .present (v.asResidual (.getAttr tgt kv.val.fst aty))
--     | .unknown ty => .unknown ty tgt)) tgt.typeOf
-- termination_by pv
-- decreasing_by sorry

/- Convert an optional value to a residual: Return `.error ty` when it's none -/
def someOrError : Option Value → CedarType → Residual
  | .some v, ty => .val v.asPartialValue ty
  | .none,   ty => .error ty

/- Convert an optional value to a residual: Return `self` when it's none -/
def someOrSelf : Option Value → CedarType → Residual → Residual
  | .some v, ty, _   => .val v.asPartialValue ty
  | .none,   _, self => self

def varₚ (req : PartialRequest) (var : Var) (ty : CedarType) : Residual :=
  match var with
  | .principal => varₒ req.principal.asEntityUID
  | .resource  => varₒ req.resource.asEntityUID
  | .action    => varₒ req.action
  | .context   => req.context >>= (PartialValue.record · |>.asResidual ty)|>.getD (.var .context ty)
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

def apply₁ (op₁ : UnaryOp) (r : Residual) (ty : CedarType) : Residual :=
  match r.asPartialValue with
  | .some v =>
    match op₁, v with
    | .not, .prim (.bool b) =>
      .val (!b) ty
    | .neg, .prim (.int i) =>
      someOrError (i.neg?) ty
    | .isEmpty, .set s =>
      .val s.isEmpty ty
    | .like p, .prim (.string s) =>
      .val (wildcardMatch s p) ty
    | .is ety, .prim (.entityUID uid) =>
      .val (ety == uid.ty) ty
    | _, _ => .error ty
  | .none =>
    match r with
    | .error _ => .error ty
    | _ => .unaryApp op₁ r ty

def inₑ (uid₁ uid₂ : EntityUID) (es : PartialEntities) : Option Bool :=
  if uid₁ = uid₂ then .some true else (es.ancestors uid₁).map (Set.contains · uid₂)

def inₛ (uid : EntityUID) (vs : Set Value) (es : PartialEntities): Option Bool := do
  (← vs.toList.mapM (Except.toOption ∘ Value.asEntityUID)).anyM (inₑ uid · es)

def hasTag (uid : EntityUID) (tag : String) (es : PartialEntities) : Option Bool :=
  (es.tags uid).map (Map.contains · tag)

def getTag (uid : EntityUID) (tag : String) (es : PartialEntities) (ty : CedarType) : Residual :=
  match es.tags uid with
  | .some tags =>
    match tags.find? tag with
    | .some (.present tv) => tv.asResidual ty
    | .some _ => .binaryApp .getTag uid tag ty
    | .none => .error ty
  | .none => .binaryApp .getTag uid tag ty

-- def eq (pv₁ pv₂ : PartialValue) (ty : CedarType) : Residual :=
--   match pv₁, pv₂ with
--   | .record _, .record _ => .binaryApp .eq (.val pv₁) (.val pv₂) ty
--   | _, _ => pv₁ == pv₂

def apply₂ (op₂ : BinaryOp) (r₁ r₂ : Residual) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r₁.asPartialValue, r₂.asPartialValue with
  | .some v₁, .some v₂ =>
    match op₂, v₁, v₂ with
    -- TODO: can be more precise, but may have to leave residual
    | .eq, (.record _), (.record _) => self
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
    -- TODO: can be more precise, but may have to leave residual
    | .contains, .set _, (.record _) => self
    | .contains, .set vs₁, _ =>
      .val (vs₁.contains (v₂.asValue.getD false)) ty
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
  | _, _ =>
    match r₁, r₂ with
    | .error _, _ | _, .error _ => .error ty
    | _, _ => self
  where
  self := .binaryApp op₂ r₁ r₂ ty

def hasAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | .val (.record m) _ => m.find? a|>.isSome
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some m =>
      match m.find? a with
      | .none => false
      | .some (.present _) => true
      | .some (.unknown _ _) => .hasAttr r a ty
    | .none   => .hasAttr r a ty
  | _ => .hasAttr r a ty

def getAttr (r : Residual) (a : Attr) (es : PartialEntities) (ty : CedarType) : Residual :=
  match r with
  | .error _ => .error ty
  | .val (.record m) _ =>
    match m.find? a with
    | .none => .error ty
    | .some (.present pv) => pv.asResidual ty
    | .some (.unknown p ty) => .access p ty
  | .val (.prim (.entityUID uid)) _ =>
    match es.attrs uid with
    | .some m =>
      match m.find? a with
      | .none => .error ty
      | .some (.present pv) => pv.asResidual ty
      | .some (.unknown p ty) => .access p ty
    | .none   => .getAttr r a ty
  | _ => .getAttr r a ty

def set (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some xs => .val (.set (Set.make xs)) ty
  | .none    => if rs.any Residual.isError then .error ty else .set rs ty

def record (m : List (Attr × Residual)) (ty : CedarType) : Residual :=
  match m.mapM λ (a, r₁) => bindAttr a (PartialAttribute.present <$> r₁.asPartialValue) with
  | .some xs => .val (.record (Map.make xs)) ty
  | .none    => if m.any λ (_, r₁) => r₁.isError then .error ty else .record m ty

def call (xfn : ExtFun) (rs : List Residual) (ty : CedarType) : Residual :=
  match rs.mapM Residual.asValue with
  | .some xs => someOrError (Spec.call xfn xs).toOption ty
  | .none    => if rs.any Residual.isError then .error ty else .call xfn rs ty

def evaluate_path (p : AccessPath)
  (req : PartialRequest)
  (es : PartialEntities) : Option PartialValue :=
  match p with
  | .context =>
    match req.context with
    | .some context => .some (.record context)
    | .none => none
  | .entityUID uid => .some uid
  | .getAttr p a  => do
    let v ← evaluate_path p req es
    match v with
    | .record m =>
      match m.find? a with
      | .none => .none
      | .some (.present pv) => .some pv
      | .some (.unknown _ _) => .none
    | .prim (.entityUID uid) =>
      match es.attrs uid with
      | .some m =>
        match m.find? a with
        | .none => .none
        | .some (.present pv) => .some pv
        | .some (.unknown _ _) => .none
      | .none   => .none
    | _ => .none
  | .getTag p t => .none -- TODO

def evaluate
  (x : Residual)
  (req : PartialRequest)
  (es : PartialEntities) : Residual :=
  match x with
  | .access p ty =>
    match evaluate_path p req es with
    | .some pv => .val pv ty
    | .none => .access p ty
  | .val l ty => .val l ty
  | .var v ty => varₚ req v ty
  | .error ty => .error ty
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
    record (axs.map₁ (λ ⟨(a, x₁), _⟩ => (a, evaluate x₁ req es))) ty
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
  match schema.environment? req.principal.ty req.resource.ty req.action with
    | .some env =>
      if requestAndEntitiesIsValid env req es
      then
        do
          let expr := substituteAction env.reqty.action p.toExpr
          let (te, _) ← (typeOf expr ∅ env).mapError Error.invalidPolicy
          .ok (evaluate te.liftBoolTypes.toResidual req es)
      else .error .invalidRequestOrEntities
    | .none => .error .invalidEnvironment

-- Basic tests
private def emptyReq : PartialRequest := ⟨⟨default, none⟩, default, ⟨default, none⟩, none⟩
private def emptyEs : PartialEntities := default

#guard evaluate (.val true (.bool .anyBool)) emptyReq emptyEs == .val true (.bool .anyBool)
#guard evaluate (.binaryApp .eq (.val (.prim (.int 1)) .int) (.val (.prim (.int 1)) .int) (.bool .anyBool)) emptyReq emptyEs = .val true (.bool .anyBool)

-- Attribute access on unknown entity
private def ety : EntityType := ⟨"User", []⟩
#guard evaluate (.hasAttr (.var .principal (.entity ety)) "role" (.bool .anyBool)) emptyReq emptyEs = .hasAttr (.var .principal (.entity ety)) "role" (.bool .anyBool)
#guard evaluate (.getAttr (.var .principal (.entity ety)) "role" .string) emptyReq emptyEs = .getAttr (.var .principal (.entity ety)) "role" .string
#guard evaluate (.getAttr (.var .resource (.entity ety)) "owner" (.entity ety)) emptyReq emptyEs = .getAttr (.var .resource (.entity ety)) "owner" (.entity ety)

-- Partially known entity data
private def uid : EntityUID := ⟨ety, "alice"⟩
private def partialEs : PartialEntities := Map.make [(uid, ⟨
  some (Map.make [
    ("name", PartialAttribute.present (PartialValue.prim (.string "Alice"))),
    ("role", PartialAttribute.unknown (.getAttr (.entityUID uid) "role") .string)
  ]),
  none,
  none
⟩)]

#guard evaluate (.hasAttr (.val (.prim (.entityUID uid)) (.entity ety)) "name" (.bool .anyBool)) emptyReq partialEs = .val true (.bool .anyBool)
#guard evaluate (.getAttr (.val (.prim (.entityUID uid)) (.entity ety)) "name" .string) emptyReq partialEs = .val (.prim (.string "Alice")) .string
#guard evaluate (.hasAttr (.val (.prim (.entityUID uid)) (.entity ety)) "role" (.bool .anyBool)) emptyReq partialEs = .hasAttr (.val (.prim (.entityUID uid)) (.entity ety)) "role" (.bool .anyBool)
#eval evaluate (.getAttr (.val (.prim (.entityUID uid)) (.entity ety)) "role" .string) emptyReq partialEs --= .getAttr (.val (.prim (.entityUID uid)) (.entity ety)) "role" .string
#guard evaluate (.hasAttr (.val (.prim (.entityUID uid)) (.entity ety)) "missing" (.bool .anyBool)) emptyReq partialEs = .val false (.bool .anyBool)

-- Nested unknown attribute access
private def uid2 : EntityUID := ⟨ety, "bob"⟩
private def partialEs2 : PartialEntities := Map.make [(uid2, ⟨
  some (Map.make [("manager", PartialAttribute.unknown (.getAttr (.entityUID uid2) "manager") (.entity ety))]),
  none,
  none
⟩)]

#eval evaluate (.getAttr (.val (.prim (.entityUID uid2)) (.entity ety)) "manager" (.entity ety)) emptyReq partialEs2 -- = .getAttr (.val (.prim (.entityUID uid2)) (.entity ety)) "manager" (.entity ety)
#eval evaluate (.getAttr (.getAttr (.val (.prim (.entityUID uid2)) (.entity ety)) "manager" (.entity ety)) "name" .string) emptyReq partialEs2 -- = .getAttr (.getAttr (.val (.prim (.entityUID uid2)) (.entity ety)) "manager" (.entity ety)) "name" .string

-- Present record with mixed known/unknown attributes
private def uid3 : EntityUID := ⟨ety, "charlie"⟩
private def partialEs3 : PartialEntities := Map.make [(uid3, ⟨
  some (Map.make [("profile", PartialAttribute.present (PartialValue.record (Map.make [
    ("email", PartialAttribute.present (PartialValue.prim (.string "charlie@example.com"))),
    ("age", PartialAttribute.unknown (.getAttr (.getAttr (.entityUID uid3) "profile") "age") .int)
  ])))]),
  none,
  none
⟩)]

private def recTy : CedarType := .record (Map.make [("email", .required .string), ("age", .required .int)])
private def getProfile := evaluate (.getAttr (.val (.prim (.entityUID uid3)) (.entity ety)) "profile" recTy) emptyReq partialEs3
#eval (evaluate (.getAttr getProfile "email" .string) emptyReq partialEs3)
#eval (evaluate (.getAttr getProfile "age" .int) emptyReq partialEs3)

end Cedar.TPE
