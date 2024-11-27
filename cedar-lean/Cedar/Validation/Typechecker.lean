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

import Cedar.Validation.Types
import Cedar.Validation.TypedExpr
import Cedar.Validation.Subtyping

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

inductive TypeError where
  | lubErr (ty₁ : CedarType) (ty₂ : CedarType)
  | unexpectedType (ty : CedarType)
  | attrNotFound (ty : CedarType) (attr : Attr)
  | tagNotFound (ety : EntityType) (tag : Expr)
  | unknownEntity (ety : EntityType)
  | extensionErr (xs : List Expr)
  | emptySetErr
  | incompatibleSetTypes (ty : List CedarType)
deriving Repr, DecidableEq

inductive Key where
  | attr (a : Attr)
  | tag (x : Expr)
deriving Repr, DecidableEq

abbrev Capabilities := List (Expr × Key)

def Capabilities.singleton (e : Expr) (k : Key) : Capabilities := [(e, k)]

abbrev ResultType := Except TypeError (TypedExpr × Capabilities)

def ResultType.typeOf : ResultType -> Except TypeError (CedarType × Capabilities)
  | .ok (ty, c) => .ok (ty.typeOf, c)
  | .error e      => .error e

def ok (ty : TypedExpr) (c : Capabilities := ∅) : ResultType := .ok (ty, c)
def err (e : TypeError) : ResultType := .error e

def typeOfLit (p : Prim) (env : Environment) : ResultType :=
  match p with
  | .bool true     => ok (.lit p $ .bool .tt)
  | .bool false    => ok (.lit p $ .bool .ff)
  | .int _         => ok (.lit p .int)
  | .string _      => ok (.lit p .string)
  | .entityUID uid =>
    if env.ets.contains uid.ty || env.acts.contains uid
    then ok (.lit p (.entity uid.ty))
    else err (.unknownEntity uid.ty)

def typeOfVar (v : Var) (env : Environment) : ResultType :=
  match v with
  | .principal => ok (.var v $ .entity env.reqty.principal)
  | .action    => ok (.var v $ .entity env.reqty.action.ty)
  | .resource  => ok (.var v $ .entity env.reqty.resource)
  | .context   => ok (.var v $ .record env.reqty.context)

def typeOfIf (r₁ : TypedExpr × Capabilities) (r₂ r₃ : ResultType) : ResultType :=
  let c₁ := r₁.snd
  match r₁.fst.typeOf with
  | .bool .tt => do
    let (ty₂, c₂) ← r₂
    ok ty₂ (c₁ ∪ c₂)
  | .bool .ff => r₃
  | .bool .anyBool => do
    let (ty₂, c₂) ← r₂
    let (ty₃, c₃) ← r₃
    match ty₂.typeOf ⊔ ty₃.typeOf with
    | .some ty => ok (.ite r₁.fst ty₂ ty₃ ty) ((c₁ ∪ c₂) ∩ c₃)
    | .none    => err (.lubErr ty₂.typeOf ty₃.typeOf)
  | ty₁ => err (.unexpectedType ty₁)

def typeOfAnd (r₁ : TypedExpr × Capabilities) (r₂ : ResultType) : ResultType :=
  let c₁ := r₁.snd
  match r₁.fst.typeOf with
  | .bool .ff  => ok r₁.fst
  | .bool ty₁  => do
    let (ty₂, c₂) ← r₂
    let mkₑ := TypedExpr.and r₁.fst ty₂
    match ty₂.typeOf with
    | .bool .ff     => ok (mkₑ (.bool .ff))
    | .bool .tt     => ok (mkₑ (.bool ty₁)) (c₁ ∪ c₂)
    | .bool _       => ok (mkₑ (.bool .anyBool)) (c₁ ∪ c₂)
    | _             => err (.unexpectedType ty₂.typeOf)
  | ty₁        => err (.unexpectedType ty₁)

def typeOfOr (r₁ : TypedExpr × Capabilities) (r₂ : ResultType) : ResultType :=
  let c₁ := r₁.snd
  match r₁.fst.typeOf with
  | .bool .tt  => ok r₁.fst
  | .bool .ff  => do
    let (ty₂, c₂) ← r₂
    let mkₑ := TypedExpr.or r₁.fst ty₂
    match ty₂.typeOf with
    | .bool _       => ok (mkₑ ty₂.typeOf) c₂
    | _             => err (.unexpectedType ty₂.typeOf)
  | .bool _    => do
    let (ty₂, c₂) ← r₂
    let mkₑ := TypedExpr.or r₁.fst ty₂
    match ty₂.typeOf with
    | .bool .tt     => ok (mkₑ (.bool .tt))
    | .bool .ff     => ok (mkₑ (.bool .anyBool)) c₁
    | .bool _       => ok (mkₑ (.bool .anyBool)) (c₁ ∩ c₂)
    | _             => err (.unexpectedType ty₂.typeOf)
  | ty₁        => err (.unexpectedType ty₁)

def typeOfUnaryApp (op : UnaryOp) (ty : TypedExpr) : ResultType :=
  let mkₑ := TypedExpr.unaryApp op ty
  match op, ty.typeOf with
  | .not, .bool x          => ok (mkₑ (.bool x.not))
  | .neg, .int             => ok (mkₑ .int)
  | .isEmpty, .set _       => ok (mkₑ (.bool .anyBool))
  | .like _, .string       => ok (mkₑ (.bool .anyBool))
  | .is ety₁, .entity ety₂ => ok (mkₑ (.bool (if ety₁ = ety₂ then .tt else .ff)))
  | _, _                   => err (.unexpectedType ty.typeOf)

def typeOfEq (ty₁ ty₂ : TypedExpr) (x₁ x₂ : Expr) : ResultType :=
  let mkₑ := TypedExpr.binaryApp .eq ty₁ ty₂
  match x₁, x₂ with
  | .lit p₁, .lit p₂ => if p₁ == p₂ then ok (mkₑ (.bool .tt)) else ok (mkₑ (.bool .ff))
  | _, _ =>
    match ty₁.typeOf ⊔ ty₂.typeOf with
    | .some _ => ok (mkₑ (.bool .anyBool))
    | .none   =>
    match ty₁.typeOf, ty₂.typeOf with
    | .entity _, .entity _ => ok (mkₑ (.bool .ff))
    | _, _                 => err (.lubErr ty₁.typeOf ty₂.typeOf)

def entityUID? : Expr → Option EntityUID
  | .lit (.entityUID uid) => .some uid
  | _                     => .none

def entityUIDs? : Expr → Option (List EntityUID)
  | .set xs => xs.mapM entityUID?
  | _       => .none

def actionUID? (x : Expr) (acts: ActionSchema) : Option EntityUID := do
  let uid ← entityUID? x
  if acts.contains uid then .some uid else .none

def actionType? (ety : EntityType) (acts: ActionSchema) : Bool :=
  acts.keys.any (EntityUID.ty · == ety)

-- x₁ in x₂ where x₁ has type ety₁ and x₂ has type ety₂
def typeOfInₑ (ety₁ ety₂ : EntityType) (x₁ x₂ : Expr) (env : Environment) : BoolType :=
  match actionUID? x₁ env.acts, entityUID? x₂ with
  | .some uid₁, .some uid₂ =>
    if env.acts.descendentOf uid₁ uid₂
    then .tt
    else .ff
  | _, _ =>
    if env.ets.descendentOf ety₁ ety₂
    then .anyBool
    else .ff

-- x₁ in x₂ where x₁ has type ety₁ and x₂ has type (.set ety₂)
def typeOfInₛ (ety₁ ety₂ : EntityType) (x₁ x₂ : Expr) (env : Environment) : BoolType :=
  match actionUID? x₁ env.acts, entityUIDs? x₂ with
  | .some uid₁, .some uids =>
    if uids.any (env.acts.descendentOf uid₁ ·)
    then .tt
    else .ff
  | _, _ =>
    if env.ets.descendentOf ety₁ ety₂
    then .anyBool
    else .ff

def typeOfHasTag (ety : EntityType) (x : Expr) (t : Expr) (c : Capabilities) (env : Environment) : Except TypeError (CedarType × Capabilities)  :=
  match env.ets.tags? ety with
  | .some .none     => .ok ((.bool .ff), ∅)
  | .some (.some _) =>
    if (x, .tag t) ∈ c
    then .ok ((.bool .tt), ∅)
    else .ok ((.bool .anyBool), (Capabilities.singleton x (.tag t)))
  | .none           =>
    if actionType? ety env.acts
    then .ok ((.bool .ff), ∅) -- action tags not allowed
    else .error (.unknownEntity ety)

def typeOfGetTag (ety : EntityType) (x : Expr) (t : Expr) (c : Capabilities) (env : Environment) : Except TypeError (CedarType × Capabilities) :=
  match env.ets.tags? ety with
  | .some .none      => .error (.tagNotFound ety t)
  | .some (.some ty) => if (x, .tag t) ∈ c then .ok (ty, ∅) else .error (.tagNotFound ety t)
  | .none            => .error (.unknownEntity ety)

def ifLubThenBool (ty₁ ty₂ : CedarType) : Except TypeError (CedarType × Capabilities) :=
  match ty₁ ⊔ ty₂ with
  | some _ => .ok ((.bool .anyBool), ∅)
  | none   => .error (.lubErr ty₁ ty₂)

def typeOfBinaryApp (op₂ : BinaryOp) (ty₁ ty₂ : TypedExpr) (x₁ x₂ : Expr) (c : Capabilities) (env : Environment) : ResultType :=
  let mkₑ := TypedExpr.binaryApp op₂ ty₁ ty₂
  match op₂, ty₁.typeOf, ty₂.typeOf with
  | .eq, _, _                               => typeOfEq ty₁ ty₂ x₁ x₂
  | .mem, .entity ety₁, .entity ety₂        => ok (mkₑ (.bool (typeOfInₑ ety₁ ety₂ x₁ x₂ env)))
  | .mem, .entity ety₁, .set (.entity ety₂) => ok (mkₑ (.bool (typeOfInₛ ety₁ ety₂ x₁ x₂ env)))
  | .hasTag, .entity ety₁, .string          => do
    let (ty, c) ← typeOfHasTag ety₁ x₁ x₂ c env
    ok (mkₑ ty) c
  | .getTag, .entity ety₁, .string          => do
    let (ty, c) ← typeOfGetTag ety₁ x₁ x₂ c env
    ok (mkₑ ty) c
  | .less,   .int, .int                     => ok (mkₑ (.bool .anyBool))
  | .lessEq, .int, .int                     => ok (mkₑ (.bool .anyBool))
  | .add,    .int, .int                     => ok (mkₑ .int)
  | .sub,    .int, .int                     => ok (mkₑ .int)
  | .mul,    .int, .int                     => ok (mkₑ .int)
  | .contains, .set ty₃, _                  => do
    let (ty, c) <- ifLubThenBool ty₂.typeOf ty₃
    ok (mkₑ ty) c
  | .containsAll, .set ty₃, .set ty₄        => do
    let (ty, c) <- ifLubThenBool ty₃ ty₄
    ok (mkₑ ty) c
  | .containsAny, .set ty₃, .set ty₄        => do
    let (ty, c) <- ifLubThenBool ty₃ ty₄
    ok (mkₑ ty) c
  | _, _, _                                 => err (.unexpectedType ty₁.typeOf)

def hasAttrInRecord (rty : RecordType) (x : Expr) (a : Attr) (c : Capabilities) (knownToExist : Bool) : Except TypeError (CedarType × Capabilities) :=
  match rty.find? a with
  | .some qty =>
    if (x, .attr a) ∈ c || (qty.isRequired && knownToExist)
    then .ok ((.bool .tt), ∅)
    else .ok ((.bool .anyBool), (Capabilities.singleton x (.attr a)))
  | .none     => .ok ((.bool .ff), ∅)

def typeOfHasAttr (ty : TypedExpr) (x : Expr) (a : Attr) (c : Capabilities) (env : Environment) : ResultType :=
  let mkₑ := TypedExpr.hasAttr ty a
  match ty.typeOf with
  | .record rty => do
    let (ty', c) ← hasAttrInRecord rty x a c true
    ok (mkₑ ty') c
  | .entity ety =>
    match env.ets.attrs? ety with
    | .some rty => do
      let (ty', c) ← hasAttrInRecord rty x a c false
      ok (mkₑ ty') c
    | .none     =>
      if actionType? ety env.acts
      then ok (mkₑ (.bool .ff)) -- action attributes not allowed
      else err (.unknownEntity ety)
  | _           => err (.unexpectedType ty.typeOf)

def getAttrInRecord (ty : TypedExpr) (rty : RecordType) (x : Expr) (a : Attr) (c : Capabilities) : Except TypeError (CedarType × Capabilities)  :=
  match rty.find? a with
  | .some (.required aty) => .ok (aty, ∅)
  | .some (.optional aty) => if (x, .attr a) ∈ c then .ok (aty, ∅) else .error (.attrNotFound ty.typeOf a)
  | .none                 => .error (.attrNotFound ty.typeOf a)

def typeOfGetAttr (ty : TypedExpr) (x : Expr) (a : Attr) (c : Capabilities) (env : Environment) : ResultType :=
  let mkₑ := TypedExpr.getAttr ty a
  match ty.typeOf with
  | .record rty => do
    let (ty', c) ← getAttrInRecord ty rty x a c
    ok (mkₑ ty') c
  | .entity ety =>
    match env.ets.attrs? ety with
    | .some rty => do
      let (ty', c) ← getAttrInRecord ty rty x a c
      ok (mkₑ ty') c
    | .none     => err (.unknownEntity ety)
  | _           => err (.unexpectedType ty.typeOf)

def typeOfSet (tys : List TypedExpr) : ResultType :=
  match tys.map (λ ty => ty.typeOf) with
  | []       => err .emptySetErr
  | hd :: tl =>
    match tl.foldlM lub? hd with
    | .some ty => ok (.set tys (.set ty))
    | .none    => err (.incompatibleSetTypes (hd :: tl))

def justType (r : ResultType) : Except TypeError TypedExpr :=
  r.map Prod.fst

def typeOfConstructor (mk : String → Option α) (xs : List Expr) (ty : CedarType) : Except TypeError (CedarType × Capabilities) :=
  match xs with
  | [.lit (.string s)] =>
    match (mk s) with
    | .some _ => .ok (ty, ∅)
    | .none   => .error (.extensionErr xs)
  | _ => .error (.extensionErr xs)

def typeOfCall (xfn : ExtFun) (tys : List TypedExpr) (xs : List Expr) : ResultType :=
  let mkₑ := TypedExpr.call xfn tys
  match xfn, tys.map TypedExpr.typeOf with
  | .decimal, _  => do
    let (ty, c) ← typeOfConstructor Cedar.Spec.Ext.Decimal.decimal xs (.ext .decimal)
    ok (mkₑ ty) c
  | .ip, _       => do
    let (ty, c) ← typeOfConstructor Cedar.Spec.Ext.IPAddr.ip xs (.ext .ipAddr)
    ok (mkₑ ty) c
  | .lessThan, [.ext .decimal, .ext .decimal]           => ok (mkₑ (.bool .anyBool))
  | .lessThanOrEqual, [.ext .decimal, .ext .decimal]    => ok (mkₑ (.bool .anyBool))
  | .greaterThan, [.ext .decimal, .ext .decimal]        => ok (mkₑ (.bool .anyBool))
  | .greaterThanOrEqual, [.ext .decimal, .ext .decimal] => ok (mkₑ (.bool .anyBool))
  | .isIpv4, [.ext .ipAddr]                             => ok (mkₑ (.bool .anyBool))
  | .isIpv6, [.ext .ipAddr]                             => ok (mkₑ (.bool .anyBool))
  | .isLoopback, [.ext .ipAddr]                         => ok (mkₑ (.bool .anyBool))
  | .isMulticast, [.ext .ipAddr]                        => ok (mkₑ (.bool .anyBool))
  | .isInRange, [.ext .ipAddr, .ext .ipAddr]            => ok (mkₑ (.bool .anyBool))
  | _, _         => err (.extensionErr xs)


-- Note: if x types as .tt or .ff, it is okay to replace x with the literal
-- expression true or false if x can never throw an extension error at runtime.
-- This is true for the current version of Cedar.
def typeOf (x : Expr) (c : Capabilities) (env : Environment) : ResultType :=
  match x with
  | .lit p => typeOfLit p env
  | .var v => typeOfVar v env
  | .ite x₁ x₂ x₃ => do
    let (ty₁, c₁) ← typeOf x₁ c env
    typeOfIf (ty₁, c₁) (typeOf x₂ (c ∪ c₁) env) (typeOf x₃ c env)
  | .and x₁ x₂ => do
    let (ty₁, c₁) ← typeOf x₁ c env
    typeOfAnd (ty₁, c₁) (typeOf x₂ (c ∪ c₁) env)
  | .or x₁ x₂ => do
    let (ty₁, c₁) ← typeOf x₁ c env
    typeOfOr (ty₁, c₁) (typeOf x₂ c env)
  | .unaryApp op₁ x₁ => do
    let (ty₁, _) ← typeOf x₁ c env
    typeOfUnaryApp op₁ ty₁
  | .binaryApp op₂ x₁ x₂ => do
    let (ty₁, _) ← typeOf x₁ c env
    let (ty₂, _) ← typeOf x₂ c env
    typeOfBinaryApp op₂ ty₁ ty₂ x₁ x₂ c env
  | .hasAttr x₁ a => do
    let (ty₁, _) ← typeOf x₁ c env
    typeOfHasAttr ty₁ x₁ a c env
  | .getAttr x₁ a => do
    let (ty₁, _) ← typeOf x₁ c env
    typeOfGetAttr ty₁ x₁ a c env
  | .set xs => do
    let tys ← xs.mapM₁ (λ ⟨x₁, _⟩ => justType (typeOf x₁ c env))
    typeOfSet tys
  | .record axs => do
    let atys ← axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => (typeOf x₁ c env).map (λ (ty, _) => (a₁, ty)))
    ok (.record atys (.record (Map.make (atys.map (λ (a, ty) => (a, .required ty.typeOf))))))
  | .call xfn xs => do
    let tys ← xs.mapM₁ (λ ⟨x₁, _⟩ => justType (typeOf x₁ c env))
    typeOfCall xfn tys xs

---- Derivations -----

deriving instance Repr for RequestType
deriving instance Repr for Environment

end Cedar.Validation
