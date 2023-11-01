/-
 Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.

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
import Cedar.Validation.Subtyping

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

abbrev Capabilities := List (Expr × Attr)

def Capabilities.singleton (e : Expr) (a : Attr) : Capabilities := [(e, a)]

abbrev ResultType := Except TypeError (CedarType × Capabilities)

def ok (ty : CedarType) (c : Capabilities := ∅) : ResultType := .ok (ty, c)
def err (e : TypeError) : ResultType := .error e

structure RequestType where
  principal : EntityType
  action : EntityUID
  resource : EntityType
  context : RecordType

structure Environment where
  ets : EntityTypeStore
  acts : ActionStore
  reqty : RequestType

def typeOfLit (p : Prim) (env : Environment) : ResultType :=
  match p with
  | .bool true     => ok (.bool .tt)
  | .bool false    => ok (.bool .ff)
  | .int _         => ok .int
  | .string _      => ok .string
  | .entityUID uid =>
    if env.ets.contains uid.ty || env.acts.contains uid
    then ok (.entity uid.ty)
    else err (.unknownEntity uid.ty)

def typeOfVar (v : Var) (env : Environment) : ResultType :=
  match v with
  | .principal => ok (.entity env.reqty.principal)
  | .action    => ok (.entity env.reqty.action.ty)
  | .resource  => ok (.entity env.reqty.resource)
  | .context   => ok (.record env.reqty.context)

def typeOfIf (r₁ : CedarType × Capabilities) (r₂ r₃ : ResultType) : ResultType :=
  match r₁ with
  | (.bool .tt, c₁) => do
    let (ty₂, c₂) ← r₂
    ok ty₂ (c₁.union c₂)
  | (.bool .ff, _) => r₃
  | (.bool .anyBool, c₁) => do
    let (ty₂, c₂) ← r₂
    let (ty₃, c₃) ← r₃
    match ty₂ ⊔ ty₃ with
    | .some ty => ok ty ((c₁ ∪ c₂) ∩ c₃)
    | .none    => err (.lubErr ty₂ ty₃)
  | (ty₁, _) => err (.unexpectedType ty₁)

def typeOfAnd (r₁ : CedarType × Capabilities) (r₂ : ResultType) : ResultType :=
  match r₁ with
  | (.bool .ff, _)  => ok (.bool .ff)
  | (.bool ty₁, c₁) => do
    let (ty₂, c₂) ← r₂
    match ty₂ with
    | .bool .ff     => ok (.bool .ff)
    | .bool .tt     => ok (.bool ty₁) (c₁ ∪ c₂)
    | .bool _       => ok (.bool .anyBool) (c₁ ∪ c₂)
    | _             => err (.unexpectedType ty₂)
  | (ty₁, _)        => err (.unexpectedType ty₁)

def typeOfOr (r₁ : CedarType × Capabilities) (r₂ : ResultType) : ResultType :=
  match r₁ with
  | (.bool .tt, _)  => ok (.bool .tt)
  | (.bool .ff, _)  => r₂
  | (.bool ty₁, c₁) => do
    let (ty₂, c₂) ← r₂
    match ty₂ with
    | .bool .tt     => ok (.bool .tt)
    | .bool .ff     => ok (.bool ty₁) c₁
    | .bool _       => ok (.bool .anyBool) (c₁ ∩ c₂)
    | _             => err (.unexpectedType ty₂)
  | (ty₁, _)        => err (.unexpectedType ty₁)

def typeOfUnaryApp (op : UnaryOp) (ty : CedarType) : ResultType :=
  match op, ty with
  | .not, .bool x          => ok (.bool x.not)
  | .neg, .int             => ok .int
  | .mulBy _, .int         => ok .int
  | .like _, .string       => ok (.bool .anyBool)
  | .is ety₁, .entity ety₂ => ok (.bool (if ety₁ = ety₂ then .tt else .ff))
  | _, _                   => err (.unexpectedType ty)

def typeOfEq (ty₁ ty₂ : CedarType) (x₁ x₂ : Expr) : ResultType :=
  match x₁, x₂ with
  | .lit p₁, .lit p₂ => if p₁ == p₂ then ok (.bool .tt) else ok (.bool .ff)
  | _, _ =>
    match ty₁ ⊔ ty₂ with
    | .some _ => ok (.bool .anyBool)
    | .none   =>
    if ty₁.isPrimType || ty₂.isPrimType
    then ok (.bool .ff)
    else err (.lubErr ty₁ ty₂)

def entityUID? : Expr → Option EntityUID
  | .lit (.entityUID uid) => .some uid
  | _                     => .none

def entityUIDs? : Expr → Option (List EntityUID)
  | .set xs => xs.mapM entityUID?
  | _       => .none

def isAction (uid : EntityUID) (acts: ActionStore) : Bool :=
  acts.contains uid

def actionUID? (x : Expr) (acts: ActionStore) : Option EntityUID := do
  let uid ← entityUID? x
  if isAction uid acts then .some uid else .none

-- x₁ in x₂ where x₁ has type ety₁ and x₂ has type ety₂
def typeOfInₑ (ety₁ ety₂ : EntityType) (x₁ x₂ : Expr) (env : Environment) : ResultType :=
  match actionUID? x₁ env.acts, entityUID? x₂ with
  | .some uid₁, .some uid₂ =>
    if env.acts.descendentOf uid₁ uid₂
    then ok (.bool .tt)
    else ok (.bool .ff)
  | _, _ =>
    if env.ets.descendentOf ety₁ ety₂
    then ok (.bool .anyBool)
    else ok (.bool .ff)

-- x₁ in x₂ where x₁ has type ety₁ and x₂ has type (.set ety₂)
def typeOfInₛ (ety₁ ety₂ : EntityType) (x₁ x₂ : Expr) (env : Environment) : ResultType :=
  match actionUID? x₁ env.acts, entityUIDs? x₂ with
  | .some uid₁, .some uids =>
    if uids.any (env.acts.descendentOf uid₁ ·)
    then ok (.bool .tt)
    else ok (.bool .ff)
  | _, _ =>
    if env.ets.descendentOf ety₁ ety₂
    then ok (.bool .anyBool)
    else ok (.bool .ff)

def ifLubThenBool (ty₁ ty₂ : CedarType) : ResultType :=
  match ty₁ ⊔ ty₂ with
  | some _ => ok (.bool .anyBool)
  | none   => err (.lubErr ty₁ ty₂)

def typeOfBinaryApp (op₂ : BinaryOp) (ty₁ ty₂ : CedarType) (x₁ x₂ : Expr) (env : Environment) : ResultType :=
  match op₂, ty₁, ty₂ with
  | .eq, _, _                               => typeOfEq ty₁ ty₂ x₁ x₂
  | .mem, .entity ety₁, .entity ety₂        => typeOfInₑ ety₁ ety₂ x₁ x₂ env
  | .mem, .entity ety₁, .set (.entity ety₂) => typeOfInₛ ety₁ ety₂ x₁ x₂ env
  | .less,   .int, .int                     => ok (.bool .anyBool)
  | .lessEq, .int, .int                     => ok (.bool .anyBool)
  | .add,    .int, .int                     => ok .int
  | .sub,    .int, .int                     => ok .int
  | .contains, .set ty₃, _                  => ifLubThenBool ty₂ ty₃
  | .containsAll, .set ty₃, .set ty₄        => ifLubThenBool ty₃ ty₄
  | .containsAny, .set ty₃, .set ty₄        => ifLubThenBool ty₃ ty₄
  | _, _, _                                 => err (.unexpectedType ty₁)

def hasAttrInRecord (rty : RecordType) (x : Expr) (a : Attr) (c : Capabilities) : ResultType :=
  match rty.find? a with
  | .some (.required _) => ok (.bool .tt)
  | .some (.optional _) =>
    if (x, a) ∈ c
    then ok (.bool .tt)
    else ok (.bool .anyBool) (Capabilities.singleton x a)
  | .none               => ok (.bool .ff)

def typeOfHasAttr (ty : CedarType) (x : Expr) (a : Attr) (c : Capabilities) (env : Environment) : ResultType :=
  match ty with
  | .record rty => hasAttrInRecord rty x a c
  | .entity ety =>
    match env.ets.attrs? ety with
    | .some rty => hasAttrInRecord rty x a c
    | .none     => err (.unknownEntity ety)
  | _           => err (.unexpectedType ty)

def getAttrInRecord (ty : CedarType) (rty : RecordType) (x : Expr) (a : Attr) (c : Capabilities) : ResultType :=
  match rty.find? a with
  | .some (.required aty) => ok aty
  | .some (.optional aty) => if (x, a) ∈ c then ok aty else err (.attrNotFound ty a)
  | .none                 => err (.attrNotFound ty a)

def typeOfGetAttr (ty : CedarType) (x : Expr) (a : Attr) (c : Capabilities) (env : Environment) : ResultType :=
  match ty with
  | .record rty => getAttrInRecord ty rty x a c
  | .entity ety =>
    match env.ets.attrs? ety with
    | .some rty => getAttrInRecord ty rty x a c
    | .none     => err (.unknownEntity ety)
  | _           => err (.unexpectedType ty)

def typeOfSet (tys : List CedarType) : ResultType :=
  match tys with
  | []       => err .emptySetErr
  | hd :: tl =>
    match tl.foldrM lub? hd with
    | .some ty => ok (.set ty)
    | .none    => err (.incompatibleSetTypes tys)

def justType (r : ResultType) : Except TypeError CedarType :=
  r.map Prod.fst

def requiredAttr (a : Attr) (r : ResultType) : Except TypeError (Attr × QualifiedType) :=
  r.map λ (ty, _) => (a, .required ty)

def typeOfConstructor (mk : String → Option α) (xs : List Expr) (ty : CedarType) : ResultType :=
  match xs with
  | [.lit (.string s)] =>
    match (mk s) with
    | .some _ => ok ty
    | .none   => err (.extensionErr xs)
  | _ => err (.extensionErr xs)

def typeOfCall (xfn : ExtFun) (tys : List CedarType) (xs : List Expr) : ResultType :=
  match xfn, tys with
  | .decimal, _  => typeOfConstructor Cedar.Spec.Ext.Decimal.decimal xs (.ext .decimal)
  | .ip, _       => typeOfConstructor Cedar.Spec.Ext.IPAddr.ip xs (.ext .ipAddr)
  | .lessThan, [.ext .decimal, .ext .decimal]           => ok (.bool .anyBool)
  | .lessThanOrEqual, [.ext .decimal, .ext .decimal]    => ok (.bool .anyBool)
  | .greaterThan, [.ext .decimal, .ext .decimal]        => ok (.bool .anyBool)
  | .greaterThanOrEqual, [.ext .decimal, .ext .decimal] => ok (.bool .anyBool)
  | .isIpv4, [.ext .ipAddr]                             => ok (.bool .anyBool)
  | .isIpv6, [.ext .ipAddr]                             => ok (.bool .anyBool)
  | .isLoopback, [.ext .ipAddr]                         => ok (.bool .anyBool)
  | .isMulticast, [.ext .ipAddr]                        => ok (.bool .anyBool)
  | .isInRange, [.ext .ipAddr, .ext .ipAddr]            => ok (.bool .anyBool)
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
    typeOfBinaryApp op₂ ty₁ ty₂ x₁ x₂ env
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
    let atys ← axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => requiredAttr a₁ (typeOf x₁ c env))
    ok (.record (Map.make atys))
  | .call xfn xs => do
    let tys ← xs.mapM₁ (λ ⟨x₁, _⟩ => justType (typeOf x₁ c env))
    typeOfCall xfn tys xs

end Cedar.Validation
