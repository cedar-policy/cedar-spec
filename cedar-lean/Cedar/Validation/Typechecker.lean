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
import Cedar.Validation.Subtyping

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

inductive TypeError where
  | levelError (ety : EntityType)
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

abbrev ResultType := Except TypeError (CedarType × Capabilities)

def ok (ty : CedarType) (c : Capabilities := ∅) : ResultType := .ok (ty, c)
def err (e : TypeError) : ResultType := .error e

def typeOfLit (p : Prim) (env : Environment) (inf : Bool) : ResultType :=
  match p with
  | .bool true     => ok (.bool .tt)
  | .bool false    => ok (.bool .ff)
  | .int _         => ok .int
  | .string _      => ok .string
  | .entityUID uid =>
    if env.ets.contains uid.ty || env.acts.contains uid
    -- Type the entity at level 0 if we're checking a finite leve schema
    --  This will forbid derefernces of entity literals
    -- othewise give it level infinity
    then ok (.entity uid.ty (if inf then Level.infinite else Level.finite 0 ))
    else err (.unknownEntity uid.ty)

def typeOfVar (v : Var) (env : Environment) : ResultType :=
  match v with
  | .principal => ok (.entity env.reqty.principal.fst env.reqty.principal.snd)
  | .action    =>
    ok (.entity env.reqty.action.fst.ty env.reqty.action.snd)
  | .resource => ok (.entity env.reqty.resource.fst env.reqty.resource.snd)
  | .context   => ok (.record env.reqty.context)

def typeOfIf (r₁ : CedarType × Capabilities) (r₂ r₃ : ResultType) : ResultType :=
  match r₁ with
  | (.bool .tt, c₁) => do
    let (ty₂, c₂) ← r₂
    ok ty₂ (c₁ ∪ c₂)
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
    | .bool .ff      => ok (.bool .ff)
    | .bool .tt      => ok (.bool ty₁) (c₁ ∪ c₂)
    | .bool .anyBool => ok (.bool .anyBool) (c₁ ∪ c₂)
    | _              => err (.unexpectedType ty₂)
  | (ty₁, _)         => err (.unexpectedType ty₁)

def typeOfOr (r₁ : CedarType × Capabilities) (r₂ : ResultType) : ResultType :=
  match r₁ with
  | (.bool .tt, _)  => ok (.bool .tt)
  | (.bool .ff, _)  => do
    let (ty₂, c₂) ← r₂
    match ty₂ with
    | .bool _       => ok ty₂ c₂
    | _             => err (.unexpectedType ty₂)
  | (.bool _, c₁)   => do
    let (ty₂, c₂) ← r₂
    match ty₂ with
    | .bool .tt     => ok (.bool .tt)
    | .bool .ff     => ok (.bool .anyBool) c₁
    | .bool _       => ok (.bool .anyBool) (c₁ ∩ c₂)
    | _             => err (.unexpectedType ty₂)
  | (ty₁, _)        => err (.unexpectedType ty₁)

def typeOfUnaryApp (op : UnaryOp) (ty : CedarType) : ResultType :=
  match op, ty with
  | .not, .bool x          => ok (.bool x.not)
  | .neg, .int             => ok .int
  | .like _, .string       => ok (.bool .anyBool)
  | .is ety₁, .entity ety₂ _ => ok (.bool (if ety₁ = ety₂ then .tt else .ff))
  | _, _                   => err (.unexpectedType ty)

def typeOfEq (ty₁ ty₂ : CedarType) (x₁ x₂ : Expr) : ResultType :=
  match x₁, x₂ with
  | .lit p₁, .lit p₂ => if p₁ == p₂ then ok (.bool .tt) else ok (.bool .ff)
  | _, _ =>
    match ty₁ ⊔ ty₂ with
    | .some _ => ok (.bool .anyBool)
    | .none   =>
    match ty₁, ty₂ with
    | .entity _ _, .entity _ _ => ok (.bool .ff)
    | _, _                 => err (.lubErr ty₁ ty₂)

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

-- x₁ in x₂ where x₁ has type ety₁ at level l₁ and x₂ has type ety₂
def typeOfInₑ (ety₁  ety₂ : EntityType) (l₁ : Level ) (x₁ x₂ : Expr) (env : Environment) : ResultType :=
  if l₁ > Level.zero then ok (.bool type) else err (.levelError ety₁)
  where
    type := match actionUID? x₁ env.acts, entityUID? x₂ with
            | .some uid₁, .some uid₂ =>
              if env.acts.descendentOf uid₁ uid₂
              then .tt else .ff
            | _, _ =>
              if env.ets.descendentOf ety₁ ety₂
              then .anyBool else .ff

-- x₁ in x₂ where x₁ has type ety₁ at level l₁ and x₂ has type (.set ety₂)
def typeOfInₛ (ety₁ ety₂ : EntityType) (l₁ : Level) (x₁ x₂ : Expr) (env : Environment) : ResultType :=
  if l₁ > Level.zero then ok (.bool type) else err (.levelError ety₁)
  where
    type := match actionUID? x₁ env.acts, entityUIDs? x₂ with
            | .some uid₁, .some uids =>
              if uids.any (env.acts.descendentOf uid₁ ·)
              then .tt else .ff
            | _, _ =>
              if env.ets.descendentOf ety₁ ety₂
              then .anyBool else .ff

def typeOfHasTag (ety : EntityType) (l : Level) (x : Expr) (t : Expr) (c : Capabilities) (env : Environment) : ResultType := do
  let (type, caps) ← mtype;
  if l > Level.zero then ok type caps else err (.levelError ety)
  where
    mtype :=
      match env.ets.tags? ety with
      | .some .none     => ok (.bool .ff)
      | .some (.some _) =>
        if (x, .tag t) ∈ c
        then ok (.bool .tt)
        else ok (.bool .anyBool) (Capabilities.singleton x (.tag t))
      | .none           =>
        if actionType? ety env.acts
        then ok (.bool .ff) -- action tags not allowed
        else err (.unknownEntity ety)

def typeOfGetTag (ety : EntityType) (l : Level) (x : Expr) (t : Expr) (c : Capabilities) (env : Environment) : ResultType := do
  let (type, caps) ← mtype;
  if l > Level.zero then ok type caps else err (.levelError ety)
  where
    mtype :=
      match env.ets.tags? ety with
      | .some .none      => err (.tagNotFound ety t)
      | .some (.some ty) => if (x, .tag t) ∈ c then ok ty else err (.tagNotFound ety t)
      | .none            => err (.unknownEntity ety)

def ifLubThenBool (ty₁ ty₂ : CedarType) : ResultType :=
  match ty₁ ⊔ ty₂ with
  | some _ => ok (.bool .anyBool)
  | none   => err (.lubErr ty₁ ty₂)

def typeOfBinaryApp (op₂ : BinaryOp) (ty₁ ty₂ : CedarType) (x₁ x₂ : Expr) (c : Capabilities) (env : Environment) : ResultType :=
  match op₂, ty₁, ty₂ with
  | .eq, _, _                               => typeOfEq ty₁ ty₂ x₁ x₂
  | .mem, .entity ety₁ l₁, .entity ety₂ _        => typeOfInₑ ety₁ ety₂ l₁ x₁ x₂ env
  | .mem, .entity ety₁ l₁, .set (.entity ety₂ _) => typeOfInₛ ety₁ ety₂ l₁ x₁ x₂ env
  | .hasTag, .entity ety₁ l, .string          => typeOfHasTag ety₁ l x₁ x₂ c env
  | .getTag, .entity ety₁ l, .string          => typeOfGetTag ety₁ l x₁ x₂ c env
  | .less,   .int, .int                     => ok (.bool .anyBool)
  | .lessEq, .int, .int                     => ok (.bool .anyBool)
  | .add,    .int, .int                     => ok .int
  | .sub,    .int, .int                     => ok .int
  | .mul,    .int, .int                     => ok .int
  | .contains, .set ty₃, _                  => ifLubThenBool ty₂ ty₃
  | .containsAll, .set ty₃, .set ty₄        => ifLubThenBool ty₃ ty₄
  | .containsAny, .set ty₃, .set ty₄        => ifLubThenBool ty₃ ty₄
  | _, _, _                                 => err (.unexpectedType ty₁)

def hasAttrInRecord (rty : RecordType) (x : Expr) (a : Attr) (c : Capabilities) (knownToExist : Bool) : ResultType :=
  match rty.find? a with
  | .some qty =>
    if (x, .attr a) ∈ c || (qty.isRequired && knownToExist)
    then ok (.bool .tt)
    else ok (.bool .anyBool) (Capabilities.singleton x (.attr a))
  | .none     => ok (.bool .ff)

def typeOfHasAttr (ty : CedarType) (x : Expr) (a : Attr) (c : Capabilities) (env : Environment) : ResultType :=
  match ty with
  | .record rty => hasAttrInRecord rty x a c true
  | .entity ety level =>
        let hasType :=
          match env.ets.attrs? ety with
          | .some rty => hasAttrInRecord rty x a c false
          | .none     =>
            if actionType? ety env.acts
            then ok (.bool .ff) -- action attributes not allowed
            else err (.unknownEntity ety)
        if level > Level.zero then hasType else err (.levelError ety)
  | _           => err (.unexpectedType ty)


def setLevel (l: Level) (ty : CedarType)  : CedarType :=
  match ty with
  | .bool b => .bool b
  | .int => .int
  | .string => .string
  | .entity ety _  => .entity ety l
  | .set ty => .set (setLevel l ty)
  | .record rty =>
    .record (rty.mapOnValuesAttach (λ v =>
      match _h : v.val with
      | .required ty => .required (setLevel l ty)
      | .optional ty => .optional (setLevel l ty)
    ))
  | .ext ty => .ext ty
termination_by sizeOf ty
decreasing_by
  all_goals simp_wf
  all_goals try omega
  all_goals {
      have h₁ := v.property
      cases h₁
      rename_i k h₁
      have h₂ : sizeOf ty < sizeOf (k, v.val) := by
        rw [_h]
        simp
        omega
      have h₃ : sizeOf (k, v.val) < sizeOf rty.kvs := by
        apply List.sizeOf_lt_of_mem
        assumption
      have h₄ : sizeOf rty.kvs < sizeOf rty := by
        apply Cedar.Data.Map.sizeOf_lt_of_kvs

      omega
  }




def getAttrInRecord (ty : CedarType) (rty : RecordType) (x : Expr) (a : Attr) (c : Capabilities) : ResultType :=
  match rty.find? a with
  | .some (.required aty) => ok aty
  | .some (.optional aty) => if (x, .attr a) ∈ c then ok aty else err (.attrNotFound ty a)
  | .none                 => err (.attrNotFound ty a)

def typeOfGetAttr (ty : CedarType) (x : Expr) (a : Attr) (c : Capabilities) (env : Environment) : ResultType :=
  match ty with
  | .record rty => getAttrInRecord ty rty x a c
  | .entity ety level =>
    if level > Level.zero then
      match env.ets.attrs? ety with
      | .some rty => do
        let (type, caps) ← getAttrInRecord ty rty x a c
        .ok (setLevel level.sub1 type, caps)
      | .none     => err (.unknownEntity ety)
    else err $ .levelError ety
  | _           => err (.unexpectedType ty)

def typeOfSet (tys : List CedarType) : ResultType :=
  match tys with
  | []       => err .emptySetErr
  | hd :: tl =>
    match tl.foldlM lub? hd with
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
def typeOf (x : Expr) (c : Capabilities) (env : Environment) (inf: Bool) : ResultType :=
  match x with
  | .lit p => typeOfLit p env inf
  | .var v => typeOfVar v env
  | .ite x₁ x₂ x₃ => do
    let (ty₁, c₁) ← typeOf x₁ c env inf
    typeOfIf (ty₁, c₁) (typeOf x₂ (c ∪ c₁) env inf) (typeOf x₃ c env inf)
  | .and x₁ x₂ => do
    let (ty₁, c₁) ← typeOf x₁ c env inf
    typeOfAnd (ty₁, c₁) (typeOf x₂ (c ∪ c₁) env inf)
  | .or x₁ x₂ => do
    let (ty₁, c₁) ← typeOf x₁ c env inf
    typeOfOr (ty₁, c₁) (typeOf x₂ c env inf)
  | .unaryApp op₁ x₁ => do
    let (ty₁, _) ← typeOf x₁ c env inf
    typeOfUnaryApp op₁ ty₁
  | .binaryApp op₂ x₁ x₂ => do
    let (ty₁, _) ← typeOf x₁ c env inf
    let (ty₂, _) ← typeOf x₂ c env inf
    typeOfBinaryApp op₂ ty₁ ty₂ x₁ x₂ c env
  | .hasAttr x₁ a => do
    let (ty₁, _) ← typeOf x₁ c env inf
    typeOfHasAttr ty₁ x₁ a c env
  | .getAttr x₁ a => do
    let (ty₁, _) ← typeOf x₁ c env inf
    typeOfGetAttr ty₁ x₁ a c env
  | .set xs => do
    let tys ← xs.mapM₁ (λ ⟨x₁, _⟩ => justType (typeOf x₁ c env inf))
    typeOfSet tys
  | .record axs => do
    let atys ← axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => requiredAttr a₁ (typeOf x₁ c env inf))
    ok (.record (Map.make atys))
  | .call xfn xs => do
    let tys ← xs.mapM₁ (λ ⟨x₁, _⟩ => justType (typeOf x₁ c env inf))
    typeOfCall xfn tys xs

---- Derivations -----

deriving instance Repr for RequestType
deriving instance Repr for Environment

end Cedar.Validation
