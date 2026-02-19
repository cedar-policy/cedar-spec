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

import Cedar.Spec.Expr
import Cedar.Spec.Value
import Cedar.Validation.TypedExpr
import Cedar.TPE.Input

namespace Cedar.Spec

open Cedar.TPE
open Cedar.Data
open Cedar.Spec
open Cedar.Validation

-- inductive PartialAttribute' (T : Type _) where
--   | present (val : T)               -- Known present, known value
--   | unknown (ty : CedarType) (target : T) -- Unknown present, unknown value
-- deriving Repr, Inhabited, BEq
--
-- inductive PartialValue' where
--   | prim (p : Prim)
--   | set (s : Set Value)
--   | record (m : Map Attr (PartialAttribute' PartialValue'))
--   | ext (x : Ext)

/- The result produced by TPE -/
-- We do not need unknown`s because they can be represented by entity dereferences
inductive Residual where
  | access (p : AccessPath) (ty : CedarType)
  | val (v : PartialValue) (ty : CedarType)
  | var (v : Var) (ty : CedarType)
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
  | error (ty : CedarType)
deriving Repr, Inhabited, BEq

instance : Coe Bool Residual where
  coe b := .val (Prim.bool b) (.bool .anyBool)

instance : Coe String Residual where
  coe s := .val (Prim.string s) .string

instance : Coe EntityUID Residual where
  coe uid := .val (Prim.entityUID uid) (.entity uid.ty)

def Residual.asPartialValue : Residual → Option PartialValue
  | .val v _ => .some v
  | _        => .none

def Residual.asValue :=
  Residual.asPartialValue >=> PartialValue.asValue

-- def Residual.asValue : Residual → Option Value
--   | .val v _ => .some v
--   | _        => .none
--
-- def PartialAttribute'.asValue : PartialAttribute' Residual → Option Value
--   | .present r => r.asValue
--   | _ => .none
--
-- def Value.toResidual (v : Value) (ty : CedarType) : Residual :=
--   .val v ty

def Residual.isError : Residual → Bool
  | .error _ => true
  | _        => false

-- def PartialAttribute'.isError : PartialAttribute' Residual → Bool
--   | .present r => r.isError
--   | _ => false

def Residual.typeOf : Residual → CedarType
  | .access _ ty
  | .val _ ty
  | .var _ ty
  | .ite _ _ _ ty
  | .and _ _ ty
  | .or _ _ ty
  | .unaryApp _ _ ty
  | .binaryApp _ _ _ ty
  | .getAttr _ _ ty
  | .hasAttr _ _ ty
  | .set _ ty
  | .record _ ty
  | .call _ _ ty
  | .error ty => ty


def BinaryOp.canError : BinaryOp → Bool
  | .add | .sub | .mul | .getTag => true
  | _ => false

def UnaryOp.canError : UnaryOp → Bool
  | .neg => true
  | _ => false

-- Assumes the residual is well typed, so there can be no type errors.
def Residual.errorFree : Residual → Bool
  -- TODO: Evaluating a nested unknown attribute may result in an
  -- entity-does-not exist error or tag-not-found error, but both of these
  -- should be ruled out by the entity consistency condition.
  | .val _ _ => true
  | .var _ _ => true
  | .binaryApp op x₁ x₂ _ =>
    !op.canError && x₁.errorFree && x₂.errorFree
  | .unaryApp op x₁ _ =>
    !op.canError && x₁.errorFree
  | .and x₁ x₂ _ =>
    x₁.errorFree && x₂.errorFree
  | .or x₁ x₂ _ =>
    x₁.errorFree && x₂.errorFree
  | ite x₁ x₂ x₃ _ =>
    x₁.errorFree && x₂.errorFree && x₃.errorFree
  | hasAttr x₁ _ _ =>
    x₁.errorFree
  | .set xs _ => xs.attach.all λ x =>
    have : sizeOf x.val < sizeOf xs :=
      List.sizeOf_lt_of_mem x.property
    x.val.errorFree
  | record xs _ =>
    xs.attach₂.all (·.val.snd.errorFree)
  | _ => false
-- termination_by 0
-- decreasing_by all_goals sorry

def AccessPath.evaluate (ap : AccessPath) (req : Request) (es : Entities) : Result Value :=
  match ap with
  | .context => .ok req.context
  | .entityUID uid => .ok uid
  | .getAttr ap' a => do
    let v ← AccessPath.evaluate ap' req es
    Cedar.Spec.getAttr v a es
  | .getTag ap' t => do
    let v ← AccessPath.evaluate ap' req es
    match v with
    | .prim (.entityUID v) => Cedar.Spec.getTag v t es
    | _ => .error .typeError

partial def PartialValue.evaluate (pv : PartialValue) (req : Request) (es : Entities) : Result Value :=
  match pv with
  | .prim p => .ok p
  | .set s => .ok s
  | .ext e => .ok e
  | .record r => do
    let t ← r.kvs.mapM₂ (λ v =>
    bindAttr v.val.fst (match v.val.snd with
      | .present v' =>
        PartialValue.evaluate v' req es
      | .unknown p _ => AccessPath.evaluate p req es))
    .ok ∘ .record ∘ Map.make $ t
termination_by pv

-- The interpreter of `Residual` that defines its semantics
def Residual.evaluate (x : Residual) (req : Request) (es: Entities) : Result Value :=
  match x with
  | .val p _ => PartialValue.evaluate p req es
  | .access p _ => AccessPath.evaluate p req es
  | .var v _ =>
    match v with
    | .principal => .ok req.principal
    | .resource => .ok req.resource
    | .action => .ok req.action
    | .context => .ok req.context
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
    Cedar.Spec.getAttr v a es
  | .set xs _ => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    .ok (Set.make vs)
  | .record axs _ => do
    let avs ← axs.mapM₂ (fun ⟨(a₁, x₁), _⟩ => bindAttr a₁ (evaluate x₁ req es))
    .ok (Map.make avs)
  | .call xfn xs _ => do
    let vs ← xs.mapM₁ (fun ⟨x₁, _⟩ => evaluate x₁ req es)
    Cedar.Spec.call xfn vs
  | .error _ => .error .extensionError
termination_by x
decreasing_by
  all_goals
    simp_wf
    rename_i h
    try have := List.sizeOf_lt_of_mem h
    try simp at h
    omega

def AccessPath.allLiteralUIDs : AccessPath → Set EntityUID
  | .context => Set.empty
  | .entityUID uid =>  Set.singleton uid
  | .getAttr p _ => AccessPath.allLiteralUIDs p
  | .getTag p _ => AccessPath.allLiteralUIDs p

partial def PartialValue.allLiteralUIDs : PartialValue → Set EntityUID
  | .prim (.entityUID uid)  => Set.singleton uid
  -- TODO: original function wouldn't look inside record value like `{f: User::"alice"}`
  | .record m => m.kvs.mapUnion₂ (λ ⟨⟨_attr, v⟩, _⟩ =>
    match v with
    | .present v' => PartialValue.allLiteralUIDs v'
    | .unknown p _ => AccessPath.allLiteralUIDs p)
  | .prim _  | .set _ | .ext _ => Set.empty

def Residual.allLiteralUIDs (x : Residual) : Set EntityUID :=
  match x with
  | .val v _ => PartialValue.allLiteralUIDs v
  | .access p _ => AccessPath.allLiteralUIDs p
  | .error _e                          => Set.empty
  | .var _ _                           => Set.empty
  | .ite x₁ x₂ x₃ _      =>
    x₁.allLiteralUIDs ∪ x₂.allLiteralUIDs ∪ x₃.allLiteralUIDs
  | .and x₁ x₂ _         =>
    x₁.allLiteralUIDs ∪ x₂.allLiteralUIDs
  | .or x₁ x₂ _          =>
    x₁.allLiteralUIDs ∪ x₂.allLiteralUIDs
  | .unaryApp _ x _      =>
    x.allLiteralUIDs
  | .binaryApp _ x₁ x₂ _ =>
    x₁.allLiteralUIDs ∪ x₂.allLiteralUIDs
  | .getAttr x _ _       => Residual.allLiteralUIDs x
  | .hasAttr x _ _       => Residual.allLiteralUIDs x
  | .set x _             =>
    x.mapUnion₁ (λ ⟨v, _⟩ => Residual.allLiteralUIDs v)
  | .record x _          =>
    x.mapUnion₂ (λ ⟨⟨_attr, v⟩, _⟩ => Residual.allLiteralUIDs v)
  | .call _ x _          =>
    x.mapUnion₁ (λ ⟨v, _⟩ => Residual.allLiteralUIDs v)
termination_by sizeOf x
decreasing_by
  any_goals
    simp
    try simp at *
    try omega
  all_goals
    rename_i h
    let so := List.sizeOf_lt_of_mem h
    simp at *
    omega

mutual

def decResidual (x y : Residual) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case val.val x₁ tx  y₁ ty | var.var x₁ tx y₁ ty | access.access x₁ tx y₁ ty =>
    exact match decEq x₁ y₁, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _  | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ tx y₁ y₂ y₃ ty =>
    exact match decResidual x₁ y₁, decResidual x₂ y₂, decResidual x₃ y₃, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse _, _, _, _ | _, isFalse _, _, _ | _, _, isFalse _, _ | _, _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ tx y₁ y₂ ty | or.or x₁ x₂ tx y₁ y₂ ty =>
    exact match decResidual x₁ y₁, decResidual x₂ y₂, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ tx o' y₁ ty =>
    exact match decEq o o', decResidual x₁ y₁, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ tx o' y₁ y₂ ty =>
    exact match decEq o o', decResidual x₁ y₁, decResidual x₂ y₂, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse _, _, _, _ | _, isFalse _, _, _ | _, _, isFalse _, _ | _, _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a tx y₁ a' ty | hasAttr.hasAttr x₁ a tx y₁ a' ty =>
    exact match decResidual x₁ y₁, decEq a a', decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs tx ys ty =>
    exact match decResidualList xs ys, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs tx ays ty =>
    exact match decProdAttrResidualList axs ays, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs tx f' ys ty =>
    exact match decEq f f', decResidualList xs ys, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case error.error ty₁ ty₂ =>
    exact match decEq ty₁ ty₂ with
    | isTrue h₁ => isTrue (by rw [h₁])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrResidualList (axs ays : List (Prod Attr Residual)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays => by
    simp only [List.cons.injEq, Prod.mk.injEq]
    have h₁ : Decidable (x = y) := decResidual x y
    cases h₁ <;> cases decProdAttrResidualList axs ays
    case isTrue.isTrue =>
      rename_i h₁ h₂
      subst h₁ h₂
      simp only [and_true]
      apply String.decEq
    all_goals
      rename_i h₁ h₂
      simp only [h₁, h₂]
      exact instDecidableAnd

def decResidualList (xs ys : List Residual) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decResidual x y, decResidualList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq Residual := decResidual

end Cedar.Spec

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec


def TypedExpr.toResidual : TypedExpr → Residual
  | .lit p ty => .val p ty
  | .var v ty => .var v ty
  | .ite x₁ x₂ x₃ ty => .ite (TypedExpr.toResidual x₁) (TypedExpr.toResidual x₂) (TypedExpr.toResidual x₃) ty
  | .and a b ty => .and (TypedExpr.toResidual a) (TypedExpr.toResidual b) ty
  | .or a b ty => .or (TypedExpr.toResidual a) (TypedExpr.toResidual b) ty
  | .unaryApp op expr ty => .unaryApp op (TypedExpr.toResidual expr) ty
  | .binaryApp op a b ty => .binaryApp op (TypedExpr.toResidual a) (TypedExpr.toResidual b) ty
  | .getAttr expr attr ty => .getAttr (TypedExpr.toResidual expr) attr ty
  | .hasAttr expr attr ty => .hasAttr (TypedExpr.toResidual expr) attr ty
  | .set ls ty => .set (ls.map₁ (λ ⟨e, _⟩ => TypedExpr.toResidual e)) ty
  | .record ls ty => .record (ls.attach₂.map (λ ⟨(a, e), _⟩ => (a, TypedExpr.toResidual e))) ty
  | .call xfn args ty => .call xfn (args.map₁ (λ ⟨e, _⟩ => TypedExpr.toResidual e)) ty
decreasing_by
  all_goals (simp_wf ; try omega)
  all_goals
    rename_i h
    try simp at h
    try replace h := List.sizeOf_lt_of_mem h
    omega


end Cedar.Validation
