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

/- The result produced by TPE.
   ResidualValue, ResidualAttribute, and Residual are mutually inductive.
   A ResidualAttribute.unknown holds a Residual (the expression that would
   compute the unknown value at full-evaluation time). -/
mutual

inductive ResidualAttribute where
  | present (val : ResidualValue)
  | unknown (expr : Residual) (ty : CedarType)

inductive ResidualValue where
  | prim (p : Prim)
  | set (s : Set Value)
  | record (m : List (Attr × ResidualAttribute))
  | ext (x : Ext)

inductive Residual where
  | val (v : ResidualValue) (ty : CedarType)
  | var (v : Var) (ty : CedarType)
  | ite (cond : Residual) (thenExpr : Residual) (elseExpr : Residual) (ty : CedarType)
  | and (a : Residual) (b : Residual) (ty : CedarType)
  | or (a : Residual) (b : Residual) (ty : CedarType)
  | unaryApp (op : UnaryOp) (expr : Residual) (ty : CedarType)
  | binaryApp (op : BinaryOp) (a : Residual) (b : Residual) (ty : CedarType)
  | getAttr (expr : Residual) (attr : Attr) (ty : CedarType)
  | hasAttr (expr : Residual) (attr : Attr) (ty : CedarType)
  | set (ls : List Residual) (ty : CedarType)
  | record (map : List (Attr × Residual)) (ty : CedarType)
  | call (xfn : ExtFun) (args : List Residual) (ty : CedarType)
  | error (ty : CedarType)

end

instance : Inhabited ResidualAttribute where default := .present (.prim (.bool false))
instance : Inhabited ResidualValue where default := .prim (.bool false)
instance : Inhabited Residual where default := .error (.bool .anyBool)

instance : Coe Bool Residual where
  coe b := .val (.prim (.bool b)) (.bool .anyBool)

instance : Coe String Residual where
  coe s := .val (.prim (.string s)) .string

instance : Coe EntityUID Residual where
  coe uid := .val (.prim (.entityUID uid)) (.entity uid.ty)

partial def Value.asResidualValue : Value → ResidualValue
  | .prim p => .prim p
  | .ext x => .ext x
  | .set s => .set s
  | .record as => .record (as.toList.attach₂.map λ kv => (kv.val.fst, .present kv.val.snd.asResidualValue))

instance : Coe Value ResidualValue where
  coe v := Value.asResidualValue v

instance {α : Type _} [Coe α Value] : Coe α ResidualValue where
  coe v := Value.asResidualValue v

partial def ResidualValue.toPartialValue : ResidualValue → PartialValue
  | .prim p => .prim p
  | .set s => .set s
  | .ext x => .ext x
  | .record m => .record (Map.mk (m.map fun (a, ra) =>
    (a, match ra with
      | .present rv => .present rv.toPartialValue
      | .unknown _ ty => .unknown ty)))

end Cedar.Spec

namespace Cedar.TPE

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

partial def PartialValue.toResidualValue (target : Residual) : PartialValue → CedarType → ResidualValue
  | .prim p, _ => .prim p
  | .set s, _ => .set s
  | .ext x, _ => .ext x
  | .record m, .record rty => .record (m.toList.map fun (a, pa) =>
    (a, match pa with
      | .present pv =>
        let aty := Qualified.getType <$> rty.find? a|>.getD (.bool .anyBool)
        .present (PartialValue.toResidualValue (.getAttr target a (.record rty)) pv aty)
      | .unknown ty => .unknown target ty))
  | _, _ => .prim (.bool false)

end Cedar.TPE

namespace Cedar.Spec

open Cedar.TPE
open Cedar.Data
open Cedar.Validation

def Residual.asResidualValue : Residual → Option ResidualValue
  | .val v _ => .some v
  | _        => .none

partial def ResidualValue.asValue : ResidualValue → Option Value
  | .record as => (Value.record ∘ Map.make) <$> as.mapM λ (a, ra) =>
    match ra with
    | .present rv => do some (a, ←rv.asValue)
    | _ => none
  | .prim p   => .some p
  | .set es   => .some (.set es)
  | .ext x    => .some (.ext x)

def Residual.asValue :=
  Residual.asResidualValue >=> ResidualValue.asValue

def Residual.isError : Residual → Bool
  | .error _ => true
  | _        => false

def Residual.typeOf : Residual → CedarType
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

-- The interpreter of `Residual` that defines its semantics
mutual

partial def ResidualValue.evaluate (rv : ResidualValue) (req : Request) (es : Entities) : Result Value :=
  match rv with
  | .prim p => .ok p
  | .set s => .ok s
  | .ext e => .ok e
  | .record r => do
    let t ← r.mapM (λ (a, ra) =>
      bindAttr a (match ra with
        | .present v' => ResidualValue.evaluate v' req es
        | .unknown expr ty => Residual.evaluate (.getAttr expr a ty) req es))
    .ok ∘ .record ∘ Map.make $ t

partial def Residual.evaluate (x : Residual) (req : Request) (es: Entities) : Result Value :=
  match x with
  | .val p _ => ResidualValue.evaluate p req es
  | .var v _ =>
    match v with
    | .principal => .ok req.principal
    | .resource => .ok req.resource
    | .action => .ok req.action
    | .context => .ok req.context
  | .ite c x y _ => do
    let c ← Residual.evaluate c req es
    let b ← c.asBool
    if b then Residual.evaluate x req es else Residual.evaluate y req es
  | .and x y _ => do
    let b ← (Residual.evaluate x req es).as Bool
    if !b then .ok b else (Residual.evaluate y req es).as Bool
  | .or x y _ => do
    let b ← (Residual.evaluate x req es).as Bool
    if b then .ok b else (Residual.evaluate y req es).as Bool
  | .unaryApp op e _ => do
    let v ← Residual.evaluate e req es
    apply₁ op v
  | .binaryApp op x y _ => do
    let v₁ ← Residual.evaluate x req es
    let v₂ ← Residual.evaluate y req es
    apply₂ op v₁ v₂ es
  | .hasAttr e a _ => do
    let v ← Residual.evaluate e req es
    Cedar.Spec.hasAttr v a es
  | .getAttr e a _ => do
    let v ← Residual.evaluate e req es
    Cedar.Spec.getAttr v a es
  | .set xs _ => do
    let vs ← xs.mapM (Residual.evaluate · req es)
    .ok (Set.make vs)
  | .record axs _ => do
    let avs ← axs.mapM (fun (a₁, x₁) => bindAttr a₁ (Residual.evaluate x₁ req es))
    .ok (Map.make avs)
  | .call xfn xs _ => do
    let vs ← xs.mapM (Residual.evaluate · req es)
    Cedar.Spec.call xfn vs
  | .error _ => .error .extensionError

end

mutual

partial def ResidualValue.allLiteralUIDs : ResidualValue → Set EntityUID
  | .prim (.entityUID uid)  => Set.singleton uid
  | .record m => m.foldl (fun acc (_, ra) =>
    match ra with
    | .present v' => acc ∪ ResidualValue.allLiteralUIDs v'
    | .unknown expr _ => acc ∪ Residual.allLiteralUIDs expr) Set.empty
  | .prim _  | .set _ | .ext _ => Set.empty

partial def Residual.allLiteralUIDs (x : Residual) : Set EntityUID :=
  match x with
  | .val v _ => ResidualValue.allLiteralUIDs v
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

end

mutual

def decResidualAttribute (x y : ResidualAttribute) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case present.present v₁ v₂ =>
    exact match decRValue v₁ v₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unknown.unknown e₁ t₁ e₂ t₂ =>
    exact match decResidual e₁ e₂, decEq t₁ t₂ with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decRValue (v₁ v₂ : ResidualValue) : Decidable (v₁ = v₂) := by
  cases v₁ <;> cases v₂ <;>
  try { apply isFalse ; intro h ; injection h }
  case prim.prim w₁ w₂ | ext.ext w₁ w₂ =>
    exact match decEq w₁ w₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set s₁ s₂ =>
    exact match decEq s₁ s₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse h₁ => isFalse (by intro h₂; injection h₂; contradiction)
  case record.record r₁ r₂ =>
    exact match decProdAttrRValueList r₁ r₂ with
    | isTrue h => isTrue (by rw [h])
    | isFalse h₁ => isFalse (by intro h₂; injection h₂; contradiction)

def decProdAttrRValueList (avs₁ avs₂ : List (Attr × ResidualAttribute)) : Decidable (avs₁ = avs₂) :=
  match avs₁, avs₂ with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a₁, v₁) :: vs₁, (a₂, v₂) :: vs₂ =>
    match decEq a₁ a₂, decResidualAttribute v₁ v₂, decProdAttrRValueList vs₁ vs₂ with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decResidual (x y : Residual) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case val.val x₁ tx y₁ ty =>
    exact match decRValue x₁ y₁, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _  | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case var.var x₁ tx y₁ ty =>
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

instance : DecidableEq ResidualAttribute := decResidualAttribute
instance : DecidableEq ResidualValue := decRValue
instance : DecidableEq Residual := decResidual

instance : BEq ResidualAttribute where beq a b := decide (a = b)
instance : BEq ResidualValue where beq a b := decide (a = b)
instance : BEq Residual where beq a b := decide (a = b)

end Cedar.Spec

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

def TypedExpr.toResidual : TypedExpr → Residual
  | .lit p ty => .val (.prim p) ty
  | .var v ty => .var v ty
  | .ite x₁ x₂ x₃ ty => .ite (TypedExpr.toResidual x₁) (TypedExpr.toResidual x₂) (TypedExpr.toResidual x₃) ty
  | .and a b ty => .and (TypedExpr.toResidual a) (TypedExpr.toResidual b) ty
  | .or a b ty => .or (TypedExpr.toResidual a) (TypedExpr.toResidual b) ty
  | .unaryApp op expr ty => .unaryApp op (TypedExpr.toResidual expr) ty
  | .binaryApp op a b ty => .binaryApp op (TypedExpr.toResidual a) (TypedExpr.toResidual b) ty
  | .getAttr expr attr ty => .getAttr (TypedExpr.toResidual expr) attr ty
  | .hasAttr expr attr ty => .hasAttr (TypedExpr.toResidual expr) attr ty
  | .set ls ty => .set (ls.map₁ (λ ⟨e, _⟩ => TypedExpr.toResidual e)) ty
  | .record ls ty => .record (ls.map₂ (λ ⟨(a, e), _⟩ => (a, TypedExpr.toResidual e))) ty
  | .call xfn args ty => .call xfn (args.map₁ (λ ⟨e, _⟩ => TypedExpr.toResidual e)) ty
decreasing_by
  all_goals (simp_wf ; try omega)
  all_goals
    rename_i h
    try simp at h
    try replace h := List.sizeOf_lt_of_mem h
    omega

end Cedar.Validation
