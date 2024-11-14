
import Cedar.Spec
import Cedar.Validation.Types

namespace Cedar.Validation

open Cedar.Data
open Cedar.Spec

inductive TypedExpr where
  | lit (p : Prim) (ty : CedarType)
  | var (v : Var) (ty : CedarType)
  | ite (cond : TypedExpr) (thenExpr : TypedExpr) (elseExpr : TypedExpr) (ty : CedarType)
  | and (a : TypedExpr) (b : TypedExpr) (ty : CedarType)
  | or (a : TypedExpr) (b : TypedExpr) (ty : CedarType)
  | unaryApp (op : UnaryOp) (expr : TypedExpr) (ty : CedarType)
  | binaryApp (op : BinaryOp) (a : TypedExpr) (b : TypedExpr) (ty : CedarType)
  | getAttr (expr : TypedExpr) (attr : Attr) (ty : CedarType)
  | hasAttr (expr : TypedExpr) (attr : Attr) (ty : CedarType)
  | set (ls : List TypedExpr) (ty : CedarType)
  | record (map : List (Attr × TypedExpr)) (ty : CedarType)
  | call (xfn : ExtFun) (args : List TypedExpr) (ty : CedarType)


deriving instance Repr, Inhabited for TypedExpr

mutual

def decTypedExpr (x y : TypedExpr) : Decidable (x = y) := by
  cases x <;> cases y <;>
  try { apply isFalse ; intro h ; injection h }
  case lit.lit x₁ tx  y₁ ty  | var.var x₁ tx y₁ ty =>
    exact match decEq x₁ y₁, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _  | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case ite.ite x₁ x₂ x₃ tx y₁ y₂ y₃ ty =>
    exact match decTypedExpr x₁ y₁, decTypedExpr x₂ y₂, decTypedExpr x₃ y₃, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse _, _, _, _ | _, isFalse _, _, _ | _, _, isFalse _, _ | _, _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case and.and x₁ x₂ tx y₁ y₂ ty | or.or x₁ x₂ tx y₁ y₂ ty =>
    exact match decTypedExpr x₁ y₁, decTypedExpr x₂ y₂, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case unaryApp.unaryApp o x₁ tx o' y₁ ty =>
    exact match decEq o o', decTypedExpr x₁ y₁, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case binaryApp.binaryApp o x₁ x₂ tx o' y₁ y₂ ty =>
    exact match decEq o o', decTypedExpr x₁ y₁, decTypedExpr x₂ y₂, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃, isTrue h₄ => isTrue (by rw [h₁, h₂, h₃, h₄])
    | isFalse _, _, _, _ | _, isFalse _, _, _ | _, _, isFalse _, _ | _, _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case getAttr.getAttr x₁ a tx y₁ a' ty | hasAttr.hasAttr x₁ a tx y₁ a' ty =>
    exact match decTypedExpr x₁ y₁, decEq a a', decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case set.set xs tx ys ty =>
    exact match decExprList xs ys, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case record.record axs tx ays ty =>
    exact match decProdAttrExprList axs ays, decEq tx ty with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
  case call.call f xs tx f' ys ty =>
    exact match decEq f f', decExprList xs ys, decEq tx ty with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ => isFalse (by intro h; injection h; contradiction)

def decProdAttrExprList (axs ays : List (Prod Attr TypedExpr)) : Decidable (axs = ays) :=
  match axs, ays with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | (a, x)::axs, (a', y)::ays =>
    match decEq a a', decTypedExpr x y, decProdAttrExprList axs ays with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse _, _, _ | _, isFalse _, _ | _, _, isFalse _ =>
      isFalse (by simp; intros; first | contradiction | assumption)

def decExprList (xs ys : List TypedExpr) : Decidable (xs = ys) :=
  match xs, ys with
  | [], [] => isTrue rfl
  | _::_, [] | [], _::_ => isFalse (by intro; contradiction)
  | x::xs, y::ys =>
    match decTypedExpr x y, decExprList xs ys with
    | isTrue h₁, isTrue h₂ => isTrue (by rw [h₁, h₂])
    | isFalse _, _ | _, isFalse _ => isFalse (by intro h; injection h; contradiction)
end

instance : DecidableEq TypedExpr := decTypedExpr

end Cedar.Validation
