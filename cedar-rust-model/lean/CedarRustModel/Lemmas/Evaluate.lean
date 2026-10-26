module

public import CedarRustModel.Lemmas.Ops
public import CedarRustModel.Ext.Correctness
import all Cedar.Data.Set
import all Cedar.Data.Map

/-! The model's evaluator agrees with `Cedar.Spec.evaluate`. -/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace CedarRustModel

open Aeneas Aeneas.Std Result cedar_rust_model Cedar.Spec Cedar.Data

public section

theorem bindAttr_ok {α} (a : Attr) (v : α) :
    (bindAttr a (Except.ok v : Cedar.Spec.Result α)) = .ok (a, v) := rfl
theorem bindAttr_error {α} (a : Attr) (e : Cedar.Spec.Error) :
    (bindAttr a (Except.error e : Cedar.Spec.Result α)) = .error e := rfl

theorem call_ext_ok (f : ext.ExtFun) (vs : value.List value.Value) :
    ∃ r, evaluator.call_ext f vs = ok r ∧
      Result.toSpec Value.toSpec r = Cedar.Spec.call (ExtFun.toSpec f) (Values.toSpec vs) := by
  obtain ⟨r, hr, hpost⟩ := spec_ok_exists (call_correct f vs)
  rw [← hpost]
  unfold evaluator.call_ext
  rw [hr]
  rcases r with ((_|_|_)|_) <;> simp [evaluator.ext_res_value, Result.toSpec, Value.toSpec, ExtRes.toSpec,
    Prim.toSpec]

mutual

theorem evaluate_ok (x : expr.Expr) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.evaluate x req es = ok r ∧
      Result.toSpec Value.toSpec r =
        Cedar.Spec.evaluate (Expr.toSpec x) (Request.toSpec req) (Entities.toSpec es) := by
  match x with
  | .Lit p =>
    rw [evaluator.evaluate.eq_def]
    simp [clone_prim_ok, Expr.toSpec, Cedar.Spec.evaluate]
  | .Var v =>
    rw [evaluator.evaluate.eq_def]
    cases v <;> simp [clone_uid_ok, clone_attrs_ok, Expr.toSpec, Var.toSpec, Cedar.Spec.evaluate,
      Request.toSpec]
  | .Ite x₁ x₂ x₃ =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    obtain ⟨b, h₃, h₄⟩ := as_bool_ok r₁
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂, ← h₄]
    simp only [h₁, Std.bind_ok]
    simp only [h₃, Std.bind_ok]
    cases b with
    | Err e => simp
    | Ok b =>
      cases b
      · simpa using evaluate_ok x₃ req es
      · simpa using evaluate_ok x₂ req es
  | .And x₁ x₂ =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    obtain ⟨b, h₃, h₄⟩ := as_bool_ok r₁
    obtain ⟨r₂, h₅, h₆⟩ := evaluate_ok x₂ req es
    obtain ⟨b', h₇, h₈⟩ := as_bool_ok r₂
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂, ← h₄, ← h₆, ← h₈]
    simp only [h₁, Std.bind_ok]
    simp only [h₃, Std.bind_ok]
    cases b with
    | Err e => simp
    | Ok b =>
      cases b
      · simp [evaluator.bool_val]
      · simp only [Bool.not_true, ite_true, Bool.false_eq_true, ite_false]
        simp only [h₅, Std.bind_ok, h₇]
        cases b' <;> simp [evaluator.bool_val]
  | .Or x₁ x₂ =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    obtain ⟨b, h₃, h₄⟩ := as_bool_ok r₁
    obtain ⟨r₂, h₅, h₆⟩ := evaluate_ok x₂ req es
    obtain ⟨b', h₇, h₈⟩ := as_bool_ok r₂
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂, ← h₄, ← h₆, ← h₈]
    simp only [h₁, Std.bind_ok]
    simp only [h₃, Std.bind_ok]
    cases b with
    | Err e => simp
    | Ok b =>
      cases b
      · simp only [ite_true, Bool.false_eq_true, ite_false]
        simp only [h₅, Std.bind_ok, h₇]
        cases b' <;> simp [evaluator.bool_val]
      · simp [evaluator.bool_val]
  | .UnaryApp op x₁ =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok v => simpa using apply1_ok op v
  | .BinaryApp op x₁ x₂ =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    obtain ⟨r₂, h₃, h₄⟩ := evaluate_ok x₂ req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂, ← h₄]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok v₁ =>
      simp only [h₃, Std.bind_ok]
      cases r₂ with
      | Err e => simp
      | Ok v₂ => simpa using apply2_ok op v₁ v₂ es
  | .GetAttr x₁ a =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok v => simpa using get_attr_ok v a es
  | .HasAttr x₁ a =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok v => simpa using has_attr_ok v a es
  | .ExtHasAttr x₁ a as₁ =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_ok x₁ req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate, ← h₂]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok v =>
      simp only [clone_str_ok, clone_strs_ok, Std.bind_ok, Result.toSpec_Ok, Except.bind_ok,
        hasAttrs]
      simpa using has_attrs_ok (.Cons a as₁) v es
  | .Set xs =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_list_ok xs req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate,
      _root_.List.mapM₁_eq_mapM (fun x => Cedar.Spec.evaluate x (Request.toSpec req) (Entities.toSpec es)),
      ← h₂]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok vs =>
      obtain ⟨ys, h₃, h₄⟩ := values_canonicalize_ok vs
      simp [h₃, Set.make, h₄]
      rfl
  | .Record axs =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_attrs_ok axs req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate,
      _root_.List.mapM₂_eq_mapM (fun (ax : Attr × Cedar.Spec.Expr) =>
        bindAttr ax.fst (Cedar.Spec.evaluate ax.snd (Request.toSpec req) (Entities.toSpec es))),
      ← h₂]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok avs =>
      obtain ⟨ys, h₃, h₄⟩ := attrs_canonicalize_ok avs
      simp [h₃, Map.make, h₄]
  | .Call f xs =>
    obtain ⟨r₁, h₁, h₂⟩ := evaluate_list_ok xs req es
    rw [evaluator.evaluate.eq_def]
    simp only [Expr.toSpec, Cedar.Spec.evaluate,
      _root_.List.mapM₁_eq_mapM (fun x => Cedar.Spec.evaluate x (Request.toSpec req) (Entities.toSpec es)),
      ← h₂]
    simp only [h₁, Std.bind_ok]
    cases r₁ with
    | Err e => simp
    | Ok vs => simpa using call_ext_ok f vs

theorem evaluate_list_ok (xs : value.List expr.Expr) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.evaluate_list xs req es = ok r ∧
      Result.toSpec Values.toSpec r =
        (Exprs.toSpec xs).mapM (fun x => Cedar.Spec.evaluate x (Request.toSpec req) (Entities.toSpec es)) := by
  match xs with
  | .Nil => rw [evaluator.evaluate_list.eq_def]; simp [Exprs.toSpec]
  | .Cons x xs =>
    rw [evaluator.evaluate_list.eq_def]
    obtain ⟨r, h₁, h₂⟩ := evaluate_ok x req es
    obtain ⟨rs, h₃, h₄⟩ := evaluate_list_ok xs req es
    simp only [h₁, Std.bind_ok, Exprs.toSpec, _root_.List.mapM_cons, ← h₂]
    cases r with
    | Err e => simp
    | Ok v =>
      simp only [h₃, Std.bind_ok, ← h₄, Result.toSpec_Ok, Except.bind_ok]
      cases rs <;> simp

theorem evaluate_attrs_ok (axs : value.List (value.List Char × expr.Expr)) (req : request.Request)
    (es : value.List (value.EntityUID × entities.EntityData)) :
    ∃ r, evaluator.evaluate_attrs axs req es = ok r ∧
      Result.toSpec Attrs.toSpec r =
        (AttrExprs.toSpec axs).mapM (fun (ax : Attr × Cedar.Spec.Expr) =>
          bindAttr ax.fst (Cedar.Spec.evaluate ax.snd (Request.toSpec req) (Entities.toSpec es))) := by
  match axs with
  | .Nil => rw [evaluator.evaluate_attrs.eq_def]; simp [AttrExprs.toSpec]
  | .Cons (a, x) axs =>
    rw [evaluator.evaluate_attrs.eq_def]
    obtain ⟨r, h₁, h₂⟩ := evaluate_ok x req es
    obtain ⟨rs, h₃, h₄⟩ := evaluate_attrs_ok axs req es
    simp only [AttrExprs.toSpec, _root_.List.mapM_cons, ← h₂, ← h₄]
    cases r <;> cases rs <;> simp [h₁, h₃, clone_str_ok, bindAttr_ok, bindAttr_error]

end

end -- public section

end CedarRustModel
