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

import Cedar.Spec.CST.Evaluator
import Cedar.Spec.CST.Translation
import Cedar.Spec.Evaluator
import Cedar.Spec.Authorizer
import Cedar.Thm.Data.Control
import Cedar.Thm.Data.List.Lemmas

/-! This file proves that CST evaluation is equivalent to translating to AST
    and then evaluating. The central theorem is `cst_evaluate_eq_evaluate_toExpr`. -/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Spec.CST
open Cedar.Data

-- Coercion simp lemma: Value → Result Bool is Value.asBool
@[simp] private theorem coe_value_result_bool :
    @Coe.coe Value (Result Bool) instCoeValueResultBool = Value.asBool := rfl

/-- Bind on Except.error propagates the error -/
@[simp] private theorem except_error_bind {α β : Type} {err : Error} {f : α → Except Error β} :
    Except.error err >>= f = Except.error err := rfl

/-- Evaluate .or when first arg evaluates to non-bool value -/
private theorem eval_or_nonbool (a b : Spec.Expr) (req : Request) (es : Entities)
    (v : Value) (err : Error)
    (h : Spec.evaluate a req es = .ok v)
    (hbv : Value.asBool v = .error err) :
    Spec.evaluate (.or a b) req es = .error err := by
  unfold Spec.evaluate; rw [h]; change (do let b₁ ← Value.asBool v; _) = _; rw [hbv]; rfl

/-- Evaluate .and when first arg evaluates to non-bool value -/
private theorem eval_and_nonbool (a b : Spec.Expr) (req : Request) (es : Entities)
    (v : Value) (err : Error)
    (h : Spec.evaluate a req es = .ok v)
    (hbv : Value.asBool v = .error err) :
    Spec.evaluate (.and a b) req es = .error err := by
  unfold Spec.evaluate; rw [h]; change (do let b₁ ← Value.asBool v; _) = _; rw [hbv]; rfl

/-- If asBool succeeds, the value was a bool prim -/
theorem asBool_ok {v : Value} {b : Bool} (h : Value.asBool v = .ok b) :
    v = .prim (.bool b) := by
  cases v with
  | prim p => cases p with
    | bool b' => simp [Value.asBool] at h; subst h; rfl
    | _ => simp [Value.asBool] at h
  | _ => simp [Value.asBool] at h

private theorem eval_or_true (a b : Spec.Expr) (req : Request) (es : Entities)
    (h : Spec.evaluate a req es = .ok (.prim (.bool true))) :
    Spec.evaluate (.or a b) req es = .ok (.prim (.bool true)) := by
  unfold Spec.evaluate; rw [h]; rfl

private theorem eval_or_error (a b : Spec.Expr) (req : Request) (es : Entities)
    (err : Error) (h : Spec.evaluate a req es = .error err) :
    Spec.evaluate (.or a b) req es = .error err := by
  unfold Spec.evaluate; rw [h]; rfl

private theorem eval_and_false (a b : Spec.Expr) (req : Request) (es : Entities)
    (h : Spec.evaluate a req es = .ok (.prim (.bool false))) :
    Spec.evaluate (.and a b) req es = .ok (.prim (.bool false)) := by
  unfold Spec.evaluate; rw [h]; rfl

private theorem eval_and_error (a b : Spec.Expr) (req : Request) (es : Entities)
    (err : Error) (h : Spec.evaluate a req es = .error err) :
    Spec.evaluate (.and a b) req es = .error err := by
  unfold Spec.evaluate; rw [h]; rfl

/-- .or when first is false, second evaluates to .ok v with asBool v = .ok b' -/
private theorem eval_or_false_ok (a eE : Spec.Expr) (req : Request) (es : Entities)
    (v : Value) (b' : Bool)
    (h_acc : Spec.evaluate a req es = .ok (.prim (.bool false)))
    (hev : Spec.evaluate eE req es = .ok v)
    (hbv : Value.asBool v = .ok b') :
    Spec.evaluate (.or a eE) req es = .ok (.prim (.bool b')) := by
  have hv := asBool_ok hbv; subst hv
  simp only [Spec.evaluate, h_acc, Result.as]; rw [hev]
  simp [Value.asBool, Functor.map, Except.map]

/-- .or when first is false, second errors -/
private theorem eval_or_false_err (a eE : Spec.Expr) (req : Request) (es : Entities)
    (err : Error)
    (h_acc : Spec.evaluate a req es = .ok (.prim (.bool false)))
    (hev : Spec.evaluate eE req es = .error err) :
    Spec.evaluate (.or a eE) req es = .error err := by
  simp only [Spec.evaluate, h_acc, Result.as]; rw [hev]; rfl

/-- .or when first is false, second has non-bool value -/
private theorem eval_or_false_nonbool (a eE : Spec.Expr) (req : Request) (es : Entities)
    (v : Value) (err : Error)
    (h_acc : Spec.evaluate a req es = .ok (.prim (.bool false)))
    (hev : Spec.evaluate eE req es = .ok v)
    (hbv : Value.asBool v = .error err) :
    Spec.evaluate (.or a eE) req es = .error err := by
  simp only [Spec.evaluate, h_acc, Result.as]; rw [hev]
  simp [hbv, Functor.map, Except.map]; rfl

/-- .and when first is true, second evaluates to .ok v with asBool v = .ok b' -/
private theorem eval_and_true_ok (a eE : Spec.Expr) (req : Request) (es : Entities)
    (v : Value) (b' : Bool)
    (h_acc : Spec.evaluate a req es = .ok (.prim (.bool true)))
    (hev : Spec.evaluate eE req es = .ok v)
    (hbv : Value.asBool v = .ok b') :
    Spec.evaluate (.and a eE) req es = .ok (.prim (.bool b')) := by
  have hv := asBool_ok hbv; subst hv
  simp only [Spec.evaluate, h_acc, Result.as]; rw [hev]
  simp [Value.asBool, Functor.map, Except.map]

/-- .and when first is true, second errors -/
private theorem eval_and_true_err (a eE : Spec.Expr) (req : Request) (es : Entities)
    (err : Error)
    (h_acc : Spec.evaluate a req es = .ok (.prim (.bool true)))
    (hev : Spec.evaluate eE req es = .error err) :
    Spec.evaluate (.and a eE) req es = .error err := by
  simp only [Spec.evaluate, h_acc, Result.as]; rw [hev]; rfl

/-- .and when first is true, second has non-bool value -/
private theorem eval_and_true_nonbool (a eE : Spec.Expr) (req : Request) (es : Entities)
    (v : Value) (err : Error)
    (h_acc : Spec.evaluate a req es = .ok (.prim (.bool true)))
    (hev : Spec.evaluate eE req es = .ok v)
    (hbv : Value.asBool v = .error err) :
    Spec.evaluate (.and a eE) req es = .error err := by
  simp only [Spec.evaluate, h_acc, Result.as]; rw [hev]
  simp [hbv, Functor.map, Except.map]; rfl

theorem foldOr_error (req : Request) (es : Entities)
    (accE : Spec.Expr) (exts : List Spec.Expr) (err : Error)
    (h : Spec.evaluate accE req es = .error err) :
    Spec.evaluate (CST.foldOr accE exts) req es = .error err := by
  induction exts generalizing accE with
  | nil => exact h
  | cons e rest ih => exact ih _ (eval_or_error accE e req es err h)

theorem foldAnd_error (req : Request) (es : Entities)
    (accE : Spec.Expr) (exts : List Spec.Expr) (err : Error)
    (h : Spec.evaluate accE req es = .error err) :
    Spec.evaluate (CST.foldAnd accE exts) req es = .error err := by
  induction exts generalizing accE with
  | nil => exact h
  | cons e rest ih => exact ih _ (eval_and_error accE e req es err h)

theorem foldOr_true (req : Request) (es : Entities)
    (accE : Spec.Expr) (exts : List Spec.Expr)
    (h : Spec.evaluate accE req es = .ok (.prim (.bool true))) :
    Spec.evaluate (CST.foldOr accE exts) req es = .ok (.prim (.bool true)) := by
  induction exts generalizing accE with
  | nil => exact h
  | cons e rest ih => exact ih _ (eval_or_true accE e req es h)

theorem foldAnd_false (req : Request) (es : Entities)
    (accE : Spec.Expr) (exts : List Spec.Expr)
    (h : Spec.evaluate accE req es = .ok (.prim (.bool false))) :
    Spec.evaluate (CST.foldAnd accE exts) req es = .ok (.prim (.bool false)) := by
  induction exts generalizing accE with
  | nil => exact h
  | cons e rest ih => exact ih _ (eval_and_false accE e req es h)

/-- evaluateOrChain on false cons -/
private theorem orChain_false_cons (req : Request) (es : Entities)
    (e : CST.Expr) (rest : List CST.Expr) :
    CST.evaluateOrChain req es (.prim (.bool false)) (e :: rest) =
    (do let v ← CST.Expr.evaluate e req es
        let _ ← Result.as Bool (.ok v)
        evaluateOrChain req es v rest) := by
  simp only [evaluateOrChain]; rfl

/-- evaluateOrChain on true cons -/
private theorem orChain_true_cons (req : Request) (es : Entities)
    (e : CST.Expr) (rest : List CST.Expr) :
    CST.evaluateOrChain req es (.prim (.bool true)) (e :: rest) =
    .ok (.prim (.bool true)) := by
  simp only [evaluateOrChain]; rfl

/-- evaluateAndChain on true cons -/
private theorem andChain_true_cons (req : Request) (es : Entities)
    (e : CST.Expr) (rest : List CST.Expr) :
    CST.evaluateAndChain req es (.prim (.bool true)) (e :: rest) =
    (do let v ← CST.Expr.evaluate e req es
        let _ ← Result.as Bool (.ok v)
        evaluateAndChain req es v rest) := by
  simp only [evaluateAndChain]; rfl

/-- evaluateAndChain on false cons -/
private theorem andChain_false_cons (req : Request) (es : Entities)
    (e : CST.Expr) (rest : List CST.Expr) :
    CST.evaluateAndChain req es (.prim (.bool false)) (e :: rest) =
    .ok (.prim (.bool false)) := by
  simp only [evaluateAndChain]; rfl

/-- Result.as Bool on .ok v is Value.asBool v -/
@[simp] private theorem result_as_ok (v : Value) :
    Result.as Bool (.ok v : Result Value) = Value.asBool v := rfl

/-- Or chain equivalence -/
theorem evaluateOrChain_eq_foldOr
    (req : Request) (es : Entities)
    (b : Bool) (accE : Spec.Expr)
    (exts : List CST.Expr)
    (h_acc : Spec.evaluate accE req es = .ok (.prim (.bool b)))
    (h_ih : ∀ e, e ∈ exts → e.evaluate req es = Spec.evaluate (e.toExpr) req es) :
    CST.evaluateOrChain req es (.prim (.bool b)) exts =
    Spec.evaluate (CST.foldOr accE (exts.map CST.Expr.toExpr)) req es := by
  induction exts generalizing b accE with
  | nil =>
    simp only [evaluateOrChain, foldOr, List.map]
    exact h_acc.symm
  | cons e rest ih =>
    have h_e := h_ih e (.head ..)
    have h_rest : ∀ e', e' ∈ rest → e'.evaluate req es = Spec.evaluate (e'.toExpr) req es :=
      fun e' h => h_ih e' (.tail _ h)
    simp only [foldOr, List.map]
    cases b with
    | true =>
      rw [orChain_true_cons]
      exact (foldOr_true req es _ _ (eval_or_true accE _ req es h_acc)).symm
    | false =>
      -- Rewrite the LHS to use the chain reduction and the IH for e
      have h_lhs : CST.evaluateOrChain req es (.prim (.bool false)) (e :: rest) =
        (do let v ← Spec.evaluate (CST.Expr.toExpr e) req es
            let _ ← Result.as Bool (.ok v)
            evaluateOrChain req es v rest) := by
        simp only [evaluateOrChain]; rw [h_e]; rfl
      rw [h_lhs]
      -- Now split on the evaluation of e
      generalize hev : Spec.evaluate (CST.Expr.toExpr e) req es = res
      cases res with
      | error err =>
        simp only []
        exact (foldOr_error req es _ _ err
          (eval_or_false_err accE _ req es err h_acc hev)).symm
      | ok v =>
        -- After generalize + cases ok, the LHS is:
        -- do let v ← .ok v; let _ ← Result.as Bool (.ok v); evaluateOrChain req es v rest
        -- which reduces to: do let _ ← Result.as Bool (.ok v); evaluateOrChain req es v rest
        -- which is: do let _ ← Value.asBool v; evaluateOrChain req es v rest
        change (do let _ ← Value.asBool v; evaluateOrChain req es v rest) = _
        cases hbv : Value.asBool v with
        | error err =>
          simp only []
          exact (foldOr_error req es _ _ err
            (eval_or_false_nonbool accE _ req es v err h_acc hev hbv)).symm
        | ok b' =>
          simp only []
          have hv := asBool_ok hbv; subst hv
          exact ih b' _ (eval_or_false_ok accE _ req es _ b' h_acc hev hbv) h_rest

/-- And chain equivalence -/
theorem evaluateAndChain_eq_foldAnd
    (req : Request) (es : Entities)
    (b : Bool) (accE : Spec.Expr)
    (exts : List CST.Expr)
    (h_acc : Spec.evaluate accE req es = .ok (.prim (.bool b)))
    (h_ih : ∀ e, e ∈ exts → e.evaluate req es = Spec.evaluate (e.toExpr) req es) :
    CST.evaluateAndChain req es (.prim (.bool b)) exts =
    Spec.evaluate (CST.foldAnd accE (exts.map CST.Expr.toExpr)) req es := by
  induction exts generalizing b accE with
  | nil =>
    simp only [evaluateAndChain, foldAnd, List.map]
    exact h_acc.symm
  | cons e rest ih =>
    have h_e := h_ih e (.head ..)
    have h_rest : ∀ e', e' ∈ rest → e'.evaluate req es = Spec.evaluate (e'.toExpr) req es :=
      fun e' h => h_ih e' (.tail _ h)
    simp only [foldAnd, List.map]
    cases b with
    | false =>
      rw [andChain_false_cons]
      exact (foldAnd_false req es _ _ (eval_and_false accE _ req es h_acc)).symm
    | true =>
      have h_lhs : CST.evaluateAndChain req es (.prim (.bool true)) (e :: rest) =
        (do let v ← Spec.evaluate (CST.Expr.toExpr e) req es
            let _ ← Result.as Bool (.ok v)
            evaluateAndChain req es v rest) := by
        simp only [evaluateAndChain]; rw [h_e]; rfl
      rw [h_lhs]
      generalize hev : Spec.evaluate (CST.Expr.toExpr e) req es = res
      cases res with
      | error err =>
        simp only []
        exact (foldAnd_error req es _ _ err
          (eval_and_true_err accE _ req es err h_acc hev)).symm
      | ok v =>
        change (do let _ ← Value.asBool v; evaluateAndChain req es v rest) = _
        cases hbv : Value.asBool v with
        | error err =>
          simp only []
          exact (foldAnd_error req es _ _ err
            (eval_and_true_nonbool accE _ req es v err h_acc hev hbv)).symm
        | ok b' =>
          simp only []
          have hv := asBool_ok hbv; subst hv
          exact ih b' _ (eval_and_true_ok accE _ req es _ b' h_acc hev hbv) h_rest

/-- Unary ops chain equivalence: evalUnaryOps on a value equals evaluating
    applyUnaryOps on the AST expression, given the expression evaluates to that value. -/
theorem evalUnaryOps_eq
    (ops : List CST.UnaryOp) (v : Value) (e : Spec.Expr)
    (req : Request) (es : Entities)
    (h : Spec.evaluate e req es = .ok v) :
    CST.evalUnaryOps ops v =
    Spec.evaluate (CST.applyUnaryOps ops e) req es := by
  induction ops with
  | nil =>
    simp only [CST.evalUnaryOps, CST.applyUnaryOps]
    exact h.symm
  | cons op rest ih =>
    cases op with
    | not =>
      simp only [CST.evalUnaryOps, CST.applyUnaryOps]
      unfold Spec.evaluate
      rw [← ih]
    | neg =>
      simp only [CST.evalUnaryOps, CST.applyUnaryOps]
      unfold Spec.evaluate
      rw [← ih]

/-- hasAttr always returns a boolean value or an error -/
private theorem hasAttr_returns_bool (v : Value) (a : Attr) (es : Entities) :
    (∃ b : Bool, Spec.hasAttr v a es = .ok (.prim (.bool b))) ∨
    (∃ err : Error, Spec.hasAttr v a es = .error err) := by
  unfold Spec.hasAttr Spec.attrsOf
  cases v with
  | prim p =>
    cases p with
    | entityUID uid => left; exact ⟨_, rfl⟩
    | _ => right; exact ⟨.typeError, rfl⟩
  | set _ => right; exact ⟨.typeError, rfl⟩
  | ext _ => right; exact ⟨.typeError, rfl⟩
  | record r => left; exact ⟨_, rfl⟩

/-- evaluateExtendedHas always returns a boolean value or an error -/
private theorem evaluateExtendedHas_returns_bool
    (base : Value) (es : Entities) (attrs : List Attr) :
    (∃ b : Bool, CST.evaluateExtendedHas base es attrs = .ok (.prim (.bool b))) ∨
    (∃ err : Error, CST.evaluateExtendedHas base es attrs = .error err) := by
  induction attrs generalizing base with
  | nil => left; exact ⟨true, rfl⟩
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [CST.evaluateExtendedHas]
      exact hasAttr_returns_bool base a es
    | cons a' rest' =>
      -- evaluateExtendedHas base es (a :: a' :: rest')
      -- = do let b ← (hasAttr base a es).as Bool
      --      if !b then .ok false else do let v ← getAttr base a es; evaluateExtendedHas v es (a' :: rest')
      cases hha : Spec.hasAttr base a es with
      | error err =>
        right; exact ⟨err, by simp only [CST.evaluateExtendedHas]; rw [hha]; rfl⟩
      | ok hasVal =>
        have h_bool := hasAttr_returns_bool base a es
        -- hasVal must be a boolean since hasAttr succeeded
        have h_is_bool : ∃ b : Bool, hasVal = Value.prim (.bool b) := by
          cases h_bool with
          | inl hb =>
            obtain ⟨b, hb⟩ := hb; rw [hha] at hb
            exact ⟨b, by injection hb⟩
          | inr he =>
            obtain ⟨err, he⟩ := he; rw [hha] at he; cases he
        obtain ⟨bval, hval⟩ := h_is_bool; subst hval
        cases bval with
        | false =>
          left; exact ⟨false, by simp only [CST.evaluateExtendedHas]; rw [hha]; rfl⟩
        | true =>
          cases hga : Spec.getAttr base a es with
          | error err =>
            right; exact ⟨err, by simp only [CST.evaluateExtendedHas]; rw [hha, hga]; rfl⟩
          | ok getVal =>
            have : CST.evaluateExtendedHas base es (a :: a' :: rest') =
                CST.evaluateExtendedHas getVal es (a' :: rest') := by
              simp only [CST.evaluateExtendedHas]; rw [hha, hga]; rfl
            rw [this]; exact ih getVal

/-- For a Result Value that is a boolean or error, the .as Bool coercion roundtrip is identity -/
private theorem result_as_bool_pure_roundtrip (r : Result Value)
    (h : (∃ b : Bool, r = .ok (.prim (.bool b))) ∨ (∃ err : Error, r = .error err)) :
    (do let b ← r.as Bool; .ok (.prim (.bool b) : Value)) = r := by
  cases h with
  | inl hb => obtain ⟨b, hb⟩ := hb; subst hb; rfl
  | inr he => obtain ⟨err, he⟩ := he; subst he; rfl

/-- Helper: evaluating .hasAttr baseE a when baseE evaluates to base -/
private theorem eval_hasAttr_base (baseE : Spec.Expr) (a : Attr)
    (req : Request) (es : Entities) (base : Value)
    (h : Spec.evaluate baseE req es = .ok base) :
    Spec.evaluate (.hasAttr baseE a) req es = Spec.hasAttr base a es := by
  unfold Spec.evaluate; rw [h]; rfl

/-- Helper: evaluating .getAttr baseE a when baseE evaluates to base -/
private theorem eval_getAttr_base (baseE : Spec.Expr) (a : Attr)
    (req : Request) (es : Entities) (base : Value)
    (h : Spec.evaluate baseE req es = .ok base) :
    Spec.evaluate (.getAttr baseE a) req es = Spec.getAttr base a es := by
  unfold Spec.evaluate; rw [h]; rfl

/-- Helper: evaluating translateExtendedHas when the base expression errors propagates the error -/
private theorem eval_translateExtendedHas_error
    (baseE : Spec.Expr) (req : Request) (es : Entities)
    (a : Attr) (attrs : List Attr) (err : Error)
    (h : Spec.evaluate baseE req es = .error err) :
    Spec.evaluate (CST.translateExtendedHas baseE (a :: attrs)) req es = .error err := by
  cases attrs with
  | nil =>
    simp only [CST.translateExtendedHas]
    unfold Spec.evaluate; rw [h]; rfl
  | cons a' rest' =>
    simp only [CST.translateExtendedHas]
    exact eval_and_error _ _ req es err (by unfold Spec.evaluate; rw [h]; rfl)

/-- Extended has equivalence: evaluateExtendedHas on a value equals evaluating
    translateExtendedHas on the AST expression, given the expression evaluates to that value. -/
theorem evaluateExtendedHas_eq_translateExtendedHas
    (base : Value) (baseE : Spec.Expr)
    (req : Request) (es : Entities)
    (attrs : List Attr)
    (h : Spec.evaluate baseE req es = .ok base) :
    CST.evaluateExtendedHas base es attrs =
    Spec.evaluate (CST.translateExtendedHas baseE attrs) req es := by
  induction attrs generalizing base baseE with
  | nil =>
    simp only [CST.evaluateExtendedHas, CST.translateExtendedHas]
    unfold Spec.evaluate; rfl
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [CST.evaluateExtendedHas, CST.translateExtendedHas]
      rw [eval_hasAttr_base baseE a req es base h]
    | cons a' rest' =>
      have h_hasattr := eval_hasAttr_base baseE a req es base h
      have h_getattr := eval_getAttr_base baseE a req es base h
      -- Case split on hasAttr base a es
      cases hha : Spec.hasAttr base a es with
      | error err =>
        -- LHS: evaluateExtendedHas errors through .as Bool on hasAttr
        have h_lhs : CST.evaluateExtendedHas base es (a :: a' :: rest') = .error err := by
          simp only [CST.evaluateExtendedHas]
          show (do let b ← (Spec.hasAttr base a es).as Bool
                   if !b then .ok (Value.prim (.bool false))
                   else do let v ← Spec.getAttr base a es
                           CST.evaluateExtendedHas v es (a' :: rest')) = .error err
          rw [hha]; rfl
        rw [h_lhs]
        -- RHS: evaluate (.and ...) errors because first operand errors
        simp only [CST.translateExtendedHas]
        exact (eval_and_error _ _ req es err (by rw [h_hasattr, hha])).symm
      | ok hasVal =>
        -- hasAttr always returns a boolean
        have h_bool := hasAttr_returns_bool base a es
        have h_is_bool : ∃ b : Bool, hasVal = Value.prim (.bool b) := by
          cases h_bool with
          | inl hb =>
            obtain ⟨b, hb⟩ := hb
            rw [hha] at hb; exact ⟨b, by injection hb⟩
          | inr he =>
            obtain ⟨err, he⟩ := he
            rw [hha] at he; cases he
        obtain ⟨bval, hval⟩ := h_is_bool; subst hval
        cases bval with
        | false =>
          -- hasAttr returned false — both sides short-circuit to .ok false
          have : CST.evaluateExtendedHas base es (a :: a' :: rest') = .ok (.prim (.bool false)) := by
            simp only [CST.evaluateExtendedHas, hha, Result.as]
            rfl
          rw [this]
          simp only [CST.translateExtendedHas]
          exact (eval_and_false _ _ req es (by rw [h_hasattr, hha])).symm
        | true =>
          -- hasAttr returned true — continue to getAttr and recursive call
          have h_hasattr_true : Spec.evaluate (.hasAttr baseE a) req es = .ok (.prim (.bool true)) := by
            rw [h_hasattr, hha]
          cases hga : Spec.getAttr base a es with
          | error err =>
            -- getAttr failed
            have : CST.evaluateExtendedHas base es (a :: a' :: rest') = .error err := by
              simp only [CST.evaluateExtendedHas, hha, Result.as, hga]
              rfl
            rw [this]
            simp only [CST.translateExtendedHas]
            have h_getattr_err : Spec.evaluate (.getAttr baseE a) req es = .error err := by
              rw [h_getattr, hga]
            exact (eval_and_true_err _ _ req es err h_hasattr_true
              (eval_translateExtendedHas_error _ req es a' rest' err h_getattr_err)).symm
          | ok getVal =>
            -- getAttr succeeded — LHS reduces to evaluateExtendedHas getVal es (a' :: rest')
            have h_lhs : CST.evaluateExtendedHas base es (a :: a' :: rest') =
                CST.evaluateExtendedHas getVal es (a' :: rest') := by
              simp only [CST.evaluateExtendedHas, hha, Result.as, hga]
              rfl
            rw [h_lhs]
            have h_getattr_ok : Spec.evaluate (.getAttr baseE a) req es = .ok getVal := by
              rw [h_getattr, hga]
            rw [ih getVal (.getAttr baseE a) h_getattr_ok]
            -- Goal: evaluate (translateExtendedHas (.getAttr baseE a) (a' :: rest')) req es =
            --   evaluate (translateExtendedHas baseE (a :: a' :: rest')) req es
            -- = evaluate (.and (.hasAttr baseE a) (translateExtendedHas (.getAttr baseE a) (a' :: rest'))) req es
            simp only [CST.translateExtendedHas]
            -- Since first operand is true, .and returns (second operand).as Bool
            -- And the second operand always returns a bool
            have h_ext_bool := evaluateExtendedHas_returns_bool getVal es (a' :: rest')
            -- After ih, the goal is:
            -- evaluate (translateExtendedHas (.getAttr baseE a) (a' :: rest')) req es =
            --   evaluate (.and (.hasAttr baseE a) (translateExtendedHas (.getAttr baseE a) (a' :: rest'))) req es
            -- By ih, evaluate (translateExtendedHas ...) = evaluateExtendedHas getVal es (a' :: rest')
            -- And evaluateExtendedHas always returns a bool
            -- So we can use eval_and_true_ok or eval_and_true_err
            symm
            cases h_ext_bool with
            | inl hb =>
              obtain ⟨b, hb⟩ := hb
              rw [ih getVal (.getAttr baseE a) h_getattr_ok] at hb
              rw [hb]
              exact eval_and_true_ok _ _ req es _ b h_hasattr_true hb (by rfl)
            | inr he =>
              obtain ⟨err, he⟩ := he
              rw [ih getVal (.getAttr baseE a) h_getattr_ok] at he
              rw [he]
              exact eval_and_true_err _ _ req es err h_hasattr_true he

/-- Helper: evaluating a binary app when both sides evaluate to known values -/
private theorem eval_binaryApp (op : BinaryOp) (e₁ e₂ : Spec.Expr)
    (req : Request) (es : Entities) (v₁ v₂ : Value)
    (h₁ : Spec.evaluate e₁ req es = .ok v₁)
    (h₂ : Spec.evaluate e₂ req es = .ok v₂) :
    Spec.evaluate (.binaryApp op e₁ e₂) req es = apply₂ op v₁ v₂ es := by
  unfold Spec.evaluate; rw [h₁, h₂]; rfl

/-- Helper: foldAdd propagates errors -/
private theorem foldAdd_error (req : Request) (es : Entities)
    (accE : Spec.Expr) (exts : List (CST.AddOp × Spec.Expr)) (err : Error)
    (h : Spec.evaluate accE req es = .error err) :
    Spec.evaluate (CST.foldAdd accE exts) req es = .error err := by
  induction exts generalizing accE with
  | nil => exact h
  | cons p rest ih =>
    cases p with
    | mk op e =>
      cases op with
      | plus =>
        simp only [CST.foldAdd]
        exact ih _ (by unfold Spec.evaluate; rw [h]; rfl)
      | minus =>
        simp only [CST.foldAdd]
        exact ih _ (by unfold Spec.evaluate; rw [h]; rfl)


/-- Helper: foldMult propagates errors -/
private theorem foldMult_error (req : Request) (es : Entities)
    (accE : Spec.Expr) (exts : List Spec.Expr) (err : Error)
    (h : Spec.evaluate accE req es = .error err) :
    Spec.evaluate (CST.foldMult accE exts) req es = .error err := by
  induction exts generalizing accE with
  | nil => exact h
  | cons e rest ih =>
    simp only [CST.foldMult]
    exact ih _ (by unfold Spec.evaluate; rw [h]; rfl)

/-- Evaluate .binaryApp when both args evaluate successfully -/
private theorem eval_binaryApp_ok (op : BinaryOp) (a b : Spec.Expr)
    (req : Request) (es : Entities) (v₁ v₂ : Value)
    (h₁ : Spec.evaluate a req es = .ok v₁)
    (h₂ : Spec.evaluate b req es = .ok v₂) :
    Spec.evaluate (.binaryApp op a b) req es = apply₂ op v₁ v₂ es := by
  unfold Spec.evaluate; rw [h₁, h₂]; rfl

/-- Evaluate .binaryApp when first ok, second errors -/
private theorem eval_binaryApp_err2 (op : BinaryOp) (a b : Spec.Expr)
    (req : Request) (es : Entities) (v₁ : Value) (err : Error)
    (h₁ : Spec.evaluate a req es = .ok v₁)
    (h₂ : Spec.evaluate b req es = .error err) :
    Spec.evaluate (.binaryApp op a b) req es = .error err := by
  unfold Spec.evaluate; rw [h₁, h₂]; rfl

/-- Add chain equivalence -/
theorem evaluateAddChain_eq_foldAdd
    (req : Request) (es : Entities)
    (acc : Value) (accE : Spec.Expr)
    (exts : List (CST.AddOp × CST.Expr))
    (h_acc : Spec.evaluate accE req es = .ok acc)
    (h_ih : ∀ p, p ∈ exts → p.2.evaluate req es = Spec.evaluate (p.2.toExpr) req es) :
    CST.evaluateAddChain req es acc exts =
    Spec.evaluate (CST.foldAdd accE (exts.map (fun (op, e) => (op, e.toExpr)))) req es := by
  induction exts generalizing acc accE with
  | nil => simp only [CST.evaluateAddChain, CST.foldAdd, List.map]; exact h_acc.symm
  | cons p rest ih =>
    obtain ⟨op, e⟩ := p
    have h_e : e.evaluate req es = Spec.evaluate (e.toExpr) req es := h_ih (op, e) (.head ..)
    have h_rest : ∀ p', p' ∈ rest → p'.2.evaluate req es = Spec.evaluate (p'.2.toExpr) req es :=
      fun p' h => h_ih p' (.tail _ h)
    cases op with
    | plus =>
      -- LHS: evaluateAddChain req es acc ((.plus, e) :: rest)
      --    = do let v ← e.evaluate req es; let r ← apply₂ .add acc v es; evaluateAddChain req es r rest
      -- After rw [h_e]: ... ← Spec.evaluate e.toExpr req es ...
      have h_lhs : CST.evaluateAddChain req es acc ((.plus, e) :: rest) =
        (do let v ← Spec.evaluate e.toExpr req es
            let r ← apply₂ .add acc v es
            evaluateAddChain req es r rest) := by
        simp only [evaluateAddChain]; rw [h_e]
      rw [h_lhs]; simp only [CST.foldAdd, List.map]
      generalize hev : Spec.evaluate e.toExpr req es = res
      cases res with
      | error err =>
        exact (foldAdd_error req es _ _ err
          (eval_binaryApp_err2 .add accE _ req es acc err h_acc hev)).symm
      | ok v =>
        change (do let r ← apply₂ .add acc v es; evaluateAddChain req es r rest) = _
        generalize happ : apply₂ .add acc v es = res2
        cases res2 with
        | error err =>
          exact (foldAdd_error req es _ _ err
            (by rw [eval_binaryApp_ok .add accE _ req es acc v h_acc hev, happ])).symm
        | ok r =>
          change evaluateAddChain req es r rest = _
          exact ih r _ (by rw [eval_binaryApp_ok .add accE _ req es acc v h_acc hev, happ]) h_rest
    | minus =>
      have h_lhs : CST.evaluateAddChain req es acc ((.minus, e) :: rest) =
        (do let v ← Spec.evaluate e.toExpr req es
            let r ← apply₂ .sub acc v es
            evaluateAddChain req es r rest) := by
        simp only [evaluateAddChain]; rw [h_e]
      rw [h_lhs]; simp only [CST.foldAdd, List.map]
      generalize hev : Spec.evaluate e.toExpr req es = res
      cases res with
      | error err =>
        exact (foldAdd_error req es _ _ err
          (eval_binaryApp_err2 .sub accE _ req es acc err h_acc hev)).symm
      | ok v =>
        change (do let r ← apply₂ .sub acc v es; evaluateAddChain req es r rest) = _
        generalize happ : apply₂ .sub acc v es = res2
        cases res2 with
        | error err =>
          exact (foldAdd_error req es _ _ err
            (by rw [eval_binaryApp_ok .sub accE _ req es acc v h_acc hev, happ])).symm
        | ok r =>
          change evaluateAddChain req es r rest = _
          exact ih r _ (by rw [eval_binaryApp_ok .sub accE _ req es acc v h_acc hev, happ]) h_rest

/-- Mult chain equivalence -/
theorem evaluateMultChain_eq_foldMult
    (req : Request) (es : Entities)
    (acc : Value) (accE : Spec.Expr)
    (exts : List CST.Expr)
    (h_acc : Spec.evaluate accE req es = .ok acc)
    (h_ih : ∀ e, e ∈ exts → e.evaluate req es = Spec.evaluate (e.toExpr) req es) :
    CST.evaluateMultChain req es acc exts =
    Spec.evaluate (CST.foldMult accE (exts.map CST.Expr.toExpr)) req es := by
  induction exts generalizing acc accE with
  | nil => simp only [CST.evaluateMultChain, CST.foldMult, List.map]; exact h_acc.symm
  | cons e rest ih =>
    have h_e := h_ih e (.head ..)
    have h_rest : ∀ e', e' ∈ rest → e'.evaluate req es = Spec.evaluate (e'.toExpr) req es :=
      fun e' h => h_ih e' (.tail _ h)
    have h_lhs : CST.evaluateMultChain req es acc (e :: rest) =
      (do let v ← Spec.evaluate e.toExpr req es
          let r ← apply₂ .mul acc v es
          evaluateMultChain req es r rest) := by
      simp only [evaluateMultChain]; rw [h_e]
    rw [h_lhs]; simp only [CST.foldMult, List.map]
    generalize hev : Spec.evaluate e.toExpr req es = res
    cases res with
    | error err =>
      exact (foldMult_error req es _ _ err
        (eval_binaryApp_err2 .mul accE _ req es acc err h_acc hev)).symm
    | ok v =>
      change (do let r ← apply₂ .mul acc v es; evaluateMultChain req es r rest) = _
      generalize happ : apply₂ .mul acc v es = res2
      cases res2 with
      | error err =>
        exact (foldMult_error req es _ _ err
          (by rw [eval_binaryApp_ok .mul accE _ req es acc v h_acc hev, happ])).symm
      | ok r =>
        change evaluateMultChain req es r rest = _
        exact ih r _ (by rw [eval_binaryApp_ok .mul accE _ req es acc v h_acc hev, happ]) h_rest

/-- apply₂ .mem always returns a bool value or an error -/
private theorem apply₂_mem_returns_bool (v₁ v₂ : Value) (es : Entities) :
    (∃ b : Bool, apply₂ .mem v₁ v₂ es = .ok (.prim (.bool b))) ∨
    (∃ err : Error, apply₂ .mem v₁ v₂ es = .error err) := by
  unfold apply₂
  cases v₁ with
  | prim p₁ =>
    cases p₁ with
    | entityUID uid₁ =>
      cases v₂ with
      | prim p₂ =>
        cases p₂ with
        | entityUID uid₂ => left; exact ⟨_, rfl⟩
        | _ => right; exact ⟨.typeError, rfl⟩
      | set vs =>
        simp only [inₛ]
        cases h : Set.mapOrErr Value.asEntityUID vs .typeError with
        | error err => right; simp
        | ok uids => left; simp
      | _ => right; exact ⟨.typeError, rfl⟩
    | _ => right; exact ⟨.typeError, rfl⟩
  | _ => right; exact ⟨.typeError, rfl⟩


/-- Main expression-level equivalence: CST evaluation equals translate-then-AST-evaluate. -/
theorem cst_evaluate_eq_evaluate_toExpr
    (cst : CST.Expr) (req : Request) (es : Entities) :
    cst.evaluate req es = Spec.evaluate (cst.toExpr) req es := by
  match cst with
  | .lit p =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]; unfold Spec.evaluate; rfl
  | .var v =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
  | .ite c t e =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr c,
        cst_evaluate_eq_evaluate_toExpr t,
        cst_evaluate_eq_evaluate_toExpr e]
    simp only [Spec.evaluate]
  | .or init ext =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr init]
    rw [List.map₁_eq_map CST.Expr.toExpr]
    generalize hev : Spec.evaluate init.toExpr req es = res
    cases res with
    | error err => exact (foldOr_error req es _ _ err hev).symm
    | ok v =>
      -- CST: do let v ← .ok v; evaluateOrChain req es v ext
      -- which reduces to: evaluateOrChain req es v ext
      change evaluateOrChain req es v ext = _
      cases ext with
      | nil => simp only [evaluateOrChain, CST.foldOr]; exact hev.symm
      | cons e rest =>
        cases hbv : Value.asBool v with
        | error err =>
          -- evaluateOrChain checks asBool v → error
          have : evaluateOrChain req es v (e :: rest) = .error err := by
            simp only [evaluateOrChain, result_as_ok, hbv]; rfl
          rw [this]
          exact (foldOr_error req es _ _ err
            (eval_or_nonbool init.toExpr _ req es v err hev hbv)).symm
        | ok b =>
          have hv := asBool_ok hbv; subst hv
          exact evaluateOrChain_eq_foldOr req es b _ (e :: rest) hev
            (fun e _ => cst_evaluate_eq_evaluate_toExpr e req es)
  | .and init ext =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr init]
    rw [List.map₁_eq_map CST.Expr.toExpr]
    generalize hev : Spec.evaluate init.toExpr req es = res
    cases res with
    | error err => exact (foldAnd_error req es _ _ err hev).symm
    | ok v =>
      change evaluateAndChain req es v ext = _
      cases ext with
      | nil => simp only [evaluateAndChain, CST.foldAnd]; exact hev.symm
      | cons e rest =>
        cases hbv : Value.asBool v with
        | error err =>
          have : evaluateAndChain req es v (e :: rest) = .error err := by
            simp only [evaluateAndChain, result_as_ok, hbv]; rfl
          rw [this]
          exact (foldAnd_error req es _ _ err
            (eval_and_nonbool init.toExpr _ req es v err hev hbv)).symm
        | ok b =>
          have hv := asBool_ok hbv; subst hv
          exact evaluateAndChain_eq_foldAnd req es b _ (e :: rest) hev
            (fun e _ => cst_evaluate_eq_evaluate_toExpr e req es)
  | .rel op l r =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr l, cst_evaluate_eq_evaluate_toExpr r]
    generalize hl : Spec.evaluate l.toExpr req es = resl
    generalize hr : Spec.evaluate r.toExpr req es = resr
    cases op <;> simp only [CST.evaluateRel, CST.translateRel]
    -- eq
    · unfold Spec.evaluate; rw [hl, hr]
    -- notEq: monad associativity
    · simp only [Spec.evaluate, hl, hr, bind_assoc]
    -- less
    · unfold Spec.evaluate; rw [hl, hr]
    -- lessEq
    · unfold Spec.evaluate; rw [hl, hr]
    -- greater
    · simp only [Spec.evaluate, hl, hr, bind_assoc]
    -- greaterEq
    · simp only [Spec.evaluate, hl, hr, bind_assoc]
    -- mem
    · unfold Spec.evaluate; rw [hl, hr]
  | .has e a =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr e]; simp only [Spec.evaluate]
  | .extendedHas e attrs =>
    cases attrs with
    | nil =>
      -- CST: .ok true, AST: Spec.evaluate (.lit (.bool true)) req es = .ok true
      simp only [CST.Expr.evaluate, CST.Expr.toExpr, CST.translateExtendedHas]
      unfold Spec.evaluate; rfl
    | cons a rest =>
      simp only [CST.Expr.evaluate, CST.Expr.toExpr]
      rw [cst_evaluate_eq_evaluate_toExpr e]
      generalize hev : Spec.evaluate e.toExpr req es = res
      cases res with
      | error err =>
        change Except.error err = _
        exact (eval_translateExtendedHas_error e.toExpr req es a rest err hev).symm
      | ok v => exact evaluateExtendedHas_eq_translateExtendedHas v _ req es (a :: rest) hev
  | .like e p =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr e]; simp only [Spec.evaluate]
  | .is e ety =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr e]; simp only [Spec.evaluate]
  | .isIn e ety inE =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr e, cst_evaluate_eq_evaluate_toExpr inE]
    generalize hev : Spec.evaluate e.toExpr req es = res
    cases res with
    | error err =>
      simp only [Except.bind_err]
      symm; exact eval_and_error _ _ req es err (by unfold Spec.evaluate; rw [hev]; rfl)
    | ok v =>
      simp only [Except.bind_ok]
      -- LHS: do let b ← (apply₁ (.is ety) v).as Bool; if !b then .ok false else do let v₂ ← eval inE.toExpr; apply₂ .mem v v₂ es
      -- RHS: eval (.and (.unaryApp (.is ety) e.toExpr) (.binaryApp .mem e.toExpr inE.toExpr))
      have h_unary : Spec.evaluate (.unaryApp (.is ety) e.toExpr) req es = apply₁ (.is ety) v := by
        unfold Spec.evaluate; rw [hev]; rfl
      cases happ : apply₁ (.is ety) v with
      | error err =>
        simp only [Result.as, Coe.coe, Value.asBool, happ, Except.bind_err]
        symm; exact eval_and_error _ _ req es err (by rw [h_unary, happ])
      | ok isVal =>
        simp only [Result.as, Coe.coe, Value.asBool, happ]
        -- isVal must be a bool since apply₁ (.is ety) returns a bool
        -- apply₁ (.is ety) v = .ok isVal means v = .prim (.entityUID uid) and isVal = .prim (.bool (ety == uid.ty))
        cases v with
        | prim p =>
          cases p with
          | entityUID uid =>
            simp only [apply₁] at happ
            have : isVal = .prim (.bool (ety == uid.ty)) := by injection happ; symm; assumption
            subst this
            simp only [Value.asBool, Except.bind_ok]
            cases h_eq : (ety == uid.ty)
            · -- ety ≠ uid.ty, so is-check returned false
              simp only [Bool.not_false, ↓reduceIte]
              symm; exact eval_and_false _ _ req es (by rw [h_unary]; simp [apply₁, h_eq])
            · -- ety = uid.ty, so is-check returned true
              simp only [Bool.not_true, ↓reduceIte]
              have h_is_true : Spec.evaluate (.unaryApp (.is ety) e.toExpr) req es = .ok (.prim (.bool true)) := by
                rw [h_unary]; simp [apply₁, h_eq]
              generalize hev2 : Spec.evaluate inE.toExpr req es = res3
              cases res3 with
              | error err =>
                simp only [Except.bind_err]
                symm; exact eval_and_true_err _ _ req es err h_is_true
                  (by unfold Spec.evaluate; rw [hev, hev2]; rfl)
              | ok v₂ =>
                simp only [Except.bind_ok]
                have h_mem_eval : Spec.evaluate (.binaryApp .mem e.toExpr inE.toExpr) req es = apply₂ .mem (.prim (.entityUID uid)) v₂ es := by
                  unfold Spec.evaluate; rw [hev, hev2]; rfl
                have h_mem_bool := apply₂_mem_returns_bool (.prim (.entityUID uid)) v₂ es
                cases h_mem_bool with
                | inl hb =>
                  obtain ⟨b', hb'⟩ := hb
                  rw [hb']
                  symm; exact eval_and_true_ok _ _ req es _ b' h_is_true (by rw [h_mem_eval, hb']) (by rfl)
                | inr he =>
                  obtain ⟨err, he⟩ := he
                  rw [he]
                  symm; exact eval_and_true_err _ _ req es err h_is_true (by rw [h_mem_eval, he])
          | _ => simp [apply₁] at happ
        | _ => simp [apply₁] at happ
  | .add init ext =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr init]
    rw [List.map₂_eq_map (fun (p : CST.AddOp × CST.Expr) => (p.1, p.2.toExpr))]
    generalize hev : Spec.evaluate init.toExpr req es = res
    cases res with
    | error err => exact (foldAdd_error req es _ _ err hev).symm
    | ok v =>
      change evaluateAddChain req es v ext = _
      exact evaluateAddChain_eq_foldAdd req es v _ ext hev
        (fun p _ => cst_evaluate_eq_evaluate_toExpr p.2 req es)
  | .mult init ext =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr init]
    rw [List.map₁_eq_map CST.Expr.toExpr]
    generalize hev : Spec.evaluate init.toExpr req es = res
    cases res with
    | error err => exact (foldMult_error req es _ _ err hev).symm
    | ok v =>
      change evaluateMultChain req es v ext = _
      exact evaluateMultChain_eq_foldMult req es v _ ext hev
        (fun e _ => cst_evaluate_eq_evaluate_toExpr e req es)
  | .unary ops e =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr e]
    generalize hev : Spec.evaluate e.toExpr req es = res
    cases res with
    | error err =>
      -- LHS: do let v ← .error err; evalUnaryOps ops v = .error err
      -- RHS: Spec.evaluate (applyUnaryOps ops e.toExpr) req es
      -- Need: applyUnaryOps wraps in unaryApp nodes, each evaluates inner first, so error propagates
      change Except.error err = _
      symm
      induction ops with
      | nil => simp only [CST.applyUnaryOps]; exact hev
      | cons op rest ih =>
        cases op <;> simp only [CST.applyUnaryOps] <;> (unfold Spec.evaluate; rw [ih]; rfl)
    | ok v => exact evalUnaryOps_eq ops v _ req es hev
  | .getAttr e a =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr e]; simp only [Spec.evaluate]
  | .hasAttr e a =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr e]; simp only [Spec.evaluate]
  | .set elems =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [List.mapM₁_eq_mapM (CST.Expr.evaluate · req es) elems,
        List.map₁_eq_map CST.Expr.toExpr]
    simp only [Spec.evaluate, List.mapM₁_eq_mapM (Spec.evaluate · req es)]
    have : elems.mapM (CST.Expr.evaluate · req es) =
           (elems.map CST.Expr.toExpr).mapM (Spec.evaluate · req es) := by
      rw [List.mapM_map]
      exact List.mapM_congr (fun e _ => cst_evaluate_eq_evaluate_toExpr e req es)
    rw [this]
  | .record pairs =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [List.mapM₂_eq_map_snd (CST.Expr.evaluate · req es) (xs := pairs),
        List.map₂_eq_map_snd CST.Expr.toExpr (xs := pairs)]
    simp only [Spec.evaluate,
      List.mapM₂_eq_mapM (fun (x : Attr × Spec.Expr) => bindAttr x.fst (Spec.evaluate x.snd req es))]
    congr 1
    rw [List.mapM_map]
    apply List.mapM_congr
    intro ⟨a, e⟩ _
    simp only [Function.comp, bindAttr]
    rw [cst_evaluate_eq_evaluate_toExpr e req es]
  | .call fn args =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [List.mapM₁_eq_mapM (CST.Expr.evaluate · req es) args,
        List.map₁_eq_map CST.Expr.toExpr]
    simp only [Spec.evaluate, List.mapM₁_eq_mapM (Spec.evaluate · req es)]
    have : args.mapM (CST.Expr.evaluate · req es) =
           (args.map CST.Expr.toExpr).mapM (Spec.evaluate · req es) := by
      rw [List.mapM_map]
      exact List.mapM_congr (fun e _ => cst_evaluate_eq_evaluate_toExpr e req es)
    rw [this]
  | .methodCall recv fn args =>
    simp only [CST.Expr.evaluate, CST.Expr.toExpr]
    rw [cst_evaluate_eq_evaluate_toExpr recv,
        List.mapM₁_eq_mapM (CST.Expr.evaluate · req es) args,
        List.map₁_eq_map CST.Expr.toExpr]
    simp only [Spec.evaluate, List.mapM₁_eq_mapM (Spec.evaluate · req es),
               List.mapM_cons, bind_assoc]
    have : args.mapM (CST.Expr.evaluate · req es) =
           (args.map CST.Expr.toExpr).mapM (Spec.evaluate · req es) := by
      rw [List.mapM_map]
      exact List.mapM_congr (fun e _ => cst_evaluate_eq_evaluate_toExpr e req es)
    rw [this]; grind
termination_by cst
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (rename_i h; have := List.sizeOf_lt_of_mem h; simp at this; omega)
    | -- For pair subterms: the variable p : α × β needs destructuring
      -- so that Prod.mk.sizeOf_spec can fire
      (rename_i h
       have h1 := List.sizeOf_lt_of_mem h
       revert h1; cases ‹_ × _›; simp [Prod.mk.sizeOf_spec]; omega)

/-- Policy translation preserves structure: effect, scopes, and conditions. -/
theorem toPolicy_preserves_structure (cstPol : CST.Policy) :
    (cstPol.toPolicy).effect = cstPol.effect ∧
    (cstPol.toPolicy).principalScope = cstPol.principalScope ∧
    (cstPol.toPolicy).actionScope = cstPol.actionScope ∧
    (cstPol.toPolicy).resourceScope = cstPol.resourceScope ∧
    (cstPol.toPolicy).condition = cstPol.conditions.map CST.Condition.toCondition := by
  simp [CST.Policy.toPolicy]

/-- Each CST condition body, when translated and evaluated, gives the same result
    as evaluating the CST body directly via the CST evaluator. -/
theorem condition_body_equiv (c : CST.Condition) (req : Request) (es : Entities) :
    c.body.evaluate req es = Spec.evaluate (c.toCondition.body) req es := by
  simp only [CST.Condition.toCondition]
  exact cst_evaluate_eq_evaluate_toExpr c.body req es

/-- Each CST condition, when translated to AST, preserves the condition kind
    and correctly translates the body expression. -/
theorem condition_toCondition_body_equiv (c : CST.Condition) (req : Request) (es : Entities) :
    c.body.evaluate req es = Spec.evaluate c.toCondition.body req es :=
  cst_evaluate_eq_evaluate_toExpr c.body req es

/-- The translated policy's satisfaction check is correct: it uses the same
    scopes (shared between CST and AST) and correctly translated condition bodies.
    This follows from `toPolicy_preserves_structure` and `cst_evaluate_eq_evaluate_toExpr`. -/
theorem cst_policy_toPolicy_correct (cstPol : CST.Policy) :
    cstPol.toPolicy.effect = cstPol.effect ∧
    cstPol.toPolicy.id = cstPol.id ∧
    (∀ (c : CST.Condition), c ∈ cstPol.conditions →
      ∀ (req : Request) (es : Entities),
        c.body.evaluate req es = Spec.evaluate (c.toCondition.body) req es) := by
  refine ⟨by simp [CST.Policy.toPolicy], by simp [CST.Policy.toPolicy], ?_⟩
  intro c _ req es
  exact cst_evaluate_eq_evaluate_toExpr c.body req es

/-- CST condition evaluation equals AST condition evaluation after translation -/
theorem condition_evaluate_eq (c : CST.Condition) (req : Request) (es : Entities) :
    c.evaluate req es = Spec.evaluate (c.toCondition.toExpr) req es := by
  cases c with
  | mk kind body =>
    cases kind with
    | when =>
      simp only [CST.Condition.evaluate, CST.Condition.toCondition, Spec.Condition.toExpr]
      exact cst_evaluate_eq_evaluate_toExpr body req es
    | «unless» =>
      simp only [CST.Condition.evaluate, CST.Condition.toCondition, Spec.Condition.toExpr]
      rw [cst_evaluate_eq_evaluate_toExpr body]
      simp only [Spec.evaluate]

/-- Helper: Conditions.toExpr on a non-empty list with at least 2 elements
    equals .and of the first condition with the rest -/
private theorem conditions_toExpr_cons (c : Spec.Condition) (c₂ : Spec.Condition) (rest : List Spec.Condition) :
    Conditions.toExpr (c :: c₂ :: rest) =
    .and (c.toExpr) (Conditions.toExpr (c₂ :: rest)) := by
  unfold Conditions.toExpr
  simp only [List.reverse_cons]
  cases h : rest.reverse ++ [c₂] with
  | nil => simp [List.append_eq_nil_iff] at h
  | cons hd tl =>
    simp only [h, List.cons_append, List.foldl_append, List.foldl]

/-- The .as Bool roundtrip preserves .ok true: a Result Value equals .ok true iff
    the .as Bool coerced version does. -/
private theorem eq_ok_true_iff_as_bool_eq_ok_true (r : Result Value) :
    r = .ok true ↔
    (do let a ← r.as Bool; .ok (.prim (.bool a) : Value)) = .ok true := by
  constructor
  · intro h; subst h; rfl
  · intro h
    cases r with
    | error err => simp [Result.as] at h
    | ok v =>
      cases v with
      | prim p =>
        cases p with
        | bool b => cases b <;> simp [Result.as, Coe.coe, Value.asBool] at h ⊢
        | _ => simp [Result.as, Coe.coe, Value.asBool] at h
      | _ => simp [Result.as, Coe.coe, Value.asBool] at h

/-- If .and evaluates to true and first operand is true, second operand is true -/
private theorem eval_and_true_implies_second_true (x₁ x₂ : Spec.Expr) (req : Request) (es : Entities)
    (h_and : Spec.evaluate (.and x₁ x₂) req es = .ok (.prim (.bool true)))
    (h_fst : Spec.evaluate x₁ req es = .ok (.prim (.bool true))) :
    Spec.evaluate x₂ req es = .ok (.prim (.bool true)) := by
  unfold Spec.evaluate at h_and; rw [h_fst] at h_and
  simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok, Bool.not_true, ↓reduceIte,
             Functor.map, Except.map] at h_and
  cases hev : Spec.evaluate x₂ req es with
  | error err => simp [hev, Result.as, Coe.coe, Value.asBool] at h_and
  | ok v =>
    cases v with
    | prim p =>
      cases p with
      | bool b =>
        simp [hev, Result.as, Coe.coe, Value.asBool] at h_and
        rw [h_and]
      | _ => simp [hev, Result.as, Coe.coe, Value.asBool] at h_and
    | _ => simp [hev, Result.as, Coe.coe, Value.asBool] at h_and

/-- CST conditions evaluation agrees with AST conditions evaluation on .ok true -/
theorem conditions_evaluate_eq_ok_true (cs : List CST.Condition) (req : Request) (es : Entities) :
    CST.Conditions.evaluate cs req es = .ok true ↔
    Spec.evaluate (Conditions.toExpr (cs.map CST.Condition.toCondition)) req es = .ok true := by
  induction cs with
  | nil =>
    simp only [CST.Conditions.evaluate, List.map, Conditions.toExpr, List.reverse_nil]
    unfold Spec.evaluate; simp
  | cons c rest ih =>
    cases rest with
    | nil =>
      simp only [CST.Conditions.evaluate, List.map, Conditions.toExpr, List.reverse_cons,
        List.reverse_nil, List.nil_append, List.foldl]
      rw [condition_evaluate_eq c]
    | cons c₂ rest₂ =>
      simp only [List.map]
      rw [conditions_toExpr_cons]
      simp only [CST.Conditions.evaluate]
      rw [condition_evaluate_eq c]
      generalize hev : Spec.evaluate (CST.Condition.toCondition c).toExpr req es = res
      constructor
      · -- CST .ok true → AST .ok true
        intro h
        cases res with
        | error err => simp [Result.as, Coe.coe, Value.asBool] at h
        | ok v =>
          cases v with
          | prim p =>
            cases p with
            | bool b =>
              simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok] at h
              cases b
              · simp at h
              · simp only [Bool.not_true, ↓reduceIte] at h
                exact eval_and_true_ok _ _ req es _ true (by rw [hev]) (ih.mp h) (by rfl)
            | _ => simp [Result.as, Coe.coe, Value.asBool] at h
          | _ => simp [Result.as, Coe.coe, Value.asBool] at h
      · -- AST .ok true → CST .ok true
        intro h
        cases res with
        | error err =>
          rw [eval_and_error _ _ req es err (by rw [hev])] at h; simp at h
        | ok v =>
          cases v with
          | prim p =>
            cases p with
            | bool b =>
              simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok]
              cases b
              · rw [eval_and_false _ _ req es (by rw [hev])] at h; simp at h
              · simp only [Bool.not_true, ↓reduceIte]
                have h_fst : Spec.evaluate c.toCondition.toExpr req es = .ok (.prim (.bool true)) := by rw [hev]
                have h_inner := eval_and_true_implies_second_true _ _ req es h h_fst
                exact ih.mpr h_inner
            | _ =>
              rw [eval_and_nonbool _ _ req es _ .typeError (by rw [hev]) (by rfl)] at h; simp at h
          | _ =>
            rw [eval_and_nonbool _ _ req es _ .typeError (by rw [hev]) (by rfl)] at h; simp at h

/-- CST policy satisfaction agrees with AST policy satisfaction on .ok true -/
theorem cst_policy_evaluate_eq_ok_true (cstPol : CST.Policy) (req : Request) (es : Entities) :
    CST.Policy.evaluate cstPol req es = .ok true ↔
    Spec.evaluate (cstPol.toPolicy.toExpr) req es = .ok true := by
  simp only [CST.Policy.evaluate, CST.Policy.toPolicy, Policy.toExpr, pure, Except.pure]
  constructor
  · -- Forward: CST .ok true → AST .ok true
    intro h
    generalize hp : Spec.evaluate cstPol.principalScope.toExpr req es = resp at h
    cases resp with
    | error err => simp [Result.as, Coe.coe, Value.asBool] at h
    | ok vp => cases vp with
      | prim pp => cases pp with
        | bool bp =>
          simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok] at h
          cases bp
          · simp at h
          · simp only [Bool.not_true, ↓reduceIte] at h
            generalize ha : Spec.evaluate cstPol.actionScope.toExpr req es = resa at h
            cases resa with
            | error err => simp [Result.as, Coe.coe, Value.asBool] at h
            | ok va => cases va with
              | prim pa => cases pa with
                | bool ba =>
                  simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok] at h
                  cases ba
                  · simp at h
                  · simp only [Bool.not_true, ↓reduceIte] at h
                    generalize hr : Spec.evaluate cstPol.resourceScope.toExpr req es = resr at h
                    cases resr with
                    | error err => simp [Result.as, Coe.coe, Value.asBool] at h
                    | ok vr => cases vr with
                      | prim pr => cases pr with
                        | bool br =>
                          simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok] at h
                          cases br
                          · simp at h
                          · simp only [Bool.not_true, ↓reduceIte] at h
                            exact eval_and_true_ok _ _ req es _ true (by rw [hp])
                              (eval_and_true_ok _ _ req es _ true (by rw [ha])
                                (eval_and_true_ok _ _ req es _ true (by rw [hr])
                                  ((conditions_evaluate_eq_ok_true _ req es).mp h) (by rfl))
                                (by rfl)) (by rfl)
                        | _ => simp [Result.as, Coe.coe, Value.asBool] at h
                      | _ => simp [Result.as, Coe.coe, Value.asBool] at h
                | _ => simp [Result.as, Coe.coe, Value.asBool] at h
              | _ => simp [Result.as, Coe.coe, Value.asBool] at h
        | _ => simp [Result.as, Coe.coe, Value.asBool] at h
      | _ => simp [Result.as, Coe.coe, Value.asBool] at h
  · -- Backward: AST .ok true → CST .ok true
    intro h
    generalize hp : Spec.evaluate cstPol.principalScope.toExpr req es = resp
    cases resp with
    | error err =>
      rw [eval_and_error _ _ req es err (by rw [hp])] at h; simp at h
    | ok vp => cases vp with
      | prim pp => cases pp with
        | bool bp =>
          simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok]
          cases bp
          · rw [eval_and_false _ _ req es (by rw [hp])] at h; simp at h
          · simp only [Bool.not_true, ↓reduceIte]
            have h1 := eval_and_true_implies_second_true _ _ req es h (by rw [hp])
            generalize ha : Spec.evaluate cstPol.actionScope.toExpr req es = resa
            cases resa with
            | error err =>
              rw [eval_and_error _ _ req es err (by rw [ha])] at h1; simp at h1
            | ok va => cases va with
              | prim pa => cases pa with
                | bool ba =>
                  simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok]
                  cases ba
                  · rw [eval_and_false _ _ req es (by rw [ha])] at h1; simp at h1
                  · simp only [Bool.not_true, ↓reduceIte]
                    have h2 := eval_and_true_implies_second_true _ _ req es h1 (by rw [ha])
                    generalize hr : Spec.evaluate cstPol.resourceScope.toExpr req es = resr
                    cases resr with
                    | error err =>
                      rw [eval_and_error _ _ req es err (by rw [hr])] at h2; simp at h2
                    | ok vr => cases vr with
                      | prim pr => cases pr with
                        | bool br =>
                          simp only [Result.as, Coe.coe, Value.asBool, Except.bind_ok]
                          cases br
                          · rw [eval_and_false _ _ req es (by rw [hr])] at h2; simp at h2
                          · simp only [Bool.not_true, ↓reduceIte]
                            exact (conditions_evaluate_eq_ok_true _ req es).mpr
                              (eval_and_true_implies_second_true _ _ req es h2 (by rw [hr]))
                        | _ =>
                          rw [eval_and_nonbool _ _ req es _ .typeError (by rw [hr]) (by rfl)] at h2
                          simp at h2
                      | _ =>
                        rw [eval_and_nonbool _ _ req es _ .typeError (by rw [hr]) (by rfl)] at h2
                        simp at h2
                | _ =>
                  rw [eval_and_nonbool _ _ req es _ .typeError (by rw [ha]) (by rfl)] at h1
                  simp at h1
              | _ =>
                rw [eval_and_nonbool _ _ req es _ .typeError (by rw [ha]) (by rfl)] at h1
                simp at h1
        | _ =>
          rw [eval_and_nonbool _ _ req es _ .typeError (by rw [hp]) (by rfl)] at h; simp at h
      | _ =>
        rw [eval_and_nonbool _ _ req es _ .typeError (by rw [hp]) (by rfl)] at h; simp at h

/-- Policy-level equivalence: direct CST policy evaluation equals AST policy
    evaluation after translation. -/
theorem cst_policy_satisfied_eq (cstPol : CST.Policy) (req : Request) (es : Entities) :
    CST.satisfiedCST cstPol req es = satisfied (cstPol.toPolicy) req es := by
  simp only [CST.satisfiedCST, satisfied]
  grind [(cst_policy_evaluate_eq_ok_true cstPol req es)]

end Cedar.Thm
