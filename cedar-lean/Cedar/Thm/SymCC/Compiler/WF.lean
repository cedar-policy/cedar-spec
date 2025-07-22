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

import Cedar.Thm.SymCC.Compiler.Basic
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Term.WF

/-!
This file proves that both `compile` and `evaluate` preserve well-formedness.
--/

-- We're disabling the linter on this file because it erroneously claims
-- that a used variable is unused in Lean 4.19.
-- TODO: Remove this option when the linter is fixed.
set_option linter.unusedVariables false

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

---------- Compile is well-formed ----------

private def CompileWF (x : Expr)  : Prop :=
  ∀ {εnv : SymEnv} {t : Term},
    εnv.WellFormedFor x →
    compile x εnv = .ok t →
    (t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty)

private def CompileValueWF (x : Value)  : Prop :=
  ∀ {εnv : SymEnv} {t : Term},
    εnv.WellFormedForValue x →
    compileVal x εnv.entities = .ok t →
    (t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty)

private theorem typeOf_term_some_is_option {t : Term} :
  ∃ ty, Term.typeOf (Term.some t) = TermType.option ty
:= by
  exists t.typeOf
  simp only [Term.typeOf]



private theorem compile_lit_wf {p: Prim} {εnv : SymEnv} {t : Term}
  (hok : compile (Expr.lit p) εnv = Except.ok t) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  simp only [compile, compilePrim] at hok
  cases p <;>
  simp only [Except.ok.injEq, someOf] at * <;>
  first | subst hok | skip
  case bool =>
    simp only [and_self, typeOf_term_some_is_option, Term.WellFormed.some_wf wf_bool]
  case int =>
    simp only [and_self, typeOf_term_some_is_option, Term.WellFormed.some_wf wf_bv]
  case string =>
    simp only [and_self, typeOf_term_some_is_option, Term.WellFormed.some_wf (Term.WellFormed.prim_wf TermPrim.WellFormed.string_wf)]
  case entityUID =>
    split at hok <;>
    simp only [Except.ok.injEq, someOf, reduceCtorEq] at hok
    rename_i h
    subst hok
    simp only [typeOf_term_some_is_option, and_true]
    exact Term.WellFormed.some_wf (Term.WellFormed.prim_wf (TermPrim.WellFormed.entity_wf h))


private theorem compile_val_expr_wf {v : Value} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.val v))
  (hok : compile (Expr.val v) εnv = Except.ok t) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  -- todo use compile_val_wf
  sorry

private theorem compile_var_wf {v : Var} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.var v))
  (hok : compile (Expr.var v) εnv = Except.ok t) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  simp [SymEnv.WellFormedFor, SymEnv.WellFormed, SymRequest.WellFormed] at hwf
  replace hwf := hwf.left.left
  simp only [compile, compileVar] at hok
  split at hok <;>
  split at hok <;>
  simp only [Except.ok.injEq, someOf, reduceCtorEq] at hok <;>
  subst hok <;>
  rename_i h <;>
  simp only [typeOf_term_some_is_option, and_true] <;>
  apply Term.WellFormed.some_wf <;>
  simp only [hwf]

private theorem compile_ite_wf {x₁ x₂ x₃: Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.ite x₁ x₂ x₃))
  (hok : compile (Expr.ite x₁ x₂ x₃) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂)
  (ih₃ : CompileWF x₃) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂, hwφ₃⟩ := wf_εnv_for_ite_implies hwf
  replace ⟨t₁, hr₁, hok⟩ := compile_ite_ok_implies hok
  split at hok
  case h_1 =>
    cases hr₂ : compile x₂ εnv <;>
    simp [hr₂] at hok
    subst hok
    exact ih₂ hwφ₂ hr₂
  case h_2 =>
    cases hr₃ : compile x₃ εnv <;>
    simp [hr₃] at hok
    subst hok
    exact ih₃ hwφ₃ hr₃
  case h_3 =>
    replace ⟨hb, t₂, t₃, hr₂, hr₃, ht, hok⟩ := hok
    subst hok
    replace ih₁ := (ih₁ hwφ₁ hr₁).left
    replace ih₂ := ih₂ hwφ₂ hr₂
    replace ih₃ := ih₃ hwφ₃ hr₃
    have h₁ := wf_option_get ih₁ hb
    have h₂ := wf_ite h₁.left ih₂.left ih₃.left h₁.right ht
    replace ⟨ty, ih₂⟩ := ih₂.right
    simp only [ih₂] at h₂
    have h₃ := wf_ifSome_option ih₁ h₂.left h₂.right
    simp only [h₃.left, true_and]
    exists ty
    exact h₃.right

private theorem compile_and_wf {x₁ x₂: Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.and x₁ x₂))
  (hok : compile (Expr.and x₁ x₂) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_and_implies hwf
  replace ⟨t₁, hr₁, hok⟩ := compile_and_ok_implies hok
  split at hok
  case h_1 =>
    subst hok
    simp only [Term.WellFormed.some_wf wf_bool, true_and]
    exists .bool
    simp only [typeOf_term_some, typeOf_bool]
  case h_2 =>
    replace ⟨ht₁, t₂, hr₂, ht₂, hok⟩ := hok
    subst hok
    replace ih₁ := (ih₁ hwφ₁ hr₁).left
    replace ih₂ := (ih₂ hwφ₂ hr₂).left
    have h₁ := wf_option_get ih₁ ht₁
    have h₂ := @wf_ite εnv.entities
      (option.get t₁) t₂ (Term.some (Term.prim (TermPrim.bool false)))
      h₁.left ih₂ (Term.WellFormed.some_wf wf_bool)
      h₁.right (by simp only [ht₂, typeOf_term_some, typeOf_bool])
    rw [ht₂] at h₂
    have h₃ := wf_ifSome_option ih₁ h₂.left h₂.right
    simp only [h₃.left, true_and]
    exists .bool
    exact h₃.right

private theorem compile_or_wf {x₁ x₂: Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.or x₁ x₂))
  (hok : compile (Expr.or x₁ x₂) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_or_implies hwf
  replace ⟨t₁, hr₁, hok⟩ := compile_or_ok_implies hok
  split at hok
  case h_1 =>
    subst hok
    simp only [Term.WellFormed.some_wf wf_bool, true_and]
    exists .bool
    simp only [typeOf_term_some, typeOf_bool]
  case h_2 =>
    replace ⟨ht₁, t₂, hr₂, ht₂, hok⟩ := hok
    subst hok
    replace ih₁ := (ih₁ hwφ₁ hr₁).left
    replace ih₂ := (ih₂ hwφ₂ hr₂).left
    have h₁ := wf_option_get ih₁ ht₁
    have h₂ := @wf_ite εnv.entities
      (option.get t₁) (Term.some (Term.prim (TermPrim.bool true))) t₂
      h₁.left (Term.WellFormed.some_wf wf_bool) ih₂ h₁.right
      (by simp only [typeOf_term_some, typeOf_bool, ← ht₂])
    simp only [typeOf_term_some, typeOf_bool] at h₂
    have h₃ := wf_ifSome_option ih₁ h₂.left h₂.right
    simp only [h₃.left, true_and]
    exists .bool
    exact h₃.right

theorem compileAttrsOf_wf {t t₁: Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileAttrsOf t₁ εs = Except.ok t)  :
  t.WellFormed εs ∧
  ∃ rty, t.typeOf = .record rty ∧
  (t₁.typeOf = .record rty ∨
   ∃ ety fₐ,
    t₁.typeOf = .entity ety ∧ εs.attrs ety = .some fₐ ∧
    fₐ.outType = .record rty)
:= by
  replace hok := compileAttrsOf_ok_implies hok
  rcases hok with ⟨rty, hty, ht⟩ | ⟨ety, fₐ, hty, hf, ht⟩ <;>
  subst ht
  case inl =>
    simp only [hw₁, exists_and_left, true_and]
    exists rty
    simp only [hty, false_and, exists_const, or_false, and_self, reduceCtorEq]
  case inr =>
    have hwf := wf_εs_implies_wf_attrs hwε hf
    rw [← hty] at hwf
    have ha := wf_app hw₁ (by simp only [hwf.right.left]) hwf.left
    simp only [ha.left, exists_and_left, true_and]
    have ⟨rty, hrty⟩ := isCedarRecordType_implies_term_record_type hwf.right.right
    exists rty
    simp only [ha.right, hrty, true_and]
    apply Or.inr
    exists ety
    simp only [hty, true_and]
    exists fₐ

theorem compileHasAttr_wf {t t₁: Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileHasAttr t₁ a εs = Except.ok t)  :
  t.WellFormed εs ∧ t.typeOf = .option .bool
:= by
  replace ⟨t₂, rty, hok, ha, ha'⟩ := compileHasAttr_ok_implies hok
  split at ha' <;> subst ha'
  case h_1 heq =>
    have ⟨hw₂, rty, hty⟩ := compileAttrsOf_wf hwε hw₁ hok
    simp [hty] at ha ; subst ha
    replace ⟨h, hty⟩ := wf_isSome (wf_record_get hw₂ hty.left heq).left
    constructor
    · exact Term.WellFormed.some_wf h
    · simp only [typeOf_term_some, TermType.option.injEq, hty]
  case h_2 | h_3 =>
    simp only [typeOf_term_some, typeOf_bool, TermType.option.injEq, exists_eq', and_true]
    exact Term.WellFormed.some_wf wf_bool

private theorem compile_hasAttr_wf {x₁ : Expr} {a : Attr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.hasAttr x₁ a))
  (hok : compile (Expr.hasAttr x₁ a) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have hwφ₁ := wf_εnv_for_hasAttr_implies hwf
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_hasAttr_ok_implies hok
  subst ht
  replace ⟨ih₁, ty, hty⟩ := ih₁ hwφ₁ hok
  have hopt := wf_option_get ih₁ hty
  replace ha := compileHasAttr_wf hwφ₁.left.right hopt.left ha
  have h := wf_ifSome_option ih₁ ha.left ha.right
  simp only [h.left, true_and]
  exists .bool
  exact h.right

theorem compileGetAttr_wf {t t₁: Term} {a : Attr} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileGetAttr t₁ a εs = Except.ok t)  :
  t.WellFormed εs ∧ ∃ tyₐ, t.typeOf = .option tyₐ
:= by
  replace ⟨t₂, rty, hok, ha, tyₐ, hf, ha'⟩ := compileGetAttr_ok_implies hok
  have ⟨hw₂, rty, hty⟩ := compileAttrsOf_wf hwε hw₁ hok
  simp [hty] at ha ; subst ha
  replace ⟨hwf, hty⟩ := wf_record_get hw₂ hty.left hf
  split at ha' <;> subst ha'
  case h_1 tyₐ =>
    constructor
    · exact hwf
    · exists tyₐ
  case h_2 tyₐ =>
    simp only [typeOf_term_some, TermType.option.injEq, exists_eq', and_true]
    exact Term.WellFormed.some_wf hwf

private theorem compile_getAttr_wf {x₁ : Expr} {a : Attr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.getAttr x₁ a))
  (hok : compile (Expr.getAttr x₁ a) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have hwφ₁ := wf_εnv_for_getAttr_implies hwf
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_getAttr_ok_implies hok
  subst ht
  replace ⟨ih₁, ty, hty⟩ := ih₁ hwφ₁ hok
  have hopt := wf_option_get ih₁ hty
  replace ⟨ha, tyₐ, ha'⟩ := compileGetAttr_wf hwφ₁.left.right hopt.left ha
  have h := wf_ifSome_option ih₁ ha ha'
  simp only [h.left, true_and]
  exists tyₐ
  exact h.right

theorem compileApp₁_wf_types {op₁ : UnaryOp} {t t₁: Term} {εs : SymEntities}
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileApp₁ op₁ t₁ = Except.ok t)  :
  t.WellFormed εs ∧
  match op₁ with
  | .neg => t.typeOf = .option (.bitvec 64)
  | _    => t.typeOf = .option .bool
:= by
  replace hok := compileApp₁_ok_implies hok
  split at hok <;> simp only
  case h_1 =>
    have hwf := wf_not hw₁ hok.left
    simp only [hok.right, typeOf_term_some, hwf.right, and_true]
    exact Term.WellFormed.some_wf hwf.left
  case h_2 =>
    have hwf₁ := wf_bvnego hw₁ hok.left
    have hwf₂ := wf_bvneg hw₁ hok.left
    have hwf₃ := wf_ifFalse hwf₁.left hwf₂.left hwf₁.right
    rw [hwf₂.right] at hwf₃
    simp only [hok.right, hwf₃, and_self]
  case h_3 p _ =>
    have hwf := @wf_string_like εs t₁ p hw₁ hok.left
    simp only [hok.right, typeOf_term_some, hwf.right, and_true]
    exact Term.WellFormed.some_wf hwf.left
  case h_4 =>
    replace ⟨_, hok⟩ := hok
    simp only [hok.right, typeOf_term_some, typeOf_bool, and_true]
    exact Term.WellFormed.some_wf wf_bool
  case h_5 =>
    replace ⟨⟨_, hty⟩, hok⟩ := hok
    have hwf := wf_set_isEmpty hw₁ hty
    simp only [hok, typeOf_term_some, hwf.right, and_true]
    exact Term.WellFormed.some_wf hwf.left

theorem compileApp₁_wf {op₁ : UnaryOp} {t t₁: Term} {εs : SymEntities}
  (hw₁ : Term.WellFormed εs t₁)
  (hok : compileApp₁ op₁ t₁ = Except.ok t)  :
  t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwf, hty⟩ := compileApp₁_wf_types hw₁ hok
  simp only [hwf, true_and]
  split at hty <;>
  simp only [hty, TermType.option.injEq, exists_eq']

private theorem compile_unaryApp_wf {op₁ : UnaryOp} {x₁ : Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.unaryApp op₁ x₁))
  (hok : compile (Expr.unaryApp op₁ x₁) εnv = Except.ok t)
  (ih₁ : CompileWF x₁) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have hwφ₁ := wf_εnv_for_unaryApp_implies hwf
  replace ⟨t₂, t₃, hok, ha, ht⟩ := compile_unaryApp_ok_implies hok
  subst ht
  replace ⟨ih₁, ty, hty⟩ := ih₁ hwφ₁ hok
  have hopt := wf_option_get ih₁ hty
  replace ⟨ha, _, ha'⟩ := compileApp₁_wf hopt.left ha
  have h := wf_ifSome_option ih₁ ha ha'
  simp only [h, TermType.option.injEq, exists_eq', and_self]

theorem compileInₑ.isEq_wf {t₁ t₂ : Term} {εs : SymEntities}
  (hw₁  : Term.WellFormed εs t₁)
  (hw₂  : Term.WellFormed εs t₂) :
  (compileInₑ.isEq t₁ t₂).WellFormed εs ∧ (compileInₑ.isEq t₁ t₂).typeOf = .bool
:= by
  simp only [compileInₑ.isEq]
  split
  · rename_i heq
    exact wf_eq hw₁ hw₂ heq
  · exact And.intro wf_bool typeOf_bool

theorem compileInₑ.isIn_wf {t₁ t₂ : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t₁)
  (hty₁ : t₁.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs t₂)
  (hty₂ : t₂.typeOf = .entity ety₂)
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (compileInₑ.isIn t₁ t₂ ancs?).WellFormed εs ∧ (compileInₑ.isIn t₁ t₂ ancs?).typeOf = .bool
:= by
  simp only [compileInₑ.isIn]
  split
  · rename_i fₐ
    rw [eq_comm] at ha
    replace hwε := wf_εs_implies_wf_ancs hwε ha
    rw [eq_comm, ← hty₁] at hwε
    have happ := wf_app hw₁ hwε.right.left hwε.left
    rw [hwε.right.right, ← hty₂] at happ
    exact wf_set_member hw₂ happ.left happ.right
  · exact And.intro wf_bool typeOf_bool

theorem compileInₑ_wf {t₁ t₂ : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t₁)
  (hty₁ : t₁.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs t₂)
  (hty₂ : t₂.typeOf = .entity ety₂)
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (compileInₑ t₁ t₂ ancs?).WellFormed εs ∧ (compileInₑ t₁ t₂ ancs?).typeOf = .bool
:= by
  have heq := compileInₑ.isEq_wf hw₁ hw₂
  have hin := compileInₑ.isIn_wf hwε hw₁ hty₁ hw₂ hty₂ ha
  rw [compileInₑ_def]
  exact wf_or heq.left hin.left heq.right hin.right

theorem compileInₛ.isIn₁_wf {t ts : Term} {εs : SymEntities}
  (hw₁  : Term.WellFormed εs t)
  (hw₂  : Term.WellFormed εs ts) :
  (compileInₛ.isIn₁ t ts).WellFormed εs ∧ (compileInₛ.isIn₁ t ts).typeOf = .bool
:= by
  simp only [compileInₛ.isIn₁]
  split
  · rename_i heq
    exact wf_set_member hw₁ hw₂ heq
  · exact And.intro wf_bool typeOf_bool

theorem compileInₛ.isIn₂_wf {t ts : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t)
  (hty₁ : t.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs ts)
  (hty₂ : ts.typeOf = .set (.entity ety₂))
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (compileInₛ.isIn₂ t ts ancs?).WellFormed εs ∧ (compileInₛ.isIn₂ t ts ancs?).typeOf = .bool
:= by
  simp only [compileInₛ.isIn₂]
  split
  · rename_i fₐ
    rw [eq_comm] at ha
    replace hwε := wf_εs_implies_wf_ancs hwε ha
    rw [eq_comm, ← hty₁] at hwε
    have happ := wf_app hw₁ hwε.right.left hwε.left
    rw [hwε.right.right] at happ
    exact wf_set_intersects hw₂ happ.left hty₂ happ.right
  · exact And.intro wf_bool typeOf_bool

theorem compileInₛ_wf {t ts : Term} {ancs? : Option UnaryFunction} {ety₁ ety₂ : EntityType} {εs : SymEntities}
  (hwε  : εs.WellFormed)
  (hw₁  : Term.WellFormed εs t)
  (hty₁ : t.typeOf = .entity ety₁)
  (hw₂  : Term.WellFormed εs ts)
  (hty₂ : ts.typeOf = .set (.entity ety₂))
  (ha   : ancs? = SymEntities.ancestorsOfType εs ety₁ ety₂) :
  (compileInₛ t ts ancs?).WellFormed εs ∧ (compileInₛ t ts ancs?).typeOf = .bool
:= by
  have hin₁ := compileInₛ.isIn₁_wf hw₁ hw₂
  have hin₂ := compileInₛ.isIn₂_wf hwε hw₁ hty₁ hw₂ hty₂ ha
  rw [compileInₛ_def]
  exact wf_or hin₁.left hin₂.left hin₁.right hin₂.right

theorem compileApp₂_wf_types {op₂ : BinaryOp} {t t₁ t₂: Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hw₂ : Term.WellFormed εs t₂)
  (hok : compileApp₂ op₂ t₁ t₂ εs = Except.ok t)  :
  t.WellFormed εs ∧
  match op₂ with
  | .add | .sub | .mul => t.typeOf = .option (.bitvec 64)
  | .getTag            => ∃ ety τs, t₁.typeOf = .entity ety ∧ εs.tags ety = some (some τs) ∧ t.typeOf = τs.vals.outType.option
  | _                  => t.typeOf = .option .bool
:= by
  cases op₂ <;> simp only
  case eq =>
    have ht := compileApp₂_eq_ok_implies hok
    rcases ht with ⟨hty, ht⟩ | ⟨_, ht⟩ <;>
    simp only [ht, typeOf_term_some, TermType.option.injEq, exists_eq', and_true]
    · replace ⟨hwf, hty⟩ := wf_eq hw₁ hw₂ (reducibleEq_ok_true_implies hty)
      simp only [Term.WellFormed.some_wf hwf, hty, and_self]
    · simp only [Term.WellFormed.some_wf wf_bool, typeOf_bool, and_self]
  case mem =>
    replace ⟨ety₁, ety₂, hty₁, hok⟩ := compileApp₂_mem_ok_implies hok
    rcases hok with ⟨hty₂, ht⟩ | ⟨hty₂, ht⟩ <;>
    simp only [ht, typeOf_term_some, TermType.option.injEq, exists_eq', and_true]
    · have hwf := compileInₑ_wf hwε hw₁ hty₁ hw₂ hty₂ rfl
      exact And.intro (Term.WellFormed.some_wf hwf.left) hwf.right
    · have hwf := compileInₛ_wf hwε hw₁ hty₁ hw₂ hty₂ rfl
      exact And.intro (Term.WellFormed.some_wf hwf.left) hwf.right
  case less =>
    have ht := compileApp₂_less_ok_implies hok
    rcases ht with ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩
    case _ =>
      have ⟨hwf, hty⟩ := wf_bvslt hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_duration_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_duration_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvslt hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_datetime_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_datetime_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvslt hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case lessEq =>
    have ht := compileApp₂_lessEq_ok_implies hok
    rcases ht with ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩ | ⟨hty₁, hty₂, ht⟩
    case _ =>
      have ⟨hwf, hty⟩ := wf_bvsle hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_duration_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_duration_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvsle hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
    case _ =>
      have ⟨hw₁, hty₁⟩ := wf_ext_datetime_val hw₁ hty₁
      have ⟨hw₂, hty₂⟩ := wf_ext_datetime_val hw₂ hty₂
      have ⟨hwf, hty⟩ := wf_bvsle hw₁ hw₂ hty₁ hty₂
      simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case add =>
    have ⟨hty₁, hty₂, ht⟩ := compileApp₂_add_ok_implies hok
    have hwt := wf_bvadd hw₁ hw₂ hty₁ hty₂
    have hwg := wf_bvsaddo hw₁ hw₂ hty₁ hty₂
    simp only [ht, wf_ifFalse hwg.left hwt.left hwg.right, hwt, and_self]
  case sub =>
    have ⟨hty₁, hty₂, ht⟩ := compileApp₂_sub_ok_implies hok
    have hwt := wf_bvsub hw₁ hw₂ hty₁ hty₂
    have hwg := wf_bvssubo hw₁ hw₂ hty₁ hty₂
    simp only [ht, wf_ifFalse hwg.left hwt.left hwg.right, hwt, and_self]
  case mul =>
    have ⟨hty₁, hty₂, ht⟩ := compileApp₂_mul_ok_implies hok
    have hwt := wf_bvmul hw₁ hw₂ hty₁ hty₂
    have hwg := wf_bvsmulo hw₁ hw₂ hty₁ hty₂
    simp only [ht, wf_ifFalse hwg.left hwt.left hwg.right, hwt, and_self]
  case contains =>
    have ⟨hty, ht⟩ := compileApp₂_contains_ok_implies hok
    replace ⟨hwf, hty⟩ := wf_set_member hw₂ hw₁ hty
    simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case containsAll =>
    have ⟨_, hty₁, hty₂, ht⟩ := compileApp₂_containsAll_ok_implies hok
    have ⟨hwf, hty⟩ := wf_set_subset hw₂ hw₁ hty₂ hty₁
    simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case containsAny =>
    have ⟨_, hty₁, hty₂, ht⟩ := compileApp₂_containsAny_ok_implies hok
    have ⟨hwf, hty⟩ := wf_set_intersects hw₁ hw₂ hty₁ hty₂
    simp only [ht, Term.WellFormed.some_wf hwf, typeOf_term_some, hty, and_self]
  case hasTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_hasTag_ok_implies hok
    replace hok := compileHasTag_ok_implies hok
    rcases hok with ⟨_, hok⟩ | ⟨τs, hτs, hok⟩ <;> subst hok
    · simp only [Term.WellFormed.some_wf wf_bool, typeOf_term_some, typeOf_bool, and_self]
    · have hwτ := wf_tags_hasTag (wf_εs_implies_wf_tags hwε hτs) hw₁ hw₂ hty₁ hty₂
      simp only [Term.WellFormed.some_wf hwτ.left, typeOf_term_some, hwτ.right, and_self]
  case getTag =>
    replace ⟨ety, hty₁, hty₂, hok⟩ := compileApp₂_getTag_ok_implies hok
    replace ⟨τs, hτs, hok⟩ := compileGetTag_ok_implies hok
    subst hok
    have hwτ := wf_tags_getTag (wf_εs_implies_wf_tags hwε hτs) hw₁ hw₂ hty₁ hty₂
    simp only [hwτ, hty₁, TermType.prim.injEq, TermPrimType.entity.injEq, TermType.option.injEq,
      exists_and_left, exists_eq_left', hτs, Option.some.injEq, and_self]

theorem compileApp₂_wf {op₂ : BinaryOp} {t t₁ t₂: Term} {εs : SymEntities}
  (hwε : εs.WellFormed)
  (hw₁ : Term.WellFormed εs t₁)
  (hw₂ : Term.WellFormed εs t₂)
  (hok : compileApp₂ op₂ t₁ t₂ εs = Except.ok t)  :
  t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwf, hty⟩ := compileApp₂_wf_types hwε hw₁ hw₂ hok
  simp only [hwf, true_and]
  split at hty
  any_goals (simp only [hty, TermType.option.injEq, exists_eq'])
  replace ⟨_, _, hty⟩ := hty
  simp only [hty, TermType.option.injEq, exists_eq']

private theorem compile_binaryApp_wf {op₂ : BinaryOp} {x₁ x₂ : Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.binaryApp op₂ x₁ x₂))
  (hok : compile (Expr.binaryApp op₂ x₁ x₂) εnv = Except.ok t)
  (ih₁ : CompileWF x₁)
  (ih₂ : CompileWF x₂) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  have ⟨hwφ₁, hwφ₂⟩ := wf_εnv_for_binaryApp_implies hwf
  replace ⟨t₁, t₂, t₃, hok₁, hok₂, hok, ht⟩ := compile_binaryApp_ok_implies hok
  subst ht
  replace ⟨ih₁, ty₁, hty₁⟩ := ih₁ hwφ₁ hok₁
  replace ⟨ih₂, ty₂, hty₂⟩ := ih₂ hwφ₂ hok₂
  have hopt₁ := wf_option_get ih₁ hty₁
  have hopt₂ := wf_option_get ih₂ hty₂
  have ⟨ih₃, ty, hty₃⟩ := compileApp₂_wf hwf.left.right hopt₁.left hopt₂.left hok
  have h := wf_ifSome_option ih₂ ih₃ hty₃
  replace h := wf_ifSome_option ih₁ h.left h.right
  simp only [h, TermType.option.injEq, exists_eq', and_self]

private theorem compile_set_wf {xs : List Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.set xs))
  (hok : compile (Expr.set xs) εnv = Except.ok t)
  (ih  : ∀ x ∈ xs, CompileWF x) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace hwf := wf_εnv_for_set_implies hwf
  replace ⟨ts, heq, hok⟩ := compile_set_ok_implies hok
  have ⟨ty, hd, tl, hcons, hty, ht⟩ := compileSet_ok_implies hok
  subst ht
  replace heq := List.forall₂_implies_all_right heq
  replace hwf : ∀ t ∈ ts, t.WellFormed εnv.entities := by
    intro t h
    replace ⟨x, heq⟩ := heq t h
    simp only [ih x heq.left (hwf x heq.left) heq.right]
  have hwo := wf_option_get_mem_of_type hwf hty
  have hwty := typeOf_option_wf_terms_is_wf hcons hwf hty
  have hwfs := wf_some_setOf_map hwo hwty
  have hwa := wf_ifAllSome hwf hwfs.left hwfs.right
  simp only [hwa, TermType.option.injEq, exists_eq', and_self]

private theorem comple_val_wf {v : Value} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedForValue εnv v)
  (hok : compileVal v εnv.entities = Except.ok t) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  cases v with
  | prim p =>
    simp [compileVal] at hok
    have h : compilePrim p εnv.entities = compile (Expr.lit p) εnv := by {
      simp [compile]
    }
    rw [h] at hok
    exact compile_lit_wf hok
  | set s =>
    sorry
  | record r =>
    have ih : ∀ aᵢ xᵢ, (aᵢ, xᵢ) ∈ r.kvs → CompileValueWF xᵢ := by
      intro aᵢ xᵢ h
      have _ : sizeOf xᵢ < 1 + sizeOf r.kvs := List.sizeOf_snd_lt_sizeOf_list h
      exact @comple_val_wf xᵢ
    replace hwf := wf_εnv_for_record_val_implies hwf
    replace ⟨ats, heq, hok⟩ := compile_record_val_ok_implies hok
    subst hok
    replace heq := List.forall₂_implies_all_right heq
    simp only [compileRecord]
    replace ih : ∀ a t, (a, t) ∈ ats → t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty := by
      intro a t h
      replace ⟨(_, x), h', ha, heq⟩ := heq (a, t) h
      simp only at ha heq
      rw [eq_comm] at ha ; subst ha
      simp only [ih a x h' (hwf (a, x) h') heq, and_self]
    replace hwf := wf_prods_option_implies_wf_prods ih
    have hwg := wf_prods_implies_wf_map_snd hwf
    have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd ih)
    have hwa := wf_ifAllSome hwg hwo hty
    simp only [someOf, hwa, TermType.option.injEq, exists_eq', and_self]
  | ext e =>
    sorry
decreasing_by
  -- todo figure out nasty termination proof here
  sorry

private theorem compile_record_wf {axs : List (Attr × Expr)} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.record axs))
  (hok : compile (Expr.record axs) εnv = Except.ok t)
  (ih  : ∀ (aᵢ : Attr) (xᵢ : Expr), (aᵢ, xᵢ) ∈ axs → CompileWF xᵢ) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace hwf := wf_εnv_for_record_implies hwf
  replace ⟨ats, heq, hok⟩ := compile_record_ok_implies hok
  subst hok
  replace heq := List.forall₂_implies_all_right heq
  simp only [compileRecord]
  replace ih : ∀ a t, (a, t) ∈ ats → t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty := by
    intro a t h
    replace ⟨(_, x), h', ha, heq⟩ := heq (a, t) h
    simp only at ha heq
    rw [eq_comm] at ha ; subst ha
    simp only [ih a x h' (hwf (a, x) h') heq, and_self]
  replace hwf := wf_prods_option_implies_wf_prods ih
  have hwg := wf_prods_implies_wf_map_snd hwf
  have ⟨hwo, ty, hty⟩ := wf_some_recordOf_map (wf_option_get_mem_of_type_snd ih)
  have hwa := wf_ifAllSome hwg hwo hty
  simp only [someOf, hwa, TermType.option.injEq, exists_eq', and_self]

local macro "simp_compileCall₁'_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
  `(tactic| (
    have ⟨t₁, hts, hty, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_arg' $hwf
    have h₁ := $wf_call_thm (wf_option_get $hwf hty)
    exact wf_ifSome_option $hwf h₁.left h₁.right
  ))

local macro "simp_compileCall₁_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
  `(tactic| (
    have ⟨t₁, hts, hty, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_arg' $hwf
    have h₁ := $wf_call_thm (wf_option_get $hwf hty)
    have h₂ := Term.WellFormed.some_wf h₁.left
    have h₃ := wf_ifSome_option $hwf h₂ typeOf_term_some
    rw [h₁.right] at h₃
    exact h₃
  ))

local macro "simp_compileCall₂'_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
 `(tactic| (
    have ⟨t₁, t₂, hts, hty₁, hty₂, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_args' $hwf
    have h₁ := wf_option_get ($hwf).left hty₁
    have h₂ := wf_option_get ($hwf).right hty₂
    have h₃ := $wf_call_thm h₁ h₂
    have h₄ := wf_ifSome_option ($hwf).right h₃.left h₃.right
    exact wf_ifSome_option ($hwf).left h₄.left h₄.right
  ))

local macro "simp_compileCall₂_wf" hwf:ident hok:ident compile_call_thm:ident wf_call_thm:ident : tactic => do
 `(tactic| (
    have ⟨t₁, t₂, hts, hty₁, hty₂, ht⟩ := $compile_call_thm $hok
    subst hts ht
    replace $hwf := wf_args' $hwf
    have h₁ := wf_option_get ($hwf).left hty₁
    have h₂ := wf_option_get ($hwf).right hty₂
    have h₃ := $wf_call_thm h₁ h₂
    have h₄ := Term.WellFormed.some_wf h₃.left
    have h₅ := wf_ifSome_option ($hwf).right h₄ typeOf_term_some
    rw [h₃.right] at h₅
    exact wf_ifSome_option ($hwf).left h₅.left h₅.right
  ))

local macro "simp_compileCall₀_wf" hok:ident compile_call_thm:ident typeOf_term_ext_thm:ident : tactic => do
`(tactic| (
    replace ⟨_, _, _, _, $hok⟩ := $compile_call_thm $hok
    simp only [$hok:ident, typeOf_term_some, $typeOf_term_ext_thm:ident, and_true]
    exact Term.WellFormed.some_wf (Term.WellFormed.prim_wf TermPrim.WellFormed.ext_wf)
))

theorem compileCall_wf_types {f : ExtFun} {ts : List Term} {εs : SymEntities} {t : Term}
  (hwf : ∀ t ∈ ts, Term.WellFormed εs t)
  (hok : compileCall f ts = Except.ok t)  :
  t.WellFormed εs ∧
  match f with
  | .decimal         => t.typeOf = .option (.ext .decimal)
  | .ip              => t.typeOf = .option (.ext .ipAddr)
  | .datetime
  | .offset
  | .toDate          => t.typeOf = .option (.ext .datetime)
  | .toTime
  | .duration
  | .durationSince   => t.typeOf = .option (.ext .duration)
  | .toMilliseconds
  | .toSeconds
  | .toMinutes
  | .toHours
  | .toDays          => t.typeOf = .option (.bitvec 64)
  | _                => t.typeOf = .option .bool
:= by
  cases f <;> simp only
  case decimal =>
    simp_compileCall₀_wf hok compileCall_decimal_ok_implies typeOf_term_prim_ext_decimal
  case lessThan =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_lessThan_ok_implies wf_decimal_lessThan
  case lessThanOrEqual =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_lessThanOrEqual_ok_implies wf_decimal_lessThanOrEqual
  case greaterThan =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_greaterThan_ok_implies wf_decimal_greaterThan
  case greaterThanOrEqual =>
    simp_compileCall₂_wf hwf hok compileCall_decimal_greaterThanOrEqual_ok_implies wf_decimal_greaterThanOrEqual
  case ip =>
    simp_compileCall₀_wf hok compileCall_ipAddr_ok_implies typeOf_term_prim_ext_ipaddr
  case isIpv4 =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isIpv4_ok_implies wf_ipaddr_isIpv4
  case isIpv6 =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isIpv6_ok_implies wf_ipaddr_isIpv6
  case isLoopback =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isLoopback_ok_implies wf_ipaddr_isLoopback
  case isMulticast =>
    simp_compileCall₁_wf hwf hok compileCall_ipAddr_isMulticast_ok_implies wf_ipaddr_isMulticast
  case isInRange =>
    simp_compileCall₂_wf hwf hok compileCall_ipAddr_isInRange_ok_implies wf_ipaddr_isInRange
  case datetime =>
    simp_compileCall₀_wf hok compileCall_datetime_ok_implies typeOf_term_prim_ext_datetime
  case duration =>
    simp_compileCall₀_wf hok compileCall_duration_ok_implies typeOf_term_prim_ext_duration
  case offset =>
    simp_compileCall₂'_wf hwf hok compileCall_datetime_offset_ok_implies wf_datetime_offset
  case durationSince =>
    simp_compileCall₂'_wf hwf hok compileCall_datetime_durationSince_ok_implies wf_datetime_durationSince
  case toDate =>
    simp_compileCall₁'_wf hwf hok compileCall_datetime_toDate_ok_implies wf_datetime_toDate
  case toTime =>
    simp_compileCall₁_wf hwf hok compileCall_datetime_toTime_ok_implies wf_datetime_toTime
  case toMilliseconds =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toMilliseconds_ok_implies wf_duration_toMilliseconds
  case toSeconds =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toSeconds_ok_implies wf_duration_toSeconds
  case toMinutes =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toMinutes_ok_implies wf_duration_toMinutes
  case toHours =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toHours_ok_implies wf_duration_toHours
  case toDays =>
    simp_compileCall₁_wf hwf hok compileCall_duration_toDays_ok_implies wf_duration_toDays

theorem compileCall_wf {f : ExtFun} {ts : List Term} {εs : SymEntities} {t : Term}
  (hwf : ∀ t ∈ ts, Term.WellFormed εs t)
  (hok : compileCall f ts = Except.ok t)  :
  t.WellFormed εs ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace ⟨hwf, hty⟩ := compileCall_wf_types hwf hok
  simp only [hwf, true_and]
  split at hty <;> simp only [hty, TermType.option.injEq, exists_eq']

private theorem compile_call_wf {f : ExtFun} {xs : List Expr} {εnv : SymEnv} {t : Term}
  (hwf : SymEnv.WellFormedFor εnv (Expr.call f xs))
  (hok : compile (Expr.call f xs) εnv = Except.ok t)
  (ih  : ∀ x ∈ xs, CompileWF x) :
  t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty
:= by
  replace hwf := wf_εnv_for_call_implies hwf
  replace ⟨ts, heq, hok⟩ := compile_call_ok_implies hok
  apply compileCall_wf _ hok
  intro t ht
  replace ⟨x, hx, heq⟩ := List.forall₂_implies_all_right heq t ht
  simp only [@ih x hx εnv t (hwf x hx) heq]

theorem compile_wf {x : Expr} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  (t.WellFormed εnv.entities ∧ ∃ ty, t.typeOf = .option ty)
:= by
  intro hwf hok
  match x with
  | .lit _           => exact compile_lit_wf hok
  | .var v           => exact compile_var_wf hwf hok
  | .val v          => exact compile_val_expr_wf hwf hok
  | .ite x₁ x₂ x₃    =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    have ih₃ := @compile_wf x₃
    exact compile_ite_wf hwf hok ih₁ ih₂ ih₃
  | .and x₁ x₂       =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    exact compile_and_wf hwf hok ih₁ ih₂
  | .or x₁ x₂        =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    exact compile_or_wf hwf hok ih₁ ih₂
  | .unaryApp _ x₁ =>
    have ih₁ := @compile_wf x₁
    exact compile_unaryApp_wf hwf hok ih₁
  | .binaryApp _ x₁ x₂ =>
    have ih₁ := @compile_wf x₁
    have ih₂ := @compile_wf x₂
    exact compile_binaryApp_wf hwf hok ih₁ ih₂
  | .getAttr x₁ _    =>
    have ih₁ := @compile_wf x₁
    exact compile_getAttr_wf hwf hok ih₁
  | .hasAttr x₁ _    =>
    have ih₁ := @compile_wf x₁
    exact compile_hasAttr_wf hwf hok ih₁
  | .set xs          =>
    have ih : ∀ xᵢ ∈ xs, CompileWF xᵢ := by
      intro xᵢ _
      exact @compile_wf xᵢ
    exact compile_set_wf hwf hok ih
  | .record axs      =>
    have ih : ∀ aᵢ xᵢ, (aᵢ, xᵢ) ∈ axs → CompileWF xᵢ := by
      intro aᵢ xᵢ h
      have _ : sizeOf xᵢ < 1 + sizeOf axs := List.sizeOf_snd_lt_sizeOf_list h
      exact @compile_wf xᵢ
    exact compile_record_wf hwf hok ih
  | .call _ xs       =>
    have ih : ∀ xᵢ ∈ xs, CompileWF xᵢ := by
      intro xᵢ _
      exact @compile_wf xᵢ
    exact compile_call_wf hwf hok ih

theorem compile_option_get_wf {x : Expr} {εnv : SymEnv} {t : Term} :
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  ∃ ty,
    (t.WellFormed εnv.entities ∧ t.typeOf = .option ty) ∧
    ((option.get t).WellFormed εnv.entities ∧ (option.get t).typeOf = ty)
:= by
  intro hwε hok
  replace ⟨hwt, ty, hty⟩ := compile_wf hwε hok
  have := wf_option_get hwt hty
  exists ty


private theorem value_bool_wf {b : Bool} {es : Entities} :
  Value.WellFormed es (Value.prim (.bool b))
:= by exact Value.WellFormed.prim_wf (by simp only [Prim.WellFormed])

private theorem value_int_wf {i : Int64} {es : Entities} :
  Value.WellFormed es (Value.prim (.int i))
:= by exact Value.WellFormed.prim_wf (by simp only [Prim.WellFormed])

private theorem value_record_wf_implies_attr_value_wf {r : Map Attr Value} {a : Attr} {v : Value} {es : Entities} :
  Value.WellFormed es (Value.record r) →
  Map.find? r a = some v →
  Value.WellFormed es v
:= by
  intro hwf hf
  cases hwf
  rename_i hwf _
  exact hwf a v hf


---------- Evaluate is well-formed ----------


private def EvaluateWF (x : Expr)  : Prop :=
  ∀ {env : Env} {v : Value},
    env.WellFormedFor x →
    evaluate x env.request env.entities = .ok v →
    v.WellFormed env.entities

private def EvaluateValueWF (v : Value)  : Prop :=
  ∀ {env : Env},
    env.WellFormedForValue v →
    v.WellFormed env.entities



private theorem evaluate_lit_wf {p: Prim} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.lit p))
  (hok : evaluate (Expr.lit p) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate, Except.ok.injEq] at hok
  subst hok
  apply Value.WellFormed.prim_wf
  cases p <;> simp only [Prim.WellFormed]
  replace hwf := hwf.right
  cases hwf
  rename_i hwf
  simp only [Prim.ValidRef] at hwf
  exact hwf

private theorem evaluate_var_wf {xv : Var} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.var xv))
  (hok : evaluate (Expr.var xv) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  unfold evaluate at hok
  replace hwf := hwf.left.left
  unfold Request.WellFormed at hwf
  split at hok <;>
  simp only [Except.ok.injEq] at hok <;>
  subst hok
  case h_4 => simp only [hwf]
  case h_1 | h_2 | h_3 =>
    apply Value.WellFormed.prim_wf
    simp only [Prim.WellFormed, hwf]

private theorem evaluate_val_wf {v : Value} {env : Env} {v' : Value}
  (hwf : Env.WellFormedFor env (Expr.val v))
  (hok : evaluate (Expr.val v) env.request env.entities = Except.ok v') :
  Value.WellFormed env.entities v'
:= by
  simp only [evaluate, Except.ok.injEq] at hok
  subst hok
  unfold Env.WellFormedFor at hwf
  replace ⟨h₁, h₂⟩ := hwf
  simp [Entities.ValidRefsFor] at h₂
  

  sorry

private theorem evaluate_ite_wf {x₁ x₂ x₃ : Expr} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.ite x₁ x₂ x₃))
  (hok : evaluate (Expr.ite x₁ x₂ x₃) env.request env.entities = Except.ok v)
  (ih₂ : EvaluateWF x₂)
  (ih₃ : EvaluateWF x₃) :
  Value.WellFormed env.entities v
:= by
  replace hwf := wf_env_for_ite_implies hwf
  simp only [evaluate, Result.as] at hok
  cases hok₁ : evaluate x₁ env.request env.entities <;>
  simp only [hok₁, Except.bind_err, reduceCtorEq] at hok
  rename_i v₁
  simp only [Coe.coe, Value.asBool] at hok
  split at hok <;>
  simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
  split at hok
  · exact ih₂ hwf.right.left hok
  · exact ih₃ hwf.right.right hok

private theorem evaluate_and_or_wf {x₁ x₂ : Expr} {env : Env} {v : Value} {shortCircuit : Bool}
  (hok: (do
    let b ← Result.as Bool (evaluate x₁ env.request env.entities)
    if b = shortCircuit
    then Except.ok (Value.prim (Prim.bool b))
    else Lean.Internal.coeM (Result.as Bool (evaluate x₂ env.request env.entities))) =
    Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [Result.as] at hok
  cases hok₁ : evaluate x₁ env.request env.entities <;>
  simp only [hok₁, Except.bind_err, reduceCtorEq] at hok
  rename_i v₁
  simp only [Coe.coe, Value.asBool] at hok
  split at hok <;>
  simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
  cases hok₂ : evaluate x₂ env.request env.entities <;>
  simp only [Bool.not_eq_true', Lean.Internal.coeM, hok₂, Except.bind_err] at hok
  case error =>
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    subst hok
    exact value_bool_wf
  case ok =>
    split at hok
    case isTrue =>
      simp only [Except.ok.injEq] at hok
      subst hok
      exact value_bool_wf
    case isFalse =>
      split at hok <;> simp only [Except.bind_ok, Except.bind_err, reduceCtorEq] at hok
      simp only [pure, Except.pure, CoeT.coe, CoeHTCT.coe, CoeHTC.coe, CoeOTC.coe, CoeTC.coe,
        Coe.coe, Except.ok.injEq] at hok
      subst hok
      exact value_bool_wf

private theorem evaluate_and_wf {x₁ x₂ : Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.and x₁ x₂) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate, Bool.not_eq_true'] at hok
  exact evaluate_and_or_wf hok

private theorem evaluate_or_wf {x₁ x₂ : Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.or x₁ x₂) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate] at hok
  exact evaluate_and_or_wf hok

private theorem evaluate_hasAttr_wf {x : Expr} {a : Attr} {env : Env} {v : Value}
  (hok : evaluate (Expr.hasAttr x a) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate, hasAttr, attrsOf] at hok
  simp_do_let (evaluate x env.request env.entities) at hok
  split at hok
  case h_3 => simp only [Except.bind_err, reduceCtorEq] at hok
  case h_1 | h_2 =>
    simp only [Except.bind_ok, Except.ok.injEq] at hok
    subst hok
    exact value_bool_wf

private theorem evaluate_getAttr_wf {x : Expr} {a : Attr} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.getAttr x a))
  (hok : evaluate (Expr.getAttr x a) env.request env.entities = Except.ok v)
  (ih  : EvaluateWF x) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate, getAttr, attrsOf] at hok
  simp_do_let (evaluate x env.request env.entities) at hok
  rename_i hok₁
  replace hwf := wf_env_for_getAttr_implies hwf
  specialize ih hwf hok₁
  split at hok
  case h_1 r =>
    simp only [Except.bind_ok, Map.findOrErr] at hok
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    rename_i v₁ hf
    subst hok
    exact value_record_wf_implies_attr_value_wf ih hf
  case h_2 uid =>
    simp_do_let (Entities.attrs env.entities uid) at hok
    rename_i ha
    simp only [Except.bind_ok, Map.findOrErr] at hok
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    rename_i r _ v₁ hf
    subst hok
    simp only [Entities.attrs] at ha
    simp_do_let (Map.findOrErr env.entities uid Error.entityDoesNotExist) at ha
    rename_i d hd
    simp only [Except.ok.injEq] at ha
    subst ha
    apply value_record_wf_implies_attr_value_wf _ hf
    simp only [Map.findOrErr] at hd
    split at hd <;> simp only [Except.ok.injEq, reduceCtorEq] at hd
    subst hd
    rename_i d hd
    exact (hwf.left.right.right uid d hd).left
  case h_3 =>
    simp only [Except.bind_err, reduceCtorEq] at hok

private theorem intOrErr_ok_wf {i : Option Int64} {v : Value} {es : Entities} :
  intOrErr i = Except.ok v → Value.WellFormed es v
:= by
  intro hok
  simp only [intOrErr] at hok
  split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
  subst hok
  exact value_int_wf

private theorem evaluate_unaryApp_wf {op : UnaryOp} {x : Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.unaryApp op x) env.request env.entities = Except.ok v):
  Value.WellFormed env.entities v
:= by
  simp only [evaluate] at hok
  simp_do_let (evaluate x env.request env.entities) at hok
  simp only [apply₁] at hok
  split at hok <;> (try simp only [Except.ok.injEq, reduceCtorEq] at hok)
  case h_1 | h_3 | h_4 | h_5 =>
    subst hok
    exact value_bool_wf
  case h_2 =>
    exact intOrErr_ok_wf hok

private theorem inₛ_wf {uid : EntityUID} {vs : Set Value} {es : Entities} {v : Value} :
  inₛ uid vs es = Except.ok v → Value.WellFormed es v
:= by
  intro hok
  simp only [inₛ] at hok
  simp_do_let (Set.mapOrErr Value.asEntityUID vs Spec.Error.typeError) at hok
  simp only [Except.ok.injEq] at hok
  subst hok
  exact value_bool_wf

private theorem evaluate_binaryApp_wf {op : BinaryOp} {x₁ x₂ : Expr} {env : Env} {v : Value}
  (hwf : Env.WellFormedFor env (Expr.binaryApp op x₁ x₂))
  (hok : evaluate (Expr.binaryApp op x₁ x₂) env.request env.entities = Except.ok v)
  (ih₁ : EvaluateWF x₁):
  Value.WellFormed env.entities v
:= by
  simp only [evaluate] at hok
  simp_do_let (evaluate x₁ env.request env.entities) at hok
  simp_do_let (evaluate x₂ env.request env.entities) at hok
  simp only [apply₂] at hok
  split at hok <;> (try simp only [Except.ok.injEq, hasTag, reduceCtorEq] at hok)
  any_goals (subst hok ; exact value_bool_wf)
  any_goals (exact intOrErr_ok_wf hok)
  exact inₛ_wf hok
  case _ uid tag h₁ h₂ => -- getTag
    simp only [getTag] at hok
    simp_do_let (env.entities.tags uid) at hok
    rename_i heq
    rw [Map.findOrErr_ok_iff_find?_some] at hok
    replace hwf := (wf_env_for_binaryApp_implies hwf).left
    specialize ih₁ hwf h₁
    replace hwf := hwf.left.right
    simp only [Entities.tags] at heq
    simp_do_let (Map.findOrErr env.entities uid Error.entityDoesNotExist) at heq
    rename_i d hd
    simp only [Except.ok.injEq] at heq
    subst heq
    rw [Map.findOrErr_ok_iff_find?_some] at hd
    replace hwf := hwf.2 uid d hd
    exact hwf.right.right.right.right tag v hok

private theorem evaluate_call_wf {xfn : ExtFun} {xs : List Expr} {env : Env} {v : Value}
  (hok : evaluate (Expr.call xfn xs) env.request env.entities = Except.ok v) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate] at hok
  simp_do_let (List.mapM₁ xs fun x => evaluate x.val env.request env.entities) at hok
  simp only [call] at hok
  split at hok <;> (try simp only [Except.ok.injEq, reduceCtorEq] at hok)
  any_goals (subst hok ; exact value_bool_wf)
  any_goals (subst hok; exact value_int_wf)
  any_goals (subst hok; exact Value.WellFormed.ext_wf)
  all_goals {
    simp only [res] at hok
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    simp only [Coe.coe] at hok
    subst hok
    exact Value.WellFormed.ext_wf
  }

private theorem evaluate_set_wf {env : Env} {v : Value} {xs : List Expr}
  (hwf : Env.WellFormedFor env (Expr.set xs))
  (hok : evaluate (Expr.set xs) env.request env.entities = Except.ok v)
  (ih : ∀ (x : Expr), x ∈ xs → Cedar.Thm.EvaluateWF x) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate] at hok
  simp_do_let (List.mapM₁ xs fun x => evaluate x.val env.request env.entities) at hok
  rename_i vs hvs
  simp only [Except.ok.injEq] at hok
  subst hok
  simp only [List.mapM₁_eq_mapM (λ x => evaluate x env.request env.entities), ← List.mapM'_eq_mapM] at hvs
  apply Value.WellFormed.set_wf _ (Set.make_wf vs)
  intro v hv
  rw [← Set.make_mem] at hv
  replace ⟨x, hx, hvs⟩ := List.mapM'_ok_implies_all_from_ok hvs v hv
  exact ih x hx (wf_env_for_set_implies hwf x hx) hvs

private theorem evaluate_record_wf {env : Env} {v : Value} {axs : List (Attr × Expr)}
  (hwf : Env.WellFormedFor env (Expr.record axs))
  (hok : evaluate (Expr.record axs) env.request env.entities = Except.ok v)
  (ih : ∀ (a : Attr) (x : Expr), (a, x) ∈ axs → Cedar.Thm.EvaluateWF x) :
  Value.WellFormed env.entities v
:= by
  simp only [evaluate] at hok
  simp_do_let ( List.mapM₂ axs fun x => bindAttr x.1.fst (evaluate x.1.snd env.request env.entities)) at hok
  rename_i vs hvs
  simp only [Except.ok.injEq] at hok
  subst hok
  simp only [List.mapM₂, List.attach₂,
    List.mapM_pmap_subtype (λ (x : Attr × Expr) => bindAttr x.fst (evaluate x.snd env.request env.entities))] at hvs
  rw [← List.mapM'_eq_mapM] at hvs
  apply Value.WellFormed.record_wf _ (Map.make_wf vs)
  intro a v hv
  replace hv := Map.find?_mem_toList hv
  simp only [Map.toList, Map.kvs, Map.make] at hv
  have hv' := List.canonicalize_subseteq Prod.fst vs
  rw [List.subset_def] at hv'
  replace hv' := hv' hv
  replace ⟨x, hx, hvs⟩ := List.mapM'_ok_implies_all_from_ok hvs (a, v) hv'
  simp [bindAttr] at hvs
  simp_do_let (evaluate x.snd env.request env.entities) at hvs <;> simp at hvs
  rename_i v' hok
  replace ⟨hvs, hvs'⟩ := hvs
  subst hvs'
  have hx' : (a, x.snd) = x := by rw [← hvs]
  replace hx' : (a, x.snd) ∈ axs := by rw [hx'] ; exact hx
  exact ih a x.snd hx' (wf_env_for_record_implies hwf x hx) hok

theorem evaluate_wf {x : Expr} {env : Env} {v : Value} :
  env.WellFormedFor x →
  evaluate x env.request env.entities = .ok v →
  v.WellFormed env.entities
:= by
  intro hwf hok
  match x with
  | .lit _            => exact evaluate_lit_wf hwf hok
  | .var _            => exact evaluate_var_wf hwf hok
  | .val _            => exact evaluate_val_wf hwf hok
  | .ite _ x₂ x₃      => exact evaluate_ite_wf hwf hok (@evaluate_wf x₂) (@evaluate_wf x₃)
  | .and _ _          => exact evaluate_and_wf hok
  | .or _ _           => exact evaluate_or_wf hok
  | .unaryApp _ _     => exact evaluate_unaryApp_wf hok
  | .binaryApp _ x₁ _ => exact evaluate_binaryApp_wf hwf hok (@evaluate_wf x₁)
  | .getAttr x₁ _     => exact evaluate_getAttr_wf hwf hok (@evaluate_wf x₁)
  | .hasAttr _ _      => exact evaluate_hasAttr_wf hok
  | .set xs           =>
    have ih : ∀ xᵢ, xᵢ ∈ xs → EvaluateWF xᵢ := by
      intro xᵢ _
      exact @evaluate_wf xᵢ
    exact evaluate_set_wf hwf hok ih
  | .record axs       =>
    have ih : ∀ aᵢ xᵢ, (aᵢ, xᵢ) ∈ axs → EvaluateWF xᵢ := by
      intro aᵢ xᵢ h
      have _ : sizeOf xᵢ < 1 + sizeOf axs := List.sizeOf_snd_lt_sizeOf_list h
      exact @evaluate_wf xᵢ
    exact evaluate_record_wf hwf hok ih
  | .call _ _         => exact evaluate_call_wf hok
termination_by sizeOf x

theorem wf_value_uid_implies_exists_entity_data {es : Entities} {uid : EntityUID}
  (hwf : Value.WellFormed es (Value.prim (Prim.entityUID uid))) :
  ∃ d, es.find? uid = some d
:= by
  cases hwf ; rename_i hwf
  simp only [Prim.WellFormed, Map.contains_iff_some_find?] at hwf
  exact hwf

end Cedar.Thm
