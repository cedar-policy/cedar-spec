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

import Cedar.Thm.SymCC.Env.Interpret
import Cedar.Thm.SymCC.Term.Same
import Cedar.Thm.SymCC.Compiler.Attr
import Cedar.Thm.SymCC.Compiler.Binary
import Cedar.Thm.SymCC.Compiler.Call
import Cedar.Thm.SymCC.Compiler.Control
import Cedar.Thm.SymCC.Compiler.LitVar
import Cedar.Thm.SymCC.Compiler.Record
import Cedar.Thm.SymCC.Compiler.Set
import Cedar.Thm.SymCC.Compiler.Unary

/-!
This file proves two key auxiliary lemmas used to show the soundness
and completeness of Cedar's symbolic compiler.
--/

namespace Cedar.Thm

open Spec SymCC Factory Validation

/--
The lemma shows that the symbolic compiler (`compile`) behaves like the
concrete evaluator (`evaluate`) on literal inputs.

In particular, let `x` be an expression, `εnv` a well-formed symbolic
environment for `x`, and `env` a well-formed concrete environment for `x` that
is equivalent to `εnv`. Then, the result produced by the symbolic compiler on
`x` and `εnv` is equivalent to the result produced by the concrete evaluator `x`
and `env`.
-/
theorem compile_evaluate {x : Expr} {env : Env} {εnv : SymEnv} {t : Term} :
  env ∼ εnv →
  env.WellFormedFor x →
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  evaluate x env.request env.entities ∼ t
:= by
  intros h₁ h₂ h₃ h₄
  match x with
  | .lit _             => exact compile_evaluate_lit h₄
  | .var _             => exact compile_evaluate_var h₁ h₄
  | .ite x₁ x₂ x₃      =>
    have ih₁ := @compile_evaluate x₁
    have ih₂ := @compile_evaluate x₂
    have ih₃ := @compile_evaluate x₃
    exact compile_evaluate_ite h₁ h₂ h₃ h₄ ih₁ ih₂ ih₃
  | .and x₁ x₂         =>
    have ih₁ := @compile_evaluate x₁
    have ih₂ := @compile_evaluate x₂
    exact compile_evaluate_and h₁ h₂ h₃ h₄ ih₁ ih₂
  | .or x₁ x₂          =>
    have ih₁ := @compile_evaluate x₁
    have ih₂ := @compile_evaluate x₂
    exact compile_evaluate_or h₁ h₂ h₃ h₄ ih₁ ih₂
  | .unaryApp _ x₁     =>
    have ih₁ := @compile_evaluate x₁
    exact compile_evaluate_unaryApp h₁ h₂ h₃ h₄ ih₁
  | .binaryApp _ x₁ x₂ =>
    have ih₁ := @compile_evaluate x₁
    have ih₂ := @compile_evaluate x₂
    exact compile_evaluate_binaryApp h₁ h₂ h₃ h₄ ih₁ ih₂
  | .getAttr x₁ _     =>
    have ih₁ := @compile_evaluate x₁
    exact compile_evaluate_getAttr h₁ h₂ h₃ h₄ ih₁
  | .hasAttr x₁ _     =>
    have ih₁ := @compile_evaluate x₁
    exact compile_evaluate_hasAttr h₁ h₂ h₃ h₄ ih₁
  | .set xs           =>
    have ih : ∀ xᵢ ∈ xs, CompileEvaluate xᵢ := by
      intro xᵢ _
      exact @compile_evaluate xᵢ
    exact compile_evaluate_set h₁ h₂ h₃ h₄ ih
  | .record axs      =>
    have ih : ∀ aᵢ xᵢ, (aᵢ, xᵢ) ∈ axs → CompileEvaluate xᵢ := by
      intro aᵢ xᵢ h
      have _ : sizeOf xᵢ < 1 + sizeOf axs := List.sizeOf_snd_lt_sizeOf_list h
      exact @compile_evaluate xᵢ
    exact compile_evaluate_record h₁ h₂ h₃ h₄ ih
  | .call _ xs       =>
    have ih : ∀ xᵢ ∈ xs, CompileEvaluate xᵢ := by
      intro xᵢ _
      exact @compile_evaluate xᵢ
    exact compile_evaluate_call h₁ h₂ h₃ h₄ ih

/--
The lemma shows that `interpret` and `compile` can be applied in any order to get
the same result. In particular, let `x` be an expression, `εnv` a well-formed
symbolic environment for `x`, and `I` a well-formed interpretion for `εnv`.
Then, compiling `x` with respect to `(εnv.interpret I)` gives the same result as
interpreting the output of compiling `x` with respect to `εnv`.
-/
theorem compile_interpret {x : Expr} {εnv : SymEnv} {I : Interpretation} {t : Term} :
  I.WellFormed εnv.entities →
  εnv.WellFormedFor x →
  compile x εnv = .ok t →
  compile x (εnv.interpret I) = .ok (t.interpret I)
:= by
  intros h₁ h₂ h₃
  match x with
  | .lit _             => exact compile_interpret_lit h₃
  | .var _             => exact compile_interpret_var h₁ h₂ h₃
  | .ite x₁ x₂ x₃      =>
    have ih₁ := @compile_interpret x₁
    have ih₂ := @compile_interpret x₂
    have ih₃ := @compile_interpret x₃
    exact compile_interpret_ite h₁ h₂ h₃ ih₁ ih₂ ih₃
  | .and x₁ x₂         =>
    have ih₁ := @compile_interpret x₁
    have ih₂ := @compile_interpret x₂
    exact compile_interpret_and h₁ h₂ h₃ ih₁ ih₂
  | .or x₁ x₂          =>
    have ih₁ := @compile_interpret x₁
    have ih₂ := @compile_interpret x₂
    exact compile_interpret_or h₁ h₂ h₃ ih₁ ih₂
  | .unaryApp _ x₁     =>
    have ih₁ := @compile_interpret x₁
    exact compile_interpret_unaryApp h₁ h₂ h₃ ih₁
  | .binaryApp _ x₁ x₂ =>
    have ih₁ := @compile_interpret x₁
    have ih₂ := @compile_interpret x₂
    exact compile_interpret_binaryApp h₁ h₂ h₃ ih₁ ih₂
  | .getAttr x₁ _      =>
    have ih₁ := @compile_interpret x₁
    exact compile_interpret_getAttr h₁ h₂ h₃ ih₁
  | .hasAttr x₁ _      =>
    have ih₁ := @compile_interpret x₁
    exact compile_interpret_hasAttr h₁ h₂ h₃ ih₁
  | .set xs            =>
    have ih : ∀ xᵢ ∈ xs, CompileInterpret xᵢ := by
      intro xᵢ _
      exact @compile_interpret xᵢ
    exact compile_interpret_set h₁ h₂ h₃ ih
  | .record axs      =>
    have ih : ∀ aᵢ xᵢ, (aᵢ, xᵢ) ∈ axs → CompileInterpret xᵢ := by
      intro aᵢ xᵢ h
      have _ : sizeOf xᵢ < 1 + sizeOf axs := List.sizeOf_snd_lt_sizeOf_list h
      exact @compile_interpret xᵢ
    exact compile_interpret_record h₁ h₂ h₃ ih
  | .call _ xs       =>
    have ih : ∀ xᵢ ∈ xs, CompileInterpret xᵢ := by
      intro xᵢ _
      exact @compile_interpret xᵢ
    exact compile_interpret_call h₁ h₂ h₃ ih

theorem compile_bisimulation {x : Expr} {env : Env} {εnv : SymEnv} {t : Term} {I : Interpretation} :
  εnv.WellFormedFor x →
  env.WellFormedFor x →
  I.WellFormed εnv.entities →
  env ∼ εnv.interpret I →
  compile x εnv = .ok t →
  evaluate x env.request env.entities ∼ t.interpret I
:= by
  intros h₁ h₂ h₃ h₄ h₅
  have h₆ := interpret_εnv_wf_for_expr h₁ h₃
  have h₇ := compile_interpret h₃ h₁ h₅
  exact compile_evaluate h₄ h₂ h₆ h₇

end Cedar.Thm
