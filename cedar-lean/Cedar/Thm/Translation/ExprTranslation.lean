import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

mutual

theorem exprOrSpecial_to_expr_evalute (eos : ExprOrSpecial) (aexp : Expr)
  (req : Request) (es : Entities) :
  eos.toExpr? = some aexp →
  evaluate aexp req es = match eos with
  | .expr e => evaluate e req es
  | .var v => evaluate (Expr.var v) req es
  | .strLit s => (CstCommon.unescape? s).elim
            (.error .typeError)
            (fun s' => .ok (.prim (.string s')))
  | .boolLit b => .ok (.prim (.bool b))
  | .name _ => .error .typeError := by
  cases eos <;> intro h <;> simp_all [ExprOrSpecial.toExpr?]
  · rename_i lit; cases hsome : CstCommon.unescape? lit with
    | none => rw [hsome] at h; simp at h
    | some s' => rw [hsome] at h; simp at *; rw [← h]; simp [evaluate]
  · rename_i b; rw [← h]; simp [evaluate]

theorem primary_to_expr_evaluate
  (prim : Cst.Primary) (eos : ExprOrSpecial)
  (req : Request) (es : Entities) :
  prim.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = prim.evaluate req es := by
  cases prim
  · /- .literal -/
    intro hprim aexp heos; rename_i lit
    simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at hprim
    have haexp := exprOrSpecial_to_expr_evalute eos aexp req es heos
    rw [haexp]; clear haexp
    cases lit <;> simp at hprim <;> try rw [← hprim]
    · /- .liTrue -/
      unfold Cst.Primary.evaluate; simp
    · /- .liFalse -/
      unfold Cst.Primary.evaluate; simp
    · /- .liNum -/
      rename_i n; unfold Cst.Primary.evaluate; simp; cases hn: (Int64.ofInt? ↑n.toNat) with
      | none => rw [hn] at hprim; simp at *
      | some n' => rw [hn] at hprim; simp at *; rw [← hprim]; simp; simp [evaluate]
    · /- .liStr -/
      rename_i s; unfold Cst.Primary.evaluate; simp; cases hs: (CstCommon.unescape? s) <;> simp

  sorry






theorem expr_translation_sound (cexp : Cst.Expr) (aexp : Expr) (req : Request) (es : Entities) :
  cexp.toAExpr? = some aexp →
  cexp.evaluate req es = evaluate aexp req es := by sorry


end
