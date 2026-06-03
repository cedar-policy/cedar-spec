import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.Aux
import Cedar.Thm.Data.List.Lemmas

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec


theorem policy_to_expr_agrees (cp : Cst.Policy) (ap : Policy)
  (ce : Cst.Expr) (ae : Expr) :
  cp.toPolicy? = some ap →
  cp.toExpr = ce →
  ce.toAExpr? = some ae →
  ap.toExpr = ae := by

  intro hap hce hae
  obtain ⟨p⟩ := cp
  obtain ⟨eff, vars, conds⟩ := p
  sorry
