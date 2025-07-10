
import Cedar.Spec

namespace Cedar.Thm

open Cedar.Spec

theorem straight_line_slicing_sound {e : Expr} {s : Entities} {r : Request}
  {es : StraightLineExprs}
  {sliced : Entities}
  : es = (to_straight_line_exprs e) ->
  sliced =  (simple_slice_entities_straight_line es s) -> evaluate e r s =
  evaluate e r sliced
:=
  sorry

theorem straight_line_slicing_sound_for_straight {se : StraightLineExpr} {s : Entities} {r : Request}
  {es : StraightLineExprs}
  {sliced : Entities}
  : es.contains se ->
  sliced =  (simple_slice_entities_straight_line es s) -> evaluate es r s =
  evaluate es r sliced
:=
  sorry


theorem straight_line_exists_non_erroring {e: Expr} {r: Request}
  {es : StraightLineExprs } {se : StraightLineExpr} {s: EntityStore}
  : es = (to_straight_line_exprs e) ->
    ∃ se,
    (es.contains se = true) ∧
      evaluate_straight_line_expr se r s = Some v
   :=
  sorry



theorem straight_line_same_semantics {e: Expr} {r: Request}
  {es : StraightLineExprs } {se : StraightLineExpr} {s: EntityStore}
  : es = (to_straight_line_exprs e) ->
    (es.contains se = true) ->
      (evaluate_straight_line_expr se r s = Some v) -> -- only when not erroring
        (evaluate e r s = v)
   :=
  sorry
