
import Cedar.Spec

import Cedar.Thm.Data

namespace Cedar.Thm

open Data Spec

-- Define a local tactic for simplifying straight line expressions
local macro "simp_slexpr_once" : tactic =>
  `(tactic| (try (simp [all_sl_exprs, Data.Set.contains, Data.Set.elts, evaluate_sl, SLResult.toResult] at *)))

local macro "simp_slexpr" : tactic =>
  `(tactic| (simp_slexpr_once; simp_slexpr_once; simp_slexpr_once))

-- after straight line analysis, there exists a SLExpr
-- which does not have an assertion error
theorem sl_exists_non_erroring (e: Expr) (s: Entities) (r: Request)
  : let es := all_sl_exprs e
    ∃ se, ∃ res,
    es.contains se ∧
      (evaluate_sl se r s).toResult = .some res
   := by
   cases e with
   | lit p =>
     intro h_es
     exists .lit p, .ok p
     subst h_es
     apply And.intro
     simp_slexpr
   | var v =>
     intro h_es
     exists .var v, .ok (match v with
       | .principal => r.principal
       | .action => r.action
       | .resource => r.resource
       | .context => r.context)
     subst h_es
     apply And.intro
     simp_slexpr
     simp_slexpr
     cases v with
     | principal | resource | context | action =>
       simp_slexpr
   | ite cond then_expr else_expr =>
     -- For an if-then-else expression, we need to show that either the then branch or the else branch
     -- has a non-erroring straight line expression
     -- First, we need to get the result of evaluating the condition
     let cond_result := evaluate cond r s
     -- Depending on the result of the condition, we choose either the then branch or the else branch
     cases cond_result with
     | ok v =>
       cases v with
       | prim p =>
          cases p with
          | bool b =>
            sorry
          | _ => sorry
       | _ => sorry
     | error e =>
       -- If the condition doesn't evaluate to a boolean, we have an error
       sorry
   | unaryApp op child =>
     intro res
     have ih := sl_exists_non_erroring child s r
     simp at ih
     obtain ⟨child_res, ih⟩ := ih
     obtain ⟨ih1, ih2⟩ := ih
     obtain ⟨child_v, ih2⟩ := ih2
     let new_sl := SLExpr.unaryApp op child_res
     exists new_sl
     subst res
     unfold all_sl_exprs
     simp [*]
     let child_exprs := all_sl_exprs child
     apply And.intro
     . rw [Set.contains_prop_bool_equiv]
       let rec_set := (Set.toList (all_sl_exprs child))
       let new_list := (List.map (fun e => SLExpr.unaryApp op e) (Set.toList (all_sl_exprs child)))
       have child_res_in_set : child_res ∈ rec_set := by
       {
         subst rec_set
         rw [Set.contains_prop_bool_equiv] at *
         rw [← Set.in_list_iff_in_set] at ih1
         unfold Set.toList
         simp [*]
       }
       -- TODO painful verbose low-level proof
       have app_in_new_set : new_sl ∈ new_list := by {
         subst rec_set
         subst new_list
         let func := (fun e => SLExpr.unaryApp op e)
         subst new_sl
         let l := (Set.toList (all_sl_exprs child))
         let me := List.map_ele_implies_result_ele func l child_res
         specialize me child_res_in_set
         subst func
         simp at me
         simp
         exact me
       }
       rw [Set.in_list_iff_in_set] at app_in_new_set
       simp [*]
     . sorry





   | _ => sorry



-- slicing using a straight line expr gives a new store
-- where evaluation is the same
-- TODO this one will change with fancier slicer
theorem straight_line_slicing_sound_for_straight {se : SLExpr} {s : Entities} {r : Request}
  {ses : SLExprs}
  {sliced : Entities}
  : ses.contains se ->
  sliced =  (simple_slice_sl ses s r) -> evaluate_sl se r s =
  evaluate_sl se r sliced
:=
  sorry




-- all the resulting SLExprs have the same semantics
-- unless they error
theorem straight_line_same_semantics {e: Expr} {r: Request}
  {es : SLExprs } {se : SLExpr} {s: Entities} {v: Result Value}
  : es = (all_sl_exprs e) ->
    (es.contains se = true) ->
      ((evaluate_sl se r s).toResult = .some v) -> -- only when not erroring
        (evaluate e r s = v)
   :=
  sorry


-- analyzing an expr and slicing using straight line exprs
-- give a new store where evaluation is the same
-- proof sketch: there is a slexpr that doesn't error
-- all the slexprs have the same semantics as the original (when they don't assert error)
-- slicing preserves the semantics of slexprs
theorem straight_line_slicing_sound {e : Expr} {s : Entities} {r : Request}
  {es : SLExprs}
  {sliced : Entities}
  : es = (all_sl_exprs e) ->
  sliced =  (simple_slice_sl es s r) -> evaluate e r s =
  evaluate e r sliced
:= by
  intros h_es h_sliced
  have h_exists := sl_exists_non_erroring e s r
  cases h_exists with
  | intro se h_exists_se =>
    cases h_exists_se with
    | intro res h_se =>
      rw [←h_es] at h_se
      let h_contains := h_se.left
      have h_res : (evaluate_sl se r s).toResult = res := h_se.right

      -- Use straight_line_slicing_sound_for_straight to show that evaluate_sl se r s = evaluate_sl se r sliced
      have h_eval_sl : evaluate_sl se r s = evaluate_sl se r sliced :=
        @straight_line_slicing_sound_for_straight se s r es sliced h_contains h_sliced

      -- From h_eval_sl and h_res, we know that (evaluate_sl se r sliced).toResult = res
      have h_res_sliced : (evaluate_sl se r sliced).toResult = res := by
        rw [← h_eval_sl]
        exact h_res

      -- Case analysis on res

      -- Use straight_line_same_semantics to show that evaluate e r s = v
      have h_eval_s : evaluate e r s = res :=
        @straight_line_same_semantics e r es se s res h_es h_contains h_res

      -- Use straight_line_same_semantics to show that evaluate e r sliced = v
      have h_eval_sliced : evaluate e r sliced = res :=
        @straight_line_same_semantics e r es se sliced res h_es h_contains h_res_sliced

      -- Combine h_eval_s and h_eval_sliced to get the desired result
      rw [h_eval_s, h_eval_sliced]
