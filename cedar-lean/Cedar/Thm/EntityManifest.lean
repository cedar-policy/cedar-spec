
import Cedar.Spec

import Cedar.Thm.Data

namespace Cedar.Thm

open Data Spec Error

-- Define a local tactic for simplifying straight line expressions
local macro "simp_slexpr_once" : tactic =>
  `(tactic| (try (simp [all_sl_exprs, Data.Set.contains, Data.Set.elts, evaluate_sl, SLResult.toResult] at *)))

local macro "simp_slexpr" : tactic =>
  `(tactic| (simp_slexpr_once; simp_slexpr_once; simp_slexpr_once))

local macro "simp_set_containment_helper" : tactic =>
  `(tactic| (try rw [Set.in_list_iff_in_set] at *;
             try rw [Set.contains_prop_bool_equiv] at *;
             try rw [←Set.in_list_iff_in_mk] at *;
             try rw [Set.in_list_iff_in_set];
             try rw [Set.contains_prop_bool_equiv];
             try rw [←Set.in_list_iff_in_mk]))

-- Does its best to canonicalize set containment facts to simpler forms,
-- eliminating wrappers that convert between sets and lists
local macro "simp_set_containment" : tactic =>
  `(tactic| (simp_set_containment_helper;
             try simp [Set.toList] at *;
             simp_set_containment_helper))

theorem to_result_from_result_inverses  (β) (v: Option (Result β))
  : (SLResult.fromOptionResult β v).toResult = v
  := by
  cases v with
  | none =>
    simp [SLResult.toResult, SLResult.fromOptionResult]
  | some r =>
    simp [SLResult.toResult, SLResult.fromOptionResult, Result.toSLResult]
    cases r with
    | error e =>
      simp
    | ok v =>
      simp

theorem from_to_result_inverses  (β) (v: (SLResult β))
  : (SLResult.fromOptionResult β (v.toResult)) = v
  := by
  cases v with
  | error e =>
    simp [SLResult.toResult, SLResult.fromOptionResult]
    cases e with
    | assertError =>
      simp
    | interpError e' =>
      simp
      unfold Result.toSLResult
      simp
  | ok r =>
    simp [SLResult.toResult, SLResult.fromOptionResult]
    unfold Result.toSLResult
    simp

theorem to_sl_to_result_inverse  (β) (v: (Result β))
  : (SLResult.toResult β (v.toSLResult)) = v
  := by
  sorry

local macro "simp_result_inverses" : tactic =>
  `(tactic| (try rw [to_result_from_result_inverses] at *;
             try rw [from_to_result_inverses] at *;
             try rw [to_sl_to_result_inverse] at *))

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
     subst res
     rcases sl_exists_non_erroring child s r with ⟨child_res, ⟨child_res_in, ⟨child_v, eval_eq⟩⟩⟩
     exists SLExpr.unaryApp op child_res
     simp
     apply And.intro

     . rw [Set.contains_prop_bool_equiv] at *
       unfold all_sl_exprs
       simp
       let child_exprs := all_sl_exprs child
       simp_set_containment
       let mh := List.map_ele_implies_result_ele (fun e => SLExpr.unaryApp op e) child_v
       simp_set_containment
       exact mh
     . have ih := congr_arg (SLResult.fromOptionResult Value) eval_eq
       unfold evaluate_sl
       rw [from_to_result_inverses] at ih
       rw [ih]
       cases child_res_in with
       | ok v =>
         simp [SLResult.fromOptionResult, SLResult.toResult, Result.toSLResult]
         cases apply₁ op v
         all_goals { simp }
       | error e =>
         simp [SLResult.fromOptionResult, SLResult.toResult, Result.toSLResult]
   | _ => sorry


theorem straight_line_slicing_sound_for_single { e : SLExpr } { s : Entities } { r : Request }
  : let sliced := (simple_slice_sl (.mk [e]) s r)
    evaluate_sl e r s = evaluate_sl e r sliced
:= by
  sorry


-- slicing using a straight line expr gives a new store
-- where evaluation is the same
-- TODO this one will change with fancier slicer
theorem straight_line_slicing_sound_for_straight {e : SLExpr} {s : Entities} {r : Request}
  {es : SLExprs}
  {sliced : Entities}
  : let sliced := (simple_slice_sl es s r)
    es.contains e ->
    evaluate_sl e r s = evaluate_sl e r sliced
:= by
  -- todo use straight_line_slicing_sound_for_single
  sorry



instance : Membership SLExpr (Set SLExpr) where
  mem s v := v ∈ s.elts

-- all the resulting SLExprs have the same semantics
-- unless they error
theorem straight_line_same_semantics (e: Expr) (r: Request) {se : SLExpr} {s: Entities} {v: Result Value}
  : let es := (all_sl_exprs e)
    se ∈ es ->
      ((evaluate_sl se r s).toResult = .some v) -> -- only when not erroring
        (evaluate e r s = v)
   := by
   intro h_es h_contains h_res
   subst h_es
   cases e with
   | lit p =>
     simp [evaluate]
     simp [all_sl_exprs] at *
     try rw [Set.contains_prop_bool_equiv] at *
     sorry
   | var v =>
     sorry
   | unaryApp op child_e =>
     simp [evaluate]
     simp [all_sl_exprs] at *
     rcases List.map_ele_implies_exists_application (fun e => SLExpr.unaryApp op e) h_contains with ⟨child_se, ⟨h_contains', child_to_se⟩⟩
     clear h_contains'
     rcases @straight_line_same_semantics child_e r with ih
     simp at ih
     specialize @ih child_se s
     simp_set_containment
     rw [←child_to_se] at h_res
     rw [←child_to_se] at *
     clear child_to_se
     simp_set_containment
     simp [evaluate_sl] at h_res

     cases case : (evaluate_sl child_se r s)
     -- cases on what the child evaluated to
     . rewrite [case] at h_res
       simp at h_res
       simp [SLResult.toResult] at h_res
       rename_i a
       cases h_a: a
       . rw [h_a] at h_res
         simp at h_res

       . rw [h_a] at h_res
         simp at h_res
         rw [case] at ih
         simp [SLResult.toResult] at ih
         rw [h_a] at ih
         simp at ih
         specialize ih h_contains
         rw [ih]
         simp
         exact h_res
     . rename_i child_v
       rw [case] at ih
       simp [SLResult.toResult] at ih
       specialize ih h_contains
       rw [ih]
       simp [Except.bind]
       rw [case] at h_res
       simp at h_res
       simp_result_inverses
       simp at h_res
       exact h_res
   | _ => sorry


-- analyzing an expr and slicing using straight line exprs
-- give a new store where evaluation is the same
-- proof sketch: there is a slexpr that doesn't error
-- all the slexprs have the same semantics as the original (when they don't assert error)
-- slicing preserves the semantics of slexprs
theorem straight_line_slicing_sound {e : Expr} {s : Entities} {r : Request}
  {es : SLExprs}
  : es = (all_sl_exprs e) ->
  let sliced := (simple_slice_sl es s r)
  evaluate e r s = evaluate e r sliced
:= by
  intros h_es sliced
  have h_exists := sl_exists_non_erroring e s r
  cases h_exists with
  | intro se h_exists_se =>
    cases h_exists_se with
    | intro res h_se =>
      rw [←h_es] at h_se
      let h_contains := h_se.left
      have h_res : (evaluate_sl se r s).toResult = res := h_se.right

      -- Use straight_line_slicing_sound_for_straight to show that evaluate_sl se r s = evaluate_sl se r sliced
      have h_eval_sl :=
        @straight_line_slicing_sound_for_straight se s r es
      simp at h_eval_sl
      simp_set_containment
      specialize h_eval_sl h_contains


      -- From h_eval_sl and h_res, we know that (evaluate_sl se r sliced).toResult = res
      have h_res_sliced : (evaluate_sl se r sliced).toResult = res := by
        rw [← h_eval_sl]
        exact h_res

      -- Case analysis on res

      rw [h_es] at h_contains
      -- Use straight_line_same_semantics to show that evaluate e r s = v
      have h_eval_s : evaluate e r s = res :=
        @straight_line_same_semantics e r se s res h_contains h_res

      -- Use straight_line_same_semantics to show that evaluate e r sliced = v
      have h_eval_sliced : evaluate e r sliced = res :=
        @straight_line_same_semantics e r se sliced res h_contains h_res_sliced

      -- Combine h_eval_s and h_eval_sliced to get the desired result
      rw [h_eval_s, h_eval_sliced]
