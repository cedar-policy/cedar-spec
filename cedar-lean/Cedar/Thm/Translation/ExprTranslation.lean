import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec


theorem Cst.Ident.toUnreservedString?_eq_toString
    {i : Cst.Ident} {s : String} :
    i.toUnreservedString? = some s →
    s = CstCommon.Ident.toString i := by
  cases i <;> intro h <;> simp [Cst.Ident.toUnreservedString?] at h
  all_goals first | rfl | (rw [← h]; rfl)

/-- If `mapM` over `toUnreservedString?` succeeds, the result equals `map toString`. -/
theorem mapM_toUnreservedString?_eq_map
    {l : List Cst.Ident} {result : List String} :
    l.mapM Cst.Ident.toUnreservedString? = some result →
    result = l.map CstCommon.Ident.toString := by
  induction l generalizing result with
  | nil =>
    intro h
    simp [List.mapM, List.mapM.loop] at h
    simp [← h]
  | cons hd tl ih =>
    intro h
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨s, hs, rest, hrest, heq⟩ := h
    simp [List.map, ← heq]
    exact ⟨Cst.Ident.toUnreservedString?_eq_toString hs, ih hrest⟩

/-- `toAName?` produces the same `Spec.Name` the evaluator builds. -/
theorem Cst.Name.toAName?_agrees
    {n : Cst.Name} {an : Spec.Name} :
    n.toAName? = some an →
    an = { id := n.name.toString,
           path := n.path.map CstCommon.Ident.toString } := by
  intro h
  simp [Cst.Name.toAName?, Option.bind_eq_some_iff] at h
  obtain ⟨id, hid, path, hpath, han⟩ := h
  rw [← han]; congr 1
  · exact Cst.Ident.toUnreservedString?_eq_toString hid
  · exact mapM_toUnreservedString?_eq_map hpath

theorem Cst.Name.toVar?_agrees
    {n : Cst.Name} {v : Var} :
    n.toVar? = some v →
    n.path = [] ∧
    match v with
    | .principal => n.name = Cst.Ident.idPrincipal
    | .action    => n.name = Cst.Ident.idAction
    | .resource  => n.name = Cst.Ident.idResource
    | .context   => n.name = Cst.Ident.idContext := by
  intro h
  simp [Cst.Name.toVar?] at h
  obtain ⟨hpath, hname⟩ := h
  refine ⟨hpath, ?_⟩
  cases hn : n.name <;> rw [hn] at hname <;> simp at hname <;>
    cases v <;> simp_all


mutual

theorem Cst.ExprOrSpecial.toExpr?_evaluate  {eos : ExprOrSpecial} {aexp : Expr} req es:
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

theorem Cst.Primary.toAExpr?_evaluate
  {prim : Cst.Primary} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  prim.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = prim.evaluate req es := by
  cases prim with

  | literal lit =>
    intro hprim aexp heos
    have haexp_eval := Cst.ExprOrSpecial.toExpr?_evaluate req es heos
    rw [haexp_eval]; clear haexp_eval;
    simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at hprim
    cases lit with
    | liTrue | liFalse =>
      simp at hprim; rw [← hprim]; unfold Cst.Primary.evaluate; simp
    | liNum n =>
      simp at hprim; cases hn: Int64.ofInt? ↑n.toNat with
      | none => rw [hn] at hprim; simp at hprim
      | some n' =>
        rw [hn] at hprim; simp at hprim; rw [← hprim]; simp
        simp [evaluate, Cst.Primary.evaluate, hn];
    | liStr s =>
      simp at hprim; rw [←hprim]
      simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString];
      cases hs : (CstCommon.unescape? s) with
      | none => simp; rfl
      | some s' => simp; rfl

  | ref r =>
    intro href aexp heos
    have haexp_eval := Cst.ExprOrSpecial.toExpr?_evaluate req es heos
    rw [haexp_eval]; clear haexp_eval
    simp [Cst.Primary.toExprOrSpecial?] at href
    cases r with
    | uid path eid =>
      let (.string s) := eid
      simp [Cst.Ref.toExprOrSpecial?] at href;
      simp only [Option.bind_eq_some_iff] at href
      obtain ⟨ty, hty, su, hsu1, hsu2⟩ := href
      simp at hsu2; rw [← hsu2]; simp [evaluate]
      simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString]
      cases hs : CstCommon.unescape? s with
      | none => rw [hs] at hsu1; contradiction
      | some su' =>
        rw [hs] at hsu1; simp at hsu1
        simp [hsu1, bind, Except.bind]
        exact (Cst.Name.toAName?_agrees hty)
    | ref path rinits => simp [Cst.Ref.toExprOrSpecial?] at href

  | name n =>
    intro hname aexp heos
    have haexp_eval := Cst.ExprOrSpecial.toExpr?_evaluate req es heos
    rw [haexp_eval]; clear haexp_eval
    simp [Cst.Primary.toExprOrSpecial?] at hname
    unfold Cst.Primary.evaluate
    cases hvar : n.toVar? with
    | none =>
      simp [hvar] at hname
      simp only [Option.bind_eq_some_iff] at hname
      obtain ⟨name, hname1, hname2 ⟩ := hname
      simp at hname2; rw [← hname2] at heos;
      simp [ExprOrSpecial.toExpr?] at heos
    | some v =>
      simp [hvar] at hname; simp [← hname]
      cases hpath : n.path with
      | nil =>
        simp; unfold evaluate;
        have ⟨hvn1, hvn2⟩ := Cst.Name.toVar?_agrees hvar
        cases hv : v with
        | principal => simp [hv] at hvn2; simp [hvn2]
        | action => simp [hv] at hvn2; simp [hvn2]
        | resource => simp [hv] at hvn2; simp [hvn2]
        | context => simp [hv] at hvn2; simp [hvn2]
      | cons hd tl =>
        have ⟨hvn1, hvn2⟩ := Cst.Name.toVar?_agrees hvar
        simp [hvn1] at hpath

  | expr e => sorry


  | eList es => sorry







theorem Cst.Expr.toAExpr?_evaluate
  (e : Cst.Expr) (eos : ExprOrSpecial)
  (req : Request) (es : Entities) :
  e.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = e.evaluate req es := by sorry

theorem Cst.Expr.toAExpr?_sound
    (e : Cst.Expr) (aexp : Expr) (req : Request) (es : Entities) :
    e.toAExpr? = some aexp →
    evaluate aexp req es = e.evaluate req es := by sorry

-- theorem expr_translation_sound (cexp : Cst.Expr) (aexp : Expr) (req : Request) (es : Entities) :
--   cexp.toAExpr? = some aexp →
--   cexp.evaluate req es = evaluate aexp req es := by sorry


end
