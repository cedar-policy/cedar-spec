import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.Aux

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec


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

theorem Cst.Member.toAExpr?_evaluate
  {mem : Cst.Member} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mem.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = mem.evaluate req es := by

  intro hmem aexp heos
  obtain ⟨item, access⟩ := mem
  simp [Cst.Member.toExprOrSpecial?] at hmem
  simp only [Option.bind_eq_some_iff] at hmem
  obtain ⟨peos, hitem, accs, haccs, hmem⟩ := hmem

  /- item evaluation -/
  have hitem_eval : ∃ eprim, evaluate eprim req es = item.evaluate req es := by
    have h := @Cst.Primary.toAExpr?_evaluate item peos req es hitem
    match hpeos : peos.toExpr? with
    | none =>
      exfalso
      have h_mem_fails : (⟨item, access⟩ : Cst.Member).toAExpr? = none := by
        apply item_none_member_none
        simp [Cst.Primary.toAExpr?, hitem, hpeos]
      simp [Cst.Member.toAExpr?, Cst.Member.toExprOrSpecial?,
          hitem, haccs, hmem] at h_mem_fails
      rw [h_mem_fails] at heos
      simp at heos
    | some eprim =>
      exists eprim
      apply (h _ hpeos)
  obtain ⟨eprim, hitem_eval⟩ := hitem_eval
  unfold Cst.Member.evaluate

  /- AttrChain agreement -/
  match hattr : Cst.AttrChain? access with
  | none =>
    exfalso
    exact attrChain?_isSome_of_mapM_toAstAccessor? access accs haccs hattr
  | some attrs =>
    have hagr : attrsAccessorsAgree accs attrs = true :=
      toAstAccessor_attrChain_agrees access accs attrs haccs hattr

    /- memberAux / foldGetAttr agreement -/
    match hpeos : peos.toExpr? with
    | none =>
      exfalso
      have h_mem_fails : (⟨item, access⟩ : Cst.Member).toAExpr? = none := by
        apply item_none_member_none
        simp [Cst.Primary.toAExpr?, hitem, hpeos]
      simp [Cst.Member.toAExpr?, Cst.Member.toExprOrSpecial?,
            hitem, haccs, hmem] at h_mem_fails
      rw [h_mem_fails] at heos
      simp at heos
    | some eprim' =>
      have hheadEval : evaluate eprim' req es = item.evaluate req es :=
        Cst.Primary.toAExpr?_evaluate hitem _ hpeos
      rw [memberAux_foldGetAttr_agrees_aux accs attrs req es hpeos hmem heos hagr,
          hheadEval]






theorem Cst.Expr.toAExpr?_evaluate
  {e : Cst.Expr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  e.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = e.evaluate req es := by sorry

theorem Cst.Expr.toAExpr?_sound
  {e : Cst.Expr} {aexp : Expr} {req : Request} {es : Entities} :
  e.toAExpr? = some aexp →
  evaluate aexp req es = e.evaluate req es := by
  intro h
  simp [Cst.Expr.toAExpr?] at h;
  cases heos : e.toExprOrSpecial? with
  | none => simp [heos] at h
  | some eos =>
    apply (@Cst.Expr.toAExpr?_evaluate _ _ req es heos aexp)
    simp [heos] at h; exact h

-- theorem expr_translation_sound (cexp : Cst.Expr) (aexp : Expr) (req : Request) (es : Entities) :
--   cexp.toAExpr? = some aexp →
--   cexp.evaluate req es = evaluate aexp req es := by sorry


end
