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
      cases hitemEval : item.evaluate req es with
      | error e =>
        rw [memberAux_foldGetAttr_agrees_aux accs attrs req es hpeos hmem heos hagr,
            hheadEval, hitemEval]
      | ok head =>
        rw [memberAux_foldGetAttr_agrees item head accs attrs req es
              hitem hpeos hmem heos hheadEval hitemEval hagr]
        simp [bind, Except.bind]

theorem Cst.Unary.toAExpr?_evaluate
  {u : Cst.Unary} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  u.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = u.evaluate req es := by

  intro hu aexp heos
  obtain ⟨op, item⟩ := u
  match hop : op with
  | none =>
    simp [Cst.Unary.toExprOrSpecial?] at hu
    simp [Cst.Unary.evaluate]
    apply @Cst.Member.toAExpr?_evaluate item eos req es hu aexp heos
  | some (.nDash 0) =>
    simp [Cst.Unary.toExprOrSpecial?] at hu
    simp [Cst.Unary.evaluate]
    apply @Cst.Member.toAExpr?_evaluate item eos req es hu aexp heos
  | some (.nBang n) =>
    simp [Cst.Unary.toExprOrSpecial?] at hu
    simp [Cst.Unary.evaluate]
    cases hitem_trans : item.toExprOrSpecial? with
    | none => simp [hitem_trans] at hu
    | some ieos =>
      simp [hitem_trans] at hu
      cases hioes_trans : ieos.toExpr? with
      | none => simp [hioes_trans] at hu
      | some iexp =>
        simp [hioes_trans] at hu
        simp [←hu, ExprOrSpecial.toExpr?] at heos
        rw [← heos]
        have hitem_eval : evaluate iexp req es = item.evaluate req es :=
          @Cst.Member.toAExpr?_evaluate item ieos req es hitem_trans iexp hioes_trans
        rw [bangN_evaluate_general iexp n.toNat req es, hitem_eval]
        have h_zero : (n.toNat = 0) ↔ (n = 0) := by
          constructor
          · intro h; exact UInt8.toNat_inj.mp (by simp [h])
          · intro h; rw [h]; rfl
        have h_par : (n.toNat % 2 = 0) ↔ (n % 2 = 0) := by
          rw [show n.toNat % 2 = (n % 2).toNat from by rw [UInt8.toNat_mod]; rfl]
          constructor
          · intro h; exact UInt8.toNat_inj.mp (by simp [h])
          · intro h; rw [h]; rfl
        simp [h_zero, h_par]
        by_cases hn : n = 0
        · simp [hn]
          cases item.evaluate req es <;> rfl
        · simp [hn]
          cases hev : item.evaluate req es with
          | error err => simp [bind, Except.bind]
          | ok v =>
            simp [bind, Except.bind]
            cases v with
            | prim p => cases p <;> simp
            | _ => simp
  | some (.nDash n) =>
    -- The previous `some (.nDash 0)` arm caught the n=0 case, so n ≠ 0 here.
    -- But we can't extract that without an explicit by_cases on n = 0.
    by_cases hn0 : n = 0
    · -- This arm is unreachable when n = 0 (caught by the prior pattern).
      -- We have to discharge it anyway. The translator's nDash branch with n=0
      -- collapses to `e.item.toExprOrSpecial?` (per the explicit nDash 0 arm
      -- earlier in `Cst.Unary.toExprOrSpecial?`), so the proof is the same.
      simp [hn0, Cst.Unary.toExprOrSpecial?] at hu
      simp [Cst.Unary.evaluate, hn0]
      apply @Cst.Member.toAExpr?_evaluate item eos req es hu aexp heos
    · -- Main case: n ≠ 0.  Match the translator's split on item.toLit?.
      simp [Cst.Unary.toExprOrSpecial?] at hu
      simp [Cst.Unary.evaluate, hn0]
      -- Bridge UInt8 ↔ Nat for n.toNat = 0 and parity.
      have h_zero : (n.toNat = 0) ↔ (n = 0) := by
        constructor
        · intro h; exact UInt8.toNat_inj.mp (by simp [h])
        · intro h; rw [h]; rfl
      have h_par : (n.toNat % 2 = 0) ↔ (n % 2 = 0) := by
        rw [show n.toNat % 2 = (n % 2).toNat from by rw [UInt8.toNat_mod]; rfl]
        constructor
        · intro h; exact UInt8.toNat_inj.mp (by simp [h])
        · intro h; rw [h]; rfl
      match hlit : CstCommon.Member.toLit? item with
      | some (.liNum x) =>
        simp [hlit] at hu
        show evaluate aexp req es = (
          match compare x.toNat (Int64.MAX + 1).toNat with
          | .eq =>
            if n = 1 then .ok (.prim (.int Int64.MIN.toInt64)) else .error .arithBoundsError
          | .lt =>
            match Int64.ofInt? ↑x.toNat with
            | some y =>
              if n % 2 = 0 then .ok (.prim (.int y)) else .ok (.prim (.int (-y)))
            | none => .error .arithBoundsError
          | .gt => .error .arithBoundsError)
        match hcmp : compare x.toNat (Int64.MAX + 1).toNat with
        | .gt =>
          rw [hcmp] at hu; simp at hu
        | .eq =>
          rw [hcmp] at hu
          simp at hu
          simp [← hu, ExprOrSpecial.toExpr?] at heos
          rw [← heos]
          rw [dashN_evaluate_general (Expr.lit (.int Int64.MIN.toInt64)) (n - 1).toNat req es]
          simp [evaluate]
          -- Int64.MIN.toInt64.neg? = none (computable; check via decide).
          have hMIN_neg : Int64.MIN.toInt64.neg? = none := by decide
          rw [hMIN_neg]
          -- Bridge `(n-1).toNat = 0 ↔ n = 1` (UInt8).
          have h_eq1 : ((n - 1).toNat = 0) ↔ (n = 1) := by
            have hpos : n.toNat > 0 := by
              by_contra h0
              apply hn0
              apply h_zero.mp
              omega
            constructor
            · intro h
              -- (n-1).toNat = 0 in UInt8.  We need n.toNat = 1.
              -- (n-1).toNat = (n.toNat + (256 - 1)) % 256 = (n.toNat + 255) % 256
              -- = 0 iff n.toNat = 1 (when n.toNat ≤ 255 which always holds for UInt8).
              have hbound : n.toNat < 256 := n.toNat_lt
              have : n - 1 = 0 := UInt8.toNat_inj.mp (by simp; exact h)
              -- From n - 1 = 0 and n ≠ 0, get n = 1.
              have : n = 1 := by
                have h2 := congrArg (· + 1) this
                simp at h2
                omega
              exact this
            · intro h; rw [h]; rfl
          simp [h_eq1]
        | .lt =>
          rw [hcmp] at hu
          simp at hu
          cases hofInt : Int64.ofInt? (x.toNat : Int) with
          | none => rw [hofInt] at hu; cases hu
          | some y =>
            rw [hofInt] at hu
            simp at hu
            simp [← hu, ExprOrSpecial.toExpr?] at heos
            rw [← heos]
            rw [dashN_evaluate_general (Expr.lit (.int (-y))) (n - 1).toNat req es]
            simp [evaluate]
            -- The .lt arm needs (-y).neg? = some y plus a parity bridge between
            -- (n-1).toNat (UInt8) and n (UInt8). The math works out (since y is
            -- in [0, Int64.MAX], -y is in [-Int64.MAX, 0], and (-y).neg? = some y),
            -- but the proof requires multiple Int64 helpers not currently exposed.
            sorry
      | some .liTrue | some .liFalse | some (.liStr _) | none =>
        all_goals
          simp [hlit] at hu
          -- hu now has the form: ... = some eos using the dashN n.toNat fallback
          cases hitem_trans : item.toExprOrSpecial? with
          | none => simp [hitem_trans] at hu
          | some ieos =>
            simp [hitem_trans] at hu
            cases hioes_trans : ieos.toExpr? with
            | none => simp [hioes_trans] at hu
            | some iexp =>
              simp [hioes_trans] at hu
              simp [←hu, ExprOrSpecial.toExpr?] at heos
              rw [← heos]
              have hitem_eval : evaluate iexp req es = item.evaluate req es :=
                @Cst.Member.toAExpr?_evaluate item ieos req es hitem_trans iexp hioes_trans
              rw [dashN_evaluate_general iexp n.toNat req es, hitem_eval]
              simp [hlit, h_zero, h_par, hn0]
              cases hev : item.evaluate req es with
              | error err => simp [bind, Except.bind]
              | ok v =>
                simp [bind, Except.bind]
                cases v with
                | prim p =>
                  cases p with
                  | int i => simp; rfl
                  | _ => simp
                | _ => simp
  | some .nOverBang => simp [Cst.Unary.toExprOrSpecial?] at hu
  | some .nOverDash => simp [Cst.Unary.toExprOrSpecial?] at hu






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
