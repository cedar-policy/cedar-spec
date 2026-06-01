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
    by_cases hn0 : n = 0
    · -- n = 0
      simp [hn0, Cst.Unary.toExprOrSpecial?] at hu
      simp [Cst.Unary.evaluate, hn0]
      apply @Cst.Member.toAExpr?_evaluate item eos req es hu aexp heos
    · -- n ≠ 0
      simp [Cst.Unary.toExprOrSpecial?] at hu
      simp [Cst.Unary.evaluate, hn0]
      -- Bridge UInt8 ↔ Nat for n.toNat = 0 and parity (used in non-liNum arms).
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
        -- Discharge the outer evaluator match by `show`-ing the reduced form.
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
          -- Translation returns none, contradicting hu.
          rw [hcmp] at hu; simp at hu
        | .eq =>
          -- AST = (.lit Int64.MIN).dashN (n-1).toNat.  Both sides agree iff n = 1
          -- (the only odd count where Int64.MIN.neg? = none doesn't kill the chain).
          rw [hcmp] at hu
          simp at hu
          simp [← hu, ExprOrSpecial.toExpr?] at heos
          rw [← heos]
          rw [dashN_evaluate_general (Expr.lit (.int Int64.MIN.toInt64)) (n - 1).toNat req es]
          simp [evaluate]
          have hMIN_neg : Int64.MIN.toInt64.neg? = none := by decide
          rw [hMIN_neg]
          have h_eq1 : ((n - 1).toNat = 0) ↔ (n = 1) := by
            have hpos : n.toNat > 0 := by
              by_contra h0; apply hn0; apply h_zero.mp; omega
            constructor
            · intro h
              have hbound : n.toNat < 256 := n.toNat_lt
              have : n - 1 = 0 := UInt8.toNat_inj.mp (by simp; exact h)
              have : n = 1 := by
                have h2 := congrArg (· + 1) this
                simp at h2
                omega
              exact this
            · intro h; rw [h]; rfl
          simp [h_eq1]
        | .lt =>
          -- AST = (.lit (-y)).dashN (n-1).toNat where y = ofInt? x.toNat.
          -- Both sides reduce to .ok y or .ok (-y) based on parity (off-by-one).
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
            -- Step 1: derive (-y).neg? = some y.
            -- y came from Int64.ofInt? x.toNat with x.toNat in [0, Int64.MAX].
            -- We use Int64.ofInt?_toInt (-y) : ofInt? (-y).toInt = some (-y).
            -- Substituting -y for the input of neg?, we get y.neg? = some (-y),
            -- then Int64.neg?_neg? flips it.
            have hy_neg : y.neg? = some (-y) := by
              show Int64.ofInt? (-y.toInt) = some (-y)
              have hround : Int64.ofInt? ((-y).toInt) = some (-y) := Int64.ofInt?_toInt (-y)
              -- (-y).toInt = -y.toInt holds when -y.toInt is in Int64 range.
              -- y came from ofInt? (Int.ofNat x.toNat) so 0 ≤ y.toInt ≤ Int64.MAX,
              -- hence -y.toInt ∈ [-Int64.MAX, 0] is in range.
              have hy_range : Int64.MIN ≤ y.toInt ∧ y.toInt ≤ Int64.MAX := by
                by_contra hnr
                have : Int64.ofInt? y.toInt = none := by
                  apply Int64.ofInt?_none_iff.mp
                  by_cases hlo : Int64.MIN ≤ y.toInt
                  · right; by_contra hhi; apply hnr; exact ⟨hlo, by omega⟩
                  · left; omega
                rw [Int64.ofInt?_toInt] at this; cases this
              -- y.toInt = Int.ofNat x.toNat (so y is nonneg)
              have hyti_x : y.toInt = Int.ofNat x.toNat := by
                have hofInt' : Int64.ofInt? (Int.ofNat x.toNat) = some y := hofInt
                have hrange' : Int64.MIN ≤ Int.ofNat x.toNat ∧ Int.ofNat x.toNat ≤ Int64.MAX := by
                  by_contra hnr
                  have : Int64.ofInt? (Int.ofNat x.toNat) = none := by
                    apply Int64.ofInt?_none_iff.mp
                    by_cases hlo : Int64.MIN ≤ Int.ofNat x.toNat
                    · right; by_contra hhi; apply hnr; exact ⟨hlo, by omega⟩
                    · left; omega
                  rw [this] at hofInt'; cases hofInt'
                have hsome : Int64.ofInt? (Int.ofNat x.toNat) =
                             some (Int64.ofInt (Int.ofNat x.toNat)) :=
                  Int64.ofInt?_some_iff.mp hrange'
                rw [hsome] at hofInt'; injection hofInt' with hyeq
                rw [← hyeq]
                show BitVec.toInt (BitVec.ofInt 64 (Int.ofNat x.toNat)) = Int.ofNat x.toNat
                rw [BitVec.toInt_ofInt]
                have hnonneg : (Int.ofNat x.toNat : Int) ≥ 0 := Int.natCast_nonneg _
                have hmaxv : Int64.MAX = 9223372036854775807 := by decide
                have hbound : Int.ofNat x.toNat ≤ 9223372036854775807 := by
                  have := hrange'.2; rw [hmaxv] at this; exact this
                have h1 : -(2:Int)^63 ≤ Int.ofNat x.toNat := by
                  have : -(2:Int)^63 = -9223372036854775808 := by decide
                  rw [this]; omega
                have h2 : Int.ofNat x.toNat < (2:Int)^63 := by
                  have : (2:Int)^63 = 9223372036854775808 := by decide
                  rw [this]; omega
                exact Int.bmod_eq_of_le h1 h2
              have hy_nonneg : y.toInt ≥ 0 := by
                rw [hyti_x]; exact Int.natCast_nonneg _
              have hneg_range : Int64.MIN ≤ -y.toInt ∧ -y.toInt ≤ Int64.MAX := by
                simp [Int64.MIN, Int64.MAX] at hy_range ⊢; omega
              have hyti : (-y).toInt = -y.toInt := by
                show BitVec.toInt (-(y.toBitVec)) = -BitVec.toInt y.toBitVec
                rw [BitVec.toInt_neg]
                have hy : Int64.toInt y = BitVec.toInt y.toBitVec := rfl
                rw [← hy]
                apply Int.bmod_eq_of_le
                · simp [Int64.MIN] at hneg_range; omega
                · simp [Int64.MAX] at hneg_range; omega
              rw [← hyti]; exact hround
            have hneg_y : (-y).neg? = some y := Int64.neg?_neg? hy_neg
            rw [hneg_y]
            -- Step 2: parity bridging between (n-1).toNat (Nat) and n (UInt8).
            have hpos : n.toNat > 0 := by
              by_contra h0; apply hn0; apply h_zero.mp; omega
            have h_sub : (n - 1).toNat = n.toNat - 1 := by
              have h1 : (UInt8.toNat 1) = 1 := by decide
              rw [UInt8.toNat_sub, h1]
              have hbnd : n.toNat < 256 := n.toNat_lt
              omega
            rw [h_sub]
            -- LHS now uses (n.toNat - 1) parity; RHS uses n % 2.
            rcases Nat.mod_two_eq_zero_or_one n.toNat with hpar | hpar
            · -- n.toNat even ⇒ n.toNat ≥ 2 (since hpos ⇒ n.toNat ≥ 1, even ⇒ ≥ 2)
              have hge2 : n.toNat ≥ 2 := by omega
              have h1 : n.toNat - 1 ≠ 0 := by omega
              have h2 : (n.toNat - 1) % 2 = 1 := by omega
              have h3 : (n % 2 = 0) := h_par.mp hpar
              simp [h1, h2, h3]
            · -- n.toNat odd
              have h3 : n % 2 ≠ 0 := by
                intro hcontra
                have : n.toNat % 2 = 0 := h_par.mpr hcontra
                omega
              by_cases h1 : n.toNat - 1 = 0
              · -- n.toNat = 1 ⇒ (n-1).toNat = 0 ⇒ LHS = .ok (-y); RHS uses n % 2 ≠ 0 ⇒ .ok (-y)
                simp [h1, h3]
              · have h2 : (n.toNat - 1) % 2 = 0 := by omega
                simp [h1, h2, h3]
      | some .liTrue | some .liFalse | some (.liStr _) | none =>
        all_goals
          simp [hlit] at hu
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
              simp [h_zero, h_par, hn0]
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

theorem multExprFoldExtended_foldOps_agrees
  (req : Request) (es : Entities)
  (xs : List (Cst.MultOp × Cst.Unary))
  {acc_ast : Expr} {result : Expr} :
  Cst.MultExpr.foldExtended acc_ast xs = some result →
  evaluate result req es = (do
    let acc_v ← evaluate acc_ast req es
    Cst.MultExpr.foldOps acc_v xs req es) := by

  intro hres
  induction xs generalizing acc_ast result with
  | nil =>
    simp [Cst.MultExpr.foldExtended] at hres
    simp [hres, bind, Except.bind]
    cases hres : evaluate result req es with
    | error er => simp
    | ok vres => simp [Cst.MultExpr.foldOps]
  | cons x xs ih =>
    obtain ⟨op, u⟩ := x
    cases op with
    | mTimes =>
      simp [Cst.MultExpr.foldExtended] at hres
      cases heu : u.toAExpr? with
      | none => rw [heu] at hres; simp at hres
      | some eu =>
        rw [heu] at hres; simp at hres
        specialize (ih hres); simp [ih]
        sorry
    | _ => sorry

theorem Cst.MultExpr.toAExpr?_evaluate
  {mult : Cst.MultExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mult.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = mult.evaluate req es := by

  intro hmult aexp heos
  obtain ⟨initial, extended⟩ := mult
  cases extended with
  | nil =>
    simp [Cst.MultExpr.toExprOrSpecial?] at hmult
    simp [Cst.MultExpr.evaluate]
    have hinit := @Cst.Unary.toAExpr?_evaluate initial eos req es hmult aexp heos
    simp [hinit]
    cases hinit' : initial.evaluate req es
    · simp [bind, Except.bind]
    · simp [bind, Except.bind, Cst.MultExpr.foldOps]
  | cons hd tl =>




    sorry




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
