import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.Aux

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec


mutual

theorem Cst.ExprOrSpecial.toExpr?_evaluate  {eos : ExprOrSpecial} {aexp : Expr} req es :
  eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  (match eos with
    | .expr e => evaluate e req es
    | .var var => evaluate (Expr.var var) req es
    | .strLit s => (CstCommon.unescape? s).elim
              (.error .typeError)
              (fun s' => .ok (.prim (.string s')))
    | .boolLit b => .ok (.prim (.bool b))
    | .name _ => .error .typeError) = .ok v := by
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
  ∀ v, evaluate aexp req es = .ok v ↔
  prim.evaluate req es = .ok v := by

  cases prim with
  | literal lit =>
    intro hprim aexp heos v
    have haexp_iff := Cst.ExprOrSpecial.toExpr?_evaluate req es heos v
    rw [haexp_iff]; clear haexp_iff
    simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at hprim
    cases lit with
    | liTrue | liFalse =>
      simp at hprim; rw [← hprim]; unfold Cst.Primary.evaluate; simp
    | liNum n =>
      simp at hprim
      cases hn : Int64.ofInt? ↑n.toNat with
      | none => rw [hn] at hprim; simp at hprim
      | some n' =>
        rw [hn] at hprim; simp at hprim; rw [← hprim]
        simp [evaluate, Cst.Primary.evaluate, hn]
    | liStr s =>
      simp at hprim; rw [← hprim]
      simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString, bind, Except.bind]
      cases hs : CstCommon.unescape? s <;> simp

  | ref r =>
    intro href aexp heos v
    have haexp_iff := Cst.ExprOrSpecial.toExpr?_evaluate req es heos v
    rw [haexp_iff]; clear haexp_iff
    simp [Cst.Primary.toExprOrSpecial?] at href
    cases r with
    | uid path eid =>
      let (.string s) := eid
      simp [Cst.Ref.toExprOrSpecial?] at href
      simp only [Option.bind_eq_some_iff] at href
      obtain ⟨ty, hty, su, hsu1, hsu2⟩ := href
      simp at hsu2; rw [← hsu2]
      simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString]
      cases hs : CstCommon.unescape? s with
      | none => rw [hs] at hsu1; contradiction
      | some su' =>
        rw [hs] at hsu1; simp at hsu1
        simp [hsu1, bind, Except.bind]
        simp [evaluate, Cst.Name.toAName?_agrees hty]
    | ref path rinits => simp [Cst.Ref.toExprOrSpecial?] at href

  | name n =>
    intro hname aexp heos v
    have haexp_iff := Cst.ExprOrSpecial.toExpr?_evaluate req es heos v
    rw [haexp_iff]; clear haexp_iff
    simp [Cst.Primary.toExprOrSpecial?] at hname
    unfold Cst.Primary.evaluate
    cases hvar : n.toVar? with
    | none =>
      simp [hvar] at hname
      simp only [Option.bind_eq_some_iff] at hname
      obtain ⟨name, hname1, hname2⟩ := hname
      simp at hname2; rw [← hname2] at heos
      simp [ExprOrSpecial.toExpr?] at heos
    | some var =>
      simp [hvar] at hname; simp [← hname]
      cases hpath : n.path with
      | nil =>
        simp
        have ⟨hvn1, hvn2⟩ := Cst.Name.toVar?_agrees hvar
        cases hv : var with
        | principal => simp [hv] at hvn2; simp [evaluate, hvn2]
        | action => simp [hv] at hvn2; simp [evaluate, hvn2]
        | resource => simp [hv] at hvn2; simp [evaluate, hvn2]
        | context => simp [hv] at hvn2; simp [evaluate, hvn2]
      | cons hd tl =>
        have ⟨hvn1, _⟩ := Cst.Name.toVar?_agrees hvar
        simp [hvn1] at hpath

  | expr e => sorry
  | eList es => sorry

theorem Cst.Member.toAExpr?_evaluate
  {mem : Cst.Member} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mem.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  mem.evaluate req es = .ok v := by

  intro hmem aexp heos v
  obtain ⟨item, access⟩ := mem
  simp [Cst.Member.toExprOrSpecial?] at hmem
  simp only [Option.bind_eq_some_iff] at hmem
  obtain ⟨peos, hitem, accs, haccs, hmem⟩ := hmem
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
      have hheadIff : ∀ vp, evaluate eprim' req es = .ok vp ↔ item.evaluate req es = .ok vp :=
        Cst.Primary.toAExpr?_evaluate hitem _ hpeos
      -- Forward direction: AST .ok v → CST .ok v.
      constructor
      · intro hev_ok
        -- aexp evaluates to .ok v.  By memberAux_foldGetAttr_agrees_aux, this means
        -- the do-block on eprim' produces .ok v.  That requires evaluate eprim' = .ok vp
        -- for some vp, then the foldlM produces .ok v.  Use hheadIff to lift to item side.
        rw [memberAux_foldGetAttr_agrees_aux accs attrs req es hpeos hmem heos hagr] at hev_ok
        simp [bind, Except.bind] at hev_ok
        cases h_eprim : evaluate eprim' req es with
        | error err => rw [h_eprim] at hev_ok; simp at hev_ok
        | ok head =>
          rw [h_eprim] at hev_ok; simp at hev_ok
          rw [(hheadIff head).mp h_eprim]
          simp [bind, Except.bind, hev_ok]
      · intro hev_ok
        rw [memberAux_foldGetAttr_agrees_aux accs attrs req es hpeos hmem heos hagr]
        simp [bind, Except.bind] at hev_ok
        cases h_item : item.evaluate req es with
        | error err => rw [h_item] at hev_ok; simp at hev_ok
        | ok head =>
          rw [h_item] at hev_ok; simp at hev_ok
          rw [(hheadIff head).mpr h_item]
          simp [bind, Except.bind, hev_ok]

theorem Cst.Unary.toAExpr?_evaluate
  {u : Cst.Unary} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  u.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  u.evaluate req es = .ok v := by

  intro hu aexp heos v
  obtain ⟨op, item⟩ := u
  match hop : op with
  | none =>
    simp [Cst.Unary.toExprOrSpecial?] at hu
    simp [Cst.Unary.evaluate]
    exact Cst.Member.toAExpr?_evaluate hu aexp heos v
  | some (.nDash 0) =>
    simp [Cst.Unary.toExprOrSpecial?] at hu
    simp [Cst.Unary.evaluate]
    exact Cst.Member.toAExpr?_evaluate hu aexp heos v
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
        simp [← hu, ExprOrSpecial.toExpr?] at heos
        rw [← heos]
        have hitem_iff : ∀ vp, evaluate iexp req es = .ok vp ↔ item.evaluate req es = .ok vp :=
          Cst.Member.toAExpr?_evaluate hitem_trans iexp hioes_trans
        rw [bangN_evaluate_general iexp n.toNat req es]
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
        -- Forward and backward of the iff together — build it via constructor.
        constructor
        · intro hev_ok
          -- Discriminate by what evaluate iexp produced.
          cases h_iexp : evaluate iexp req es with
          | error err =>
            rw [h_iexp] at hev_ok; simp at hev_ok
          | ok vp =>
            rw [h_iexp] at hev_ok
            have h_item := (hitem_iff vp).mp h_iexp
            simp [h_item, bind, Except.bind]
            by_cases hn : n = 0
            · simp [hn] at hev_ok ⊢
              exact hev_ok
            · simp [hn] at hev_ok ⊢
              -- The match on vp yields .ok ... or .error.
              cases vp with
              | prim p =>
                cases p with
                | bool b => simp at hev_ok ⊢; exact hev_ok
                | _ => simp at hev_ok
              | _ => simp at hev_ok
        · intro hev_ok
          -- CST side .ok v.  Expand u.evaluate to see vp from item.evaluate.
          cases h_item : item.evaluate req es with
          | error err => rw [h_item] at hev_ok; simp [bind, Except.bind] at hev_ok
          | ok vp =>
            rw [h_item] at hev_ok
            have h_iexp := (hitem_iff vp).mpr h_item
            rw [h_iexp]
            simp [bind, Except.bind] at hev_ok ⊢
            by_cases hn : n = 0
            · simp [hn] at hev_ok ⊢; exact hev_ok
            · simp [hn] at hev_ok ⊢
              cases vp with
              | prim p =>
                cases p with
                | bool b => simp at hev_ok ⊢; exact hev_ok
                | _ => simp at hev_ok
              | _ => simp at hev_ok
  | some (.nDash n) =>
    by_cases hn0 : n = 0
    · -- Already handled by the prior `nDash 0` arm; defensively handle here too.
      simp [hn0, Cst.Unary.toExprOrSpecial?] at hu
      simp [Cst.Unary.evaluate, hn0]
      exact Cst.Member.toAExpr?_evaluate hu aexp heos v
    · simp [Cst.Unary.toExprOrSpecial?] at hu
      simp [Cst.Unary.evaluate, hn0]
      have h_zero : (n.toNat = 0) ↔ (n = 0) := by
        constructor
        · intro h; exact UInt8.toNat_inj.mp (by simp [h])
        · intro h; rw [h]; rfl
      have h_par : (n.toNat % 2 = 0) ↔ (n % 2 = 0) := by
        rw [show n.toNat % 2 = (n % 2).toNat from by rw [UInt8.toNat_mod]; rfl]
        constructor
        · intro h; exact UInt8.toNat_inj.mp (by simp [h])
        · intro h; rw [h]; rfl
      have hpos : n.toNat > 0 := by
        by_contra h0; apply hn0; apply h_zero.mp; omega
      have h_sub : (n - 1).toNat = n.toNat - 1 := by
        have h1 : (UInt8.toNat 1) = 1 := by decide
        rw [UInt8.toNat_sub, h1]
        have hbnd : n.toNat < 256 := n.toNat_lt
        omega
      match hlit : CstCommon.Member.toLit? item with
      | some (.liNum x) =>
        simp [hlit] at hu
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
          have hMIN_neg : Int64.MIN.toInt64.neg? = none := by decide
          rw [hMIN_neg]
          have h_eq1 : ((n - 1).toNat = 0) ↔ (n = 1) := by
            constructor
            · intro h
              have : n - 1 = 0 := UInt8.toNat_inj.mp (by simp; exact h)
              have h2 := congrArg (· + 1) this
              simp at h2
              omega
            · intro h; rw [h]; rfl
          simp [h_eq1, hcmp]
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
            have hy_neg : y.neg? = some (-y) := by
              show Int64.ofInt? (-y.toInt) = some (-y)
              have hround : Int64.ofInt? ((-y).toInt) = some (-y) := Int64.ofInt?_toInt (-y)
              have hy_range : Int64.MIN ≤ y.toInt ∧ y.toInt ≤ Int64.MAX := by
                by_contra hnr
                have : Int64.ofInt? y.toInt = none := by
                  apply Int64.ofInt?_none_iff.mp
                  by_cases hlo : Int64.MIN ≤ y.toInt
                  · right; by_contra hhi; apply hnr; exact ⟨hlo, by omega⟩
                  · left; omega
                rw [Int64.ofInt?_toInt] at this; cases this
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
                have hmaxv : Int64.MAX = 9223372036854775807 := by decide
                have hbound : Int.ofNat x.toNat ≤ 9223372036854775807 := by
                  have := hrange'.2; rw [hmaxv] at this; exact this
                have h1 : -(2:Int)^63 ≤ Int.ofNat x.toNat := by
                  have hnn : (Int.ofNat x.toNat : Int) ≥ 0 := Int.natCast_nonneg _
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
            rw [h_sub]
            rcases Nat.mod_two_eq_zero_or_one n.toNat with hpar | hpar
            · have hge2 : n.toNat ≥ 2 := by omega
              have h1 : n.toNat - 1 ≠ 0 := by omega
              have h2 : (n.toNat - 1) % 2 = 1 := by omega
              have h3 : (n % 2 = 0) := h_par.mp hpar
              simp [h1, h2, h3, hcmp, hofInt]
            · have h3 : n % 2 ≠ 0 := by
                intro hcontra
                have : n.toNat % 2 = 0 := h_par.mpr hcontra
                omega
              by_cases h1 : n.toNat - 1 = 0
              · simp [h1, h3, hcmp, hofInt]
              · have h2 : (n.toNat - 1) % 2 = 0 := by omega
                simp [h1, h2, h3, hcmp, hofInt]
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
              simp [← hu, ExprOrSpecial.toExpr?] at heos
              rw [← heos]
              have hitem_iff : ∀ vp, evaluate iexp req es = .ok vp ↔ item.evaluate req es = .ok vp :=
                Cst.Member.toAExpr?_evaluate hitem_trans iexp hioes_trans
              rw [dashN_evaluate_general iexp n.toNat req es]
              simp [h_zero, h_par, hn0]
              constructor
              · intro hev_ok
                cases h_iexp : evaluate iexp req es with
                | error err => rw [h_iexp] at hev_ok; simp at hev_ok
                | ok vp =>
                  rw [h_iexp] at hev_ok
                  have h_item := (hitem_iff vp).mp h_iexp
                  simp [h_item, bind, Except.bind]
                  cases vp with
                  | prim p =>
                    cases p with
                    | int i => simp at hev_ok ⊢; exact hev_ok
                    | _ => simp at hev_ok
                  | _ => simp at hev_ok
              · intro hev_ok
                cases h_item : item.evaluate req es with
                | error err => rw [h_item] at hev_ok; simp [bind, Except.bind] at hev_ok
                | ok vp =>
                  rw [h_item] at hev_ok
                  have h_iexp := (hitem_iff vp).mpr h_item
                  rw [h_iexp]
                  simp [bind, Except.bind] at hev_ok ⊢
                  cases vp with
                  | prim p =>
                    cases p with
                    | int i => simp at hev_ok ⊢; exact hev_ok
                    | _ => simp at hev_ok
                  | _ => simp at hev_ok
  | some .nOverBang => simp [Cst.Unary.toExprOrSpecial?] at hu
  | some .nOverDash => simp [Cst.Unary.toExprOrSpecial?] at hu

theorem multExprFoldExtended_foldOps_agrees
  (req : Request) (es : Entities)
  (xs : List (Cst.MultOp × Cst.Unary))
  {acc_ast : Expr} {result : Expr} :
  Cst.MultExpr.foldExtended acc_ast xs = some result →
  ∀ v, evaluate result req es = .ok v ↔
       (do let acc_v ← evaluate acc_ast req es
           Cst.MultExpr.foldOps acc_v xs req es) = .ok v := by

  intro hfold v
  induction xs generalizing acc_ast result with
  | nil =>
    simp [Cst.MultExpr.foldExtended] at hfold
    simp [hfold]; constructor <;> intro h
    · simp [h, bind, Except.bind]
      simp [Cst.MultExpr.foldOps]
    · cases hres : evaluate result req es with
      | error err =>
        simp [bind, Except.bind, hres] at h
      | ok v' =>
        simp [bind, Except.bind, hres] at h
        simp [Cst.MultExpr.foldOps] at h
        rw [h]

  | cons x xs ih =>
    obtain ⟨op, u⟩ := x
    -- Translator only succeeds on .mTimes; other ops fail and contradict hfold.
    cases hop : op with
    | mTimes =>
      simp [Cst.MultExpr.foldExtended, hop] at hfold
      cases hu : u.toAExpr? with
      | none => rw [hu] at hfold; simp at hfold
      | some eu =>
        rw [hu] at hfold
        simp at hfold
        have ih' := ih hfold
        rw [ih']
        simp [Cst.Unary.toAExpr?, Option.bind_eq_some_iff] at hu
        obtain ⟨ueos, hueos, heu⟩ := hu
        have hu_iff : ∀ vp, evaluate eu req es = .ok vp ↔ u.evaluate req es = .ok vp :=
          Cst.Unary.toAExpr?_evaluate hueos eu heu
        -- Reduce both sides' do-notation and align via case splits.
        simp [evaluate, bind, Except.bind, Cst.MultExpr.foldOps]
        cases h_acc : evaluate acc_ast req es with
        | error err => simp
        | ok acc_v =>
          simp
          cases h_eu : evaluate eu req es with
          | error err =>
            simp
            -- evaluate eu errors ⇒ u.evaluate also errors (or returns non-ok); RHS shorts.
            cases h_u : u.evaluate req es with
            | error _ => simp
            | ok u_v =>
              -- contradiction: hu_iff u_v says evaluate eu = .ok u_v but h_eu = .error.
              have := (hu_iff u_v).mpr h_u
              rw [this] at h_eu; cases h_eu
          | ok eu_v =>
            simp
            have hu_v := (hu_iff eu_v).mp h_eu
            rw [hu_v]
    | _ =>
      simp [Cst.MultExpr.foldExtended, hop] at hfold

theorem Cst.MultExpr.toAExpr?_evaluate
  {mult : Cst.MultExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mult.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  mult.evaluate req es = .ok v := by

  intro hmult aexp heos v
  obtain ⟨initial, extended⟩ := mult
  match hext : extended with
  | [] =>
    subst hext
    simp only [Cst.MultExpr.toExprOrSpecial?] at hmult
    have hu_iff := @Cst.Unary.toAExpr?_evaluate initial eos req es hmult aexp heos v
    rw [hu_iff]
    simp [Cst.MultExpr.evaluate]
    cases h_init : initial.evaluate req es with
    | error err => simp [bind, Except.bind]
    | ok iv => simp [bind, Except.bind, Cst.MultExpr.foldOps]
  | hd :: tl =>
    subst hext
    simp [Cst.MultExpr.toExprOrSpecial?, Option.bind_eq_some_iff] at hmult
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hmult
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [multExprFoldExtended_foldOps_agrees req es _ hres v]
    simp [Cst.Unary.toAExpr?, Option.bind_eq_some_iff] at hfirst
    obtain ⟨ueos, hueos, hfeu⟩ := hfirst
    have hu_iff : ∀ vp, evaluate first req es = .ok vp ↔ initial.evaluate req es = .ok vp :=
      Cst.Unary.toAExpr?_evaluate hueos first hfeu
    simp [Cst.MultExpr.evaluate]
    cases h_init : initial.evaluate req es with
    | error err =>
      simp [bind, Except.bind]
      cases h_first : evaluate first req es with
      | ok vp =>
        have := (hu_iff vp).mp h_first
        rw [this] at h_init; cases h_init
      | error _ => simp
    | ok iv =>
      simp [bind, Except.bind]
      have h_first : evaluate first req es = .ok iv := (hu_iff iv).mpr h_init
      rw [h_first]

/-- Fold-helper analog for `AddExpr`. Mirrors `multExprFoldExtended_foldOps_agrees`
    with `aPlus`/`aMinus` instead of `mTimes`, `MultExpr` instead of `Unary`,
    and `apply₂ .add`/`apply₂ .sub` instead of `apply₂ .mul`. -/
theorem addExprFoldExtended_foldOps_agrees
  (req : Request) (es : Entities)
  (xs : List (Cst.AddOp × Cst.MultExpr))
  {acc_ast : Expr} {result : Expr} :
  Cst.AddExpr.foldExtended acc_ast xs = some result →
  ∀ v, evaluate result req es = .ok v ↔
       (do let acc_v ← evaluate acc_ast req es
           Cst.AddExpr.foldOps acc_v xs req es) = .ok v := by
  intro hfold v
  induction xs generalizing acc_ast result with
  | nil =>
    simp [Cst.AddExpr.foldExtended] at hfold
    simp [hfold]; constructor <;> intro h
    · simp [h, bind, Except.bind, Cst.AddExpr.foldOps]
    · cases hres : evaluate result req es with
      | error err => simp [bind, Except.bind, hres] at h
      | ok v' =>
        simp [bind, Except.bind, hres] at h
        simp [Cst.AddExpr.foldOps] at h
        rw [h]
  | cons x xs ih =>
    obtain ⟨op, m⟩ := x
    cases hop : op with
    | aPlus =>
      simp [Cst.AddExpr.foldExtended, hop] at hfold
      cases hm : m.toAExpr? with
      | none => rw [hm] at hfold; simp at hfold
      | some em =>
        rw [hm] at hfold
        simp at hfold
        have ih' := ih hfold
        rw [ih']
        simp [Cst.MultExpr.toAExpr?, Option.bind_eq_some_iff] at hm
        obtain ⟨meos, hmeos, hmem⟩ := hm
        have hm_iff : ∀ vp, evaluate em req es = .ok vp ↔ m.evaluate req es = .ok vp :=
          Cst.MultExpr.toAExpr?_evaluate hmeos em hmem
        simp [evaluate, bind, Except.bind, Cst.AddExpr.foldOps]
        cases h_acc : evaluate acc_ast req es with
        | error err => simp
        | ok acc_v =>
          simp
          cases h_em : evaluate em req es with
          | error err =>
            simp
            cases h_m : m.evaluate req es with
            | error _ => simp
            | ok m_v =>
              have := (hm_iff m_v).mpr h_m
              rw [this] at h_em; cases h_em
          | ok em_v =>
            simp
            have hm_v := (hm_iff em_v).mp h_em
            rw [hm_v]
    | aMinus =>
      simp [Cst.AddExpr.foldExtended, hop] at hfold
      cases hm : m.toAExpr? with
      | none => rw [hm] at hfold; simp at hfold
      | some em =>
        rw [hm] at hfold
        simp at hfold
        have ih' := ih hfold
        rw [ih']
        simp [Cst.MultExpr.toAExpr?, Option.bind_eq_some_iff] at hm
        obtain ⟨meos, hmeos, hmem⟩ := hm
        have hm_iff : ∀ vp, evaluate em req es = .ok vp ↔ m.evaluate req es = .ok vp :=
          Cst.MultExpr.toAExpr?_evaluate hmeos em hmem
        simp [evaluate, bind, Except.bind, Cst.AddExpr.foldOps]
        cases h_acc : evaluate acc_ast req es with
        | error err => simp
        | ok acc_v =>
          simp
          cases h_em : evaluate em req es with
          | error err =>
            simp
            cases h_m : m.evaluate req es with
            | error _ => simp
            | ok m_v =>
              have := (hm_iff m_v).mpr h_m
              rw [this] at h_em; cases h_em
          | ok em_v =>
            simp
            have hm_v := (hm_iff em_v).mp h_em
            rw [hm_v]

theorem Cst.AddExpr.toAExpr?_evaluate
  {add : Cst.AddExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  add.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  add.evaluate req es = .ok v := by
  intro hadd aexp heos v
  obtain ⟨initial, extended⟩ := add
  match hext : extended with
  | [] =>
    subst hext
    simp only [Cst.AddExpr.toExprOrSpecial?] at hadd
    have hm_iff := @Cst.MultExpr.toAExpr?_evaluate initial eos req es hadd aexp heos v
    rw [hm_iff]
    simp [Cst.AddExpr.evaluate]
    cases h_init : initial.evaluate req es with
    | error err => simp [bind, Except.bind]
    | ok iv => simp [bind, Except.bind, Cst.AddExpr.foldOps]
  | hd :: tl =>
    subst hext
    simp [Cst.AddExpr.toExprOrSpecial?, Option.bind_eq_some_iff] at hadd
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hadd
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [addExprFoldExtended_foldOps_agrees req es _ hres v]
    simp [Cst.MultExpr.toAExpr?, Option.bind_eq_some_iff] at hfirst
    obtain ⟨ueos, hueos, hfeu⟩ := hfirst
    have hu_iff : ∀ vp, evaluate first req es = .ok vp ↔ initial.evaluate req es = .ok vp :=
      Cst.MultExpr.toAExpr?_evaluate hueos first hfeu
    simp [Cst.AddExpr.evaluate]
    cases h_init : initial.evaluate req es with
    | error err =>
      simp [bind, Except.bind]
      cases h_first : evaluate first req es with
      | ok vp =>
        have := (hu_iff vp).mp h_first
        rw [this] at h_init; cases h_init
      | error _ => simp
    | ok iv =>
      simp [bind, Except.bind]
      have h_first : evaluate first req es = .ok iv := (hu_iff iv).mpr h_init
      rw [h_first]




theorem Cst.Expr.toAExpr?_evaluate
  {e : Cst.Expr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  e.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  e.evaluate req es = .ok v := by sorry

theorem Cst.Expr.toAExpr?_sound
  {e : Cst.Expr} {aexp : Expr} {req : Request} {es : Entities} :
  e.toAExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔ e.evaluate req es = .ok v := by
  intro h v
  simp [Cst.Expr.toAExpr?] at h
  cases heos : e.toExprOrSpecial? with
  | none => simp [heos] at h
  | some eos =>
    apply Cst.Expr.toAExpr?_evaluate heos aexp
    simp [heos] at h; exact h

-- theorem expr_translation_sound (cexp : Cst.Expr) (aexp : Expr) (req : Request) (es : Entities) :
--   cexp.toAExpr? = some aexp →
--   cexp.evaluate req es = evaluate aexp req es := by sorry


end
