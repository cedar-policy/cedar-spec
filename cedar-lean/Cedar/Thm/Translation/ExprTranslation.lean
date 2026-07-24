import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.AuxSound
import Cedar.Thm.Data.List.Lemmas

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

set_option maxHeartbeats 1000000

theorem Cst.ExprOrSpecial.toExpr?_sound {eos : ExprOrSpecial} {aexp : Expr} req es :
    eos.toExpr? = some aexp →
    evaluate aexp req es =
      (match eos with
        | .expr e    => evaluate e req es
        | .var var   => evaluate (Expr.var var) req es
        | .strLit s  => (CstCommon.unescape? s).elim
                          (.error (.cstError .stringError))
                          (fun s' => .ok (.prim (.string s')))
        | .boolLit b => .ok (.prim (.bool b))
        | .name _    => .error (.cstError .nameError)) := by
  cases eos <;> intro h <;> simp_all [ExprOrSpecial.toExpr?]
  · rename_i lit
    cases hsome : CstCommon.unescape? lit with
    | none => simp [hsome] at h
    | some s' => simp only [hsome] at h ⊢; simp at h; subst h; simp [evaluate]
  · rename_i b; subst h; simp [evaluate]

mutual

theorem Cst.Primary.toAExpr?_sound
  {prim : Cst.Primary} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  prim.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = prim.evaluate req es := by
  cases prim with
  | literal lit =>
    intro hprim aexp heos
    rw [Cst.ExprOrSpecial.toExpr?_sound req es heos]
    simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at hprim
    cases lit with
    | liTrue | liFalse =>
      simp at hprim; subst hprim; simp [Cst.Primary.evaluate]
    | liNum n =>
      simp at hprim
      cases hn : Int64.ofInt? ↑n.toNat with
      | none => rw [hn] at hprim; simp at hprim
      | some n' =>
        rw [hn] at hprim; simp at hprim; subst hprim
        simp [Cst.Primary.evaluate, hn, evaluate]
    | liStr s =>
      simp at hprim; subst hprim
      simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString]
      cases hs : CstCommon.unescape? s <;> simp
  | ref r =>
    intro href aexp heos
    rw [Cst.ExprOrSpecial.toExpr?_sound req es heos]
    simp [Cst.Primary.toExprOrSpecial?] at href
    cases r with
    | uid path eid =>
      let (.string s) := eid
      simp [Cst.Ref.toExprOrSpecial?] at href
      simp only [Option.bind_eq_some_iff] at href
      obtain ⟨ty, hty, su, hsu1, hsu2⟩ := href
      simp at hsu2; subst hsu2
      simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString]
      cases hs : CstCommon.unescape? s with
      | none => rw [hs] at hsu1; contradiction
      | some su' =>
        rw [hs] at hsu1; simp at hsu1
        simp [hsu1, bind, Except.bind]
        simp only [Cst.Name.toAName?] at hty
        simp [evaluate, hty]
    | ref path rinits => simp [Cst.Ref.toExprOrSpecial?] at href
  | name n =>
    intro hname aexp heos
    rw [Cst.ExprOrSpecial.toExpr?_sound req es heos]
    simp [Cst.Primary.toExprOrSpecial?] at hname
    unfold Cst.Primary.evaluate
    cases hvar : n.toVar? with
    | none =>
      simp [hvar] at hname
      simp only [Option.bind_eq_some_iff] at hname
      obtain ⟨name, hname1, hname2⟩ := hname
      simp at hname2; subst hname2
      simp [ExprOrSpecial.toExpr?] at heos
    | some var =>
      simp [hvar] at hname; subst hname
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
  | expr e =>
    intro hprim aexp heos
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at hprim
    obtain ⟨ae, hae, heq⟩ := hprim
    rw [← heq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    simp [Cst.Primary.evaluate]
    simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hae
    obtain ⟨eEos, heEos, heExpr⟩ := hae
    exact Cst.Expr.toAExpr?_sound heEos ae heExpr
  | eList xs =>
    intro hprim aexp heos
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at hprim
    obtain ⟨aes, haes, heq⟩ := hprim
    rw [← heq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    have hperElt : ∀ x ∈ xs, ∀ ax, x.toAExpr? = some ax →
        evaluate ax req es = x.evaluate req es := by
      intro x hx ax hax
      have hsz : sizeOf x < sizeOf (Cst.Primary.eList xs) := by
        have := List.sizeOf_lt_of_mem hx
        simp only [Cst.Primary.eList.sizeOf_spec]; omega
      simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hax
      obtain ⟨xEos, hxEos, hxExpr⟩ := hax
      exact Cst.Expr.toAExpr?_sound hxEos ax hxExpr
    have hbridge := mapM_eval_eq req es xs aes haes hperElt
    simp [evaluate, Cst.Primary.evaluate, bind, Except.bind,
          List.mapM₁_eq_mapM (evaluate · req es)]
    rw [hbridge]
  | rInits r =>
    intro hprim aexp heos
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at hprim
    obtain ⟨map, hmap, heq⟩ := hprim
    rw [← heq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    have hperElt : ∀ ri ∈ r, ∀ ax, ri.value.toAExpr? = some ax →
        evaluate ax req es = ri.value.evaluate req es := by
      intro ri hmem ax hax
      have hsz : sizeOf ri.value < sizeOf (Cst.Primary.rInits r) := by
        have h1 := List.sizeOf_lt_of_mem hmem
        have hval : sizeOf ri.value < sizeOf ri := by
          cases ri; simp only [Cst.RecInit.mk.sizeOf_spec]; omega
        simp only [Cst.Primary.rInits.sizeOf_spec]; omega
      simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hax
      obtain ⟨vEos, hvEos, hvExpr⟩ := hax
      exact Cst.Expr.toAExpr?_sound hvEos ax hvExpr
    exact rInits_record_eval_eq req es r map hmap hperElt

termination_by (sizeOf prim, 0)
decreasing_by all_goals (apply Prod.Lex.left; first | (subst_vars; assumption) | simp_wf)

theorem Cst.Member.toAExpr?_sound
  {mem : Cst.Member} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mem.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = mem.evaluate req es := by
  intro hmem aexp heos
  simp only [Cst.Member.toExprOrSpecial?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hmem
  obtain ⟨peos, hitem, accs, haccs, hmem⟩ := hmem
  have hacc : sizeOf mem.access < sizeOf mem := by
    cases mem; simp only [Cst.Member.mk.sizeOf_spec]; omega
  have hitm : sizeOf mem.item < sizeOf mem := by
    cases mem; simp only [Cst.Member.mk.sizeOf_spec]; omega
  have harg : ∀ ce : Cst.Expr, sizeOf ce < sizeOf mem.access → ∀ ax, ce.toAExpr? = some ax →
      evaluate ax req es = ce.evaluate req es := by
    intro ce hsz ax hax
    simp only [Cst.Expr.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hax
    obtain ⟨ceos, hceos, hax2⟩ := hax
    exact Cst.Expr.toAExpr?_sound hceos ax hax2
  unfold Cst.Member.evaluate
  split
  case h_1 _ s args rest =>
    simp only [Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?, Cst.Name.toAName?,
      CstCommon.Name.toAName?,
      CstCommon.Ident.toUnrestrictedString?, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true,
      reduceIte, Option.pure_def, List.mapM_nil, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq] at hitem
    subst hitem
    rw [List.mapM_cons] at haccs
    simp only [Cst.MemAccess.toAstAccessor?, Option.pure_def, Option.bind_eq_bind,
      Option.bind_eq_some_iff, Option.some.injEq] at haccs
    obtain ⟨a_ast, ha_ast, rest_ast, hrest_ast, rfl⟩ := haccs
    obtain ⟨xs, hxs, rfl⟩ := ha_ast
    have hargm : ∀ ce ∈ args, ∀ ax, ce.toAExpr? = some ax →
        evaluate ax req es = ce.evaluate req es := by
      intro ce hce ax hax
      exact harg ce (by
        have := List.sizeOf_lt_of_mem hce
        simp only [Cst.MemAccess.call.sizeOf_spec,
          List.cons.sizeOf_spec]; omega) ax hax
    cases hfn : CstCommon.String.toExtFun? s with
    | none =>
      have htf : Name.toFunc? { id := s, path := [] } xs = none := by
        simp [Name.toFunc?, hfn]
      rw [memberAux, memberAuxA, htf] at hmem
      simp at hmem
    | some xfn =>
      have htf : Name.toFunc? { id := s, path := [] } xs = some (.call xfn xs) := by
        simp [Name.toFunc?, hfn, toExtFun?_some_isFunctionName hfn]
      have hb : memberAuxB (.call xfn xs) rest_ast = some aexp := by
        have hmeq : memberAux (.name { id := s, path := [] }) (.call xs :: rest_ast)
                  = (memberAuxB (.call xfn xs) rest_ast).bind (fun r => some (.expr r)) := by
          simp [memberAux, memberAuxA, htf]
        rw [hmeq] at hmem
        simp only [Option.bind_eq_some_iff] at hmem
        obtain ⟨ret, hret, heq2⟩ := hmem
        rw [← Option.some.inj heq2] at heos
        simp only [ExprOrSpecial.toExpr?, Option.some.injEq] at heos
        rw [heos] at hret; exact hret
      have hstep : evaluate (Expr.call xfn xs) req es =
          (do let argVals ← args.mapM (fun a : Cst.Expr => a.evaluate req es); call xfn argVals) := by
        simp only [evaluate, List.mapM₁_eq_mapM (fun a => evaluate a req es)]
        rw [toAExprs?_eval_eq args xs hxs hargm]
      rw [evalAccessors_step_eq hstep hb
        (fun hv' hge => evalAccessors_eq rest rest_ast (.call xfn xs) aexp hv'
          hrest_ast hb hge (fun ce hsz => harg ce (Nat.lt_trans hsz (by
            simp only [Cst.MemAccess.call.sizeOf_spec, List.cons.sizeOf_spec]; omega))))]
      simp [bind_assoc]
  case h_2 item access hnfc =>
    simp only [] at hitem haccs harg
    match hpe : peos.toExpr? with
    | some headExpr =>
      have hb : memberAuxB headExpr accs = some aexp := by
        have he := memberAux_toExpr_eq accs hpe
        rw [hmem, Option.bind_some, heos] at he; exact he.symm
      have hheadEq := @Cst.Primary.toAExpr?_sound item peos req es hitem headExpr hpe
      cases hh : evaluate headExpr req es with
      | error e =>
        rw [memberAuxB_eval_error_eq accs headExpr aexp e hb hh]
        rw [← hheadEq, hh]; simp [bind, Except.bind]
      | ok hv =>
        rw [evalAccessors_eq access accs headExpr aexp hv haccs hb hh harg]
        rw [← hheadEq, hh]; simp [bind, Except.bind]
    | none =>
      exfalso
      cases memberAux_some_cases hmem with
      | inl hl => obtain ⟨_, heq⟩ := hl; subst heq; rw [hpe] at heos; simp at heos
      | inr hr =>
        obtain ⟨e, heq⟩ := hr
        subst heq
        cases peos with
        | expr _ => simp [ExprOrSpecial.toExpr?] at hpe
        | var _ => simp [ExprOrSpecial.toExpr?] at hpe
        | boolLit _ => simp [ExprOrSpecial.toExpr?] at hpe
        | strLit ss =>
          cases accs with
          | nil => rw [memberAux_nil] at hmem; simp at hmem
          | cons a r => simp [memberAux, memberAuxA, hpe] at hmem
        | name an =>
          cases accs with
          | nil => rw [memberAux_nil] at hmem; simp at hmem
          | cons a rest_ast =>
            cases a with
            | field id =>
              cases rest_ast with
              | nil => simp [memberAux, memberAuxA] at hmem
              | cons a2 r2 => cases a2 <;> simp [memberAux, memberAuxA] at hmem
            | index id => simp [memberAux, memberAuxA] at hmem
            | call xs =>
              cases hfunc : Name.toFunc? an xs with
              | none => simp [memberAux, memberAuxA, hfunc] at hmem
              | some e'' =>
                simp only [Name.toFunc?] at hfunc
                split at hfunc
                · rename_i hcond
                  simp only [Bool.and_eq_true] at hcond
                  obtain ⟨hpath, hfn⟩ := hcond
                  obtain ⟨ss, hs⟩ := toExprOrSpecial_name_func hitem (by simpa using hpath) hfn
                  cases haccess : access with
                  | nil => rw [haccess] at haccs; simp at haccs
                  | cons aa rr =>
                    cases aa with
                    | call cargs => exact hnfc ss cargs rr hs haccess
                    | field f =>
                      rw [haccess] at haccs
                      cases f <;>
                        simp [List.mapM_cons, Cst.MemAccess.toAstAccessor?,
                          Option.bind_eq_bind, Option.bind_eq_some_iff] at haccs
                    | index _ =>
                      rw [haccess] at haccs
                      simp [List.mapM_cons, Cst.MemAccess.toAstAccessor?,
                        Option.bind_eq_bind, Option.bind_eq_some_iff] at haccs
                · simp at hfunc

termination_by (sizeOf mem, 0)
decreasing_by
  all_goals (apply Prod.Lex.left; first
    | omega
    | (subst_vars; simp only [Cst.Member.mk.sizeOf_spec] at *; omega))

theorem Cst.Unary.toAExpr?_sound
  {u : Cst.Unary} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  u.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = u.evaluate req es := by
  intro hu aexp heos
  have hmk : sizeOf u.item < sizeOf u := by cases u; simp only [Cst.Unary.mk.sizeOf_spec]; omega
  match hop : u.op with
  | none =>
    simp [Cst.Unary.toExprOrSpecial?, hop] at hu
    simp [Cst.Unary.evaluate, hop]
    exact Cst.Member.toAExpr?_sound hu aexp heos
  | some (.nDash 0) =>
    simp [Cst.Unary.toExprOrSpecial?, hop] at hu
    simp [Cst.Unary.evaluate, hop]
    exact Cst.Member.toAExpr?_sound hu aexp heos
  | some .nOverBang =>
    simp [Cst.Unary.toExprOrSpecial?, hop] at hu
  | some .nOverDash =>
    simp [Cst.Unary.toExprOrSpecial?, hop] at hu
  | some (.nBang n) =>
    simp [Cst.Unary.toExprOrSpecial?, hop] at hu
    simp [Cst.Unary.evaluate, hop]
    cases hitem_trans : u.item.toExprOrSpecial? with
    | none => simp [hitem_trans] at hu
    | some ieos =>
      simp [hitem_trans] at hu
      cases hioes_trans : ieos.toExpr? with
      | none => simp [hioes_trans] at hu
      | some iexp =>
        simp [hioes_trans] at hu
        simp [← hu, ExprOrSpecial.toExpr?] at heos
        rw [← heos]
        have hitem_eq : evaluate iexp req es = u.item.evaluate req es :=
          Cst.Member.toAExpr?_sound hitem_trans iexp hioes_trans
        have h_zero : (n.toNat = 0) ↔ (n = 0) := by
          constructor
          · intro h; exact UInt8.toNat_inj.mp (by simp [h])
          · intro h; rw [h]; rfl
        have h_par : (n.toNat % 2 = 0) ↔ (n % 2 = 0) := by
          rw [show n.toNat % 2 = (n % 2).toNat from by rw [UInt8.toNat_mod]; rfl]
          constructor
          · intro h; exact UInt8.toNat_inj.mp (by simp [h])
          · intro h; rw [h]; rfl
        rw [bangN_evaluate_general iexp n.toNat req es, hitem_eq]
        by_cases hn : n = 0
        · subst hn; cases hie : u.item.evaluate req es <;> simp
        · have h0 : ¬ (n.toNat = 0) := fun h => hn (h_zero.mp h)
          cases hie : u.item.evaluate req es with
          | error e => simp [bind, Except.bind]
          | ok vp =>
            cases vp with
            | prim p =>
              cases p with
              | bool b =>
                by_cases hpar : n % 2 = 0
                · simp [hn, h0, hpar, h_par.mpr hpar, bind, Except.bind]
                · have hp2 : ¬ (n.toNat % 2 = 0) := fun h => hpar (h_par.mp h)
                  simp [hn, h0, hpar, hp2, bind, Except.bind]
              | _ => simp [hn, h0, bind, Except.bind]
            | _ => simp [hn, h0, bind, Except.bind]
  | some (.nDash n) =>
    by_cases hn0 : n = 0
    · simp [hn0, Cst.Unary.toExprOrSpecial?, hop] at hu
      simp [Cst.Unary.evaluate, hop, hn0]
      exact Cst.Member.toAExpr?_sound hu aexp heos
    · simp [Cst.Unary.toExprOrSpecial?, hop] at hu
      simp [Cst.Unary.evaluate, hop, hn0]
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
      match hlit : CstCommon.Member.toLit? u.item with
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
          by_cases h1 : n = 1
          · simp [h1, hcmp]
          · have h0 : ¬ ((n - 1).toNat = 0) := fun h => h1 (h_eq1.mp h)
            simp [h0, h1, hcmp]
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
          cases hitem_trans : u.item.toExprOrSpecial? with
          | none => simp [hitem_trans] at hu
          | some ieos =>
            simp [hitem_trans] at hu
            cases hioes_trans : ieos.toExpr? with
            | none => simp [hioes_trans] at hu
            | some iexp =>
              simp [hioes_trans] at hu
              simp [← hu, ExprOrSpecial.toExpr?] at heos
              rw [← heos]
              have hitem_eq : evaluate iexp req es = u.item.evaluate req es :=
                Cst.Member.toAExpr?_sound hitem_trans iexp hioes_trans
              rw [dashN_evaluate_general iexp n.toNat req es, hitem_eq]
              have h0 : ¬ (n.toNat = 0) := by omega
              cases hie : u.item.evaluate req es with
              | error e => simp [bind, Except.bind]
              | ok vp =>
                cases vp with
                | prim p =>
                  cases p with
                  | int i =>
                    cases hneg : i.neg? with
                    | none => simp [h0, hneg, bind, Except.bind]
                    | some j =>
                      by_cases hpar : n % 2 = 0
                      · simp [h0, hpar, h_par.mpr hpar, hneg, bind, Except.bind]
                      · have hp2 : ¬ (n.toNat % 2 = 0) := fun h => hpar (h_par.mp h)
                        simp [h0, hpar, hp2, hneg, bind, Except.bind]
                  | _ => simp [h0, bind, Except.bind]
                | _ => simp [h0, bind, Except.bind]

termination_by (sizeOf u, 0)
decreasing_by all_goals (apply Prod.Lex.left; (subst_vars; assumption))

theorem Cst.MultExpr.toAExpr?_sound
  {mult : Cst.MultExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mult.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = mult.evaluate req es := by
  intro hmult aexp heos
  have hmk : sizeOf mult.initial < sizeOf mult := by cases mult; simp only [Cst.MultExpr.mk.sizeOf_spec]; omega
  have hueq : ∀ p ∈ mult.extended, ∀ (eu : Expr), p.2.toAExpr? = some eu →
      evaluate eu req es = p.2.evaluate req es := by
    intro p hp eu heu
    have hsz : sizeOf p.2 < sizeOf mult := by
      obtain ⟨mi, me⟩ := mult
      have h1 := List.sizeOf_lt_of_mem hp
      obtain ⟨pop, pu⟩ := p
      simp only [Cst.MultExpr.mk.sizeOf_spec, Prod.mk.sizeOf_spec] at h1 ⊢
      omega
    simp only [Cst.Unary.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at heu
    obtain ⟨ueos, hueos, heu'⟩ := heu
    exact Cst.Unary.toAExpr?_sound hueos eu heu'
  match hext : mult.extended with
  | [] =>
    simp only [Cst.MultExpr.toExprOrSpecial?, hext] at hmult
    rw [@Cst.Unary.toAExpr?_sound mult.initial eos req es hmult aexp heos]
    simp [Cst.MultExpr.evaluate, hext]
    cases h_init : mult.initial.evaluate req es <;>
      simp [bind, Except.bind, Cst.MultExpr.foldOps]
  | hd :: tl =>
    simp [Cst.MultExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hmult
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hmult
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [hext] at hueq
    rw [multExprFoldExtended_foldOps_eq req es _ hueq _ _ hres]
    have hfirst_eq : evaluate first req es = mult.initial.evaluate req es := by
      simp only [Cst.Unary.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfirst
      obtain ⟨ueos, hueos, hfeu⟩ := hfirst
      exact Cst.Unary.toAExpr?_sound hueos first hfeu
    rw [hfirst_eq]
    simp [Cst.MultExpr.evaluate, hext]

termination_by (sizeOf mult, 0)
decreasing_by all_goals (apply Prod.Lex.left; (subst_vars; assumption))

theorem Cst.AddExpr.toAExpr?_sound
  {add : Cst.AddExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  add.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = add.evaluate req es := by
  intro hadd aexp heos
  have hmk : sizeOf add.initial < sizeOf add := by cases add; simp only [Cst.AddExpr.mk.sizeOf_spec]; omega
  have hmeq : ∀ p ∈ add.extended, ∀ (em : Expr), p.2.toAExpr? = some em →
      evaluate em req es = p.2.evaluate req es := by
    intro p hp em hem
    have hsz : sizeOf p.2 < sizeOf add := by
      obtain ⟨ai, aext⟩ := add
      have h1 := List.sizeOf_lt_of_mem hp
      obtain ⟨pop, pm⟩ := p
      simp only [Cst.AddExpr.mk.sizeOf_spec, Prod.mk.sizeOf_spec] at h1 ⊢
      omega
    simp only [Cst.MultExpr.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hem
    obtain ⟨meos, hmeos, hem'⟩ := hem
    exact Cst.MultExpr.toAExpr?_sound hmeos em hem'
  match hext : add.extended with
  | [] =>
    simp only [Cst.AddExpr.toExprOrSpecial?, hext] at hadd
    rw [@Cst.MultExpr.toAExpr?_sound add.initial eos req es hadd aexp heos]
    simp [Cst.AddExpr.evaluate, hext]
    cases h_init : add.initial.evaluate req es <;>
      simp [bind, Except.bind, Cst.AddExpr.foldOps]
  | hd :: tl =>
    simp [Cst.AddExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hadd
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hadd
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [hext] at hmeq
    rw [addExprFoldExtended_foldOps_eq req es _ hmeq _ _ hres]
    have hfirst_eq : evaluate first req es = add.initial.evaluate req es := by
      simp only [Cst.MultExpr.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfirst
      obtain ⟨meos, hmeos, hfem⟩ := hfirst
      exact Cst.MultExpr.toAExpr?_sound hmeos first hfem
    rw [hfirst_eq]
    simp [Cst.AddExpr.evaluate, hext]

termination_by (sizeOf add, 0)
decreasing_by all_goals (apply Prod.Lex.left; (subst_vars; assumption))

theorem Cst.Relation.toAExpr?_sound
  {rel : Cst.Relation} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  rel.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = rel.evaluate req es := by
  intro hrel aexp heos
  cases rel with
  | rCommon initial extended =>
    match hext : extended with
    | [] =>
      simp [Cst.Relation.toExprOrSpecial?] at hrel
      rw [@Cst.AddExpr.toAExpr?_sound initial eos req es hrel aexp heos]
      simp [Cst.Relation.evaluate]
    | [(op, x)] =>
      simp [Cst.Relation.toExprOrSpecial?] at hrel
      simp only [Option.bind_eq_some_iff] at hrel
      obtain ⟨ieos, hieos, eFirst, hFirst, eSecond, hSecond, hres⟩ := hrel
      injection hres with hres
      rw [← hres] at heos
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      have hinit_eq : evaluate eFirst req es = initial.evaluate req es :=
        @Cst.AddExpr.toAExpr?_sound initial ieos req es hieos eFirst hFirst
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hSecond
      obtain ⟨xeos, hxeos, hxsecond⟩ := hSecond
      have hx_eq : evaluate eSecond req es = x.evaluate req es :=
        Cst.AddExpr.toAExpr?_sound hxeos eSecond hxsecond
      cases h_init : initial.evaluate req es with
      | error err =>
        have h_first : evaluate eFirst req es = .error err := hinit_eq.trans h_init
        cases op <;>
          simp [constructExprRel, evaluate, Cst.Relation.evaluate, h_first, h_init, bind, Except.bind]
      | ok iv =>
        have h_first : evaluate eFirst req es = .ok iv := hinit_eq.trans h_init
        cases h_x : x.evaluate req es with
        | error err =>
          have h_second : evaluate eSecond req es = .error err := hx_eq.trans h_x
          cases op <;>
            simp [constructExprRel, evaluate, Cst.Relation.evaluate, h_first, h_second, h_init, h_x, bind, Except.bind]
        | ok xv =>
          have h_second : evaluate eSecond req es = .ok xv := hx_eq.trans h_x
          rw [constructExprRel_applyRelOp_eq op eFirst eSecond req es iv xv h_first h_second]
          simp [Cst.Relation.evaluate, h_init, h_x, bind, Except.bind]
    | _ :: _ :: _ =>
      simp [Cst.Relation.toExprOrSpecial?] at hrel
  | rHas target field =>
    simp [Cst.Relation.toExprOrSpecial?, Option.bind_eq_some_iff] at hrel
    obtain ⟨mt, hmt, mf, hmf, hres⟩ := hrel
    simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
    obtain ⟨tEos, htEos, htExpr⟩ := hmt
    have htarget_eq : evaluate mt req es = target.evaluate req es :=
      @Cst.AddExpr.toAExpr?_sound target tEos req es htEos mt htExpr
    have hfield_attrs := addExpr_toHasRhs_toAttrs_agrees hmf
    have hfield_nonempty := hasRhsToList_nonempty hmf
    simp [Cst.Relation.evaluate, hfield_attrs]
    cases mf with
    | inl f =>
      simp at hres
      rw [← hres] at heos
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      simp [hasRhsToList]
      cases htgt : target.evaluate req es with
      | error err =>
        have hmtE : evaluate mt req es = .error err := htarget_eq.trans htgt
        simp [evaluate, hmtE, bind, Except.bind]
      | ok vt =>
        have hmtO : evaluate mt req es = .ok vt := htarget_eq.trans htgt
        simp [evaluate, hmtO, bind, Except.bind, Cst.rHasChain]
    | inr fs =>
      simp at hres
      rw [← hres] at heos
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      simp [hasRhsToList] at hfield_attrs hfield_nonempty
      cases hfs : fs with
      | nil => rw [hfs] at hfield_nonempty; simp at hfield_nonempty
      | cons a as =>
        rw [hfs] at hfield_attrs
        cases htgt : target.evaluate req es with
        | error err =>
          have htgtMt : evaluate mt req es = .error err := htarget_eq.trans htgt
          cases as with
          | nil => simp [extendedHasAttr, evaluate, htgtMt, bind, Except.bind]
          | cons b bs => simp [extendedHasAttr, evaluate, htgtMt, bind, Except.bind, Result.as]
        | ok vt =>
          have htgtMt : evaluate mt req es = .ok vt := htarget_eq.trans htgt
          rw [extendedHasAttr_evaluate_agrees mt a as req es vt htgtMt]
          simp [hasRhsToList, bind, Except.bind]
  | rLike target pattern =>
    simp [Cst.Relation.toExprOrSpecial?, Option.bind_eq_some_iff] at hrel
    obtain ⟨mt, hmt, mp, hmp, hres⟩ := hrel
    rw [← hres] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
    obtain ⟨tEos, htEos, htExpr⟩ := hmt
    have htarget_eq : evaluate mt req es = target.evaluate req es :=
      @Cst.AddExpr.toAExpr?_sound target tEos req es htEos mt htExpr
    obtain ⟨s, hpStr, hpToPattern⟩ := addExpr_toPattern_toPatternString_agrees hmp
    simp [Cst.Relation.evaluate, hpStr]
    cases htgt : target.evaluate req es with
    | error err =>
      have hmtE : evaluate mt req es = .error err := htarget_eq.trans htgt
      simp [evaluate, hmtE, bind, Except.bind]
    | ok vt =>
      have hmtO : evaluate mt req es = .ok vt := htarget_eq.trans htgt
      simp [evaluate, hmtO, bind, Except.bind, hpToPattern]
  | rIsIn target ety inEntity =>
    simp [Cst.Relation.toExprOrSpecial?, Option.bind_eq_some_iff] at hrel
    have ⟨mt, hmt, et, hEt, hMatch⟩ := hrel
    match hinE : inEntity, hMatch with
    | none, hMatch =>
      simp at hMatch
      subst hMatch
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
      have ⟨tEos, htEos, htExpr⟩ := hmt
      have htarget_eq : evaluate mt req es = target.evaluate req es :=
        @Cst.AddExpr.toAExpr?_sound target tEos req es htEos mt htExpr
      simp [Cst.Relation.evaluate, hEt]
      cases htgt : target.evaluate req es with
      | error err =>
        have hmtE : evaluate mt req es = .error err := htarget_eq.trans htgt
        simp [evaluate, hmtE, bind, Except.bind]
      | ok vt =>
        have hmtO : evaluate mt req es = .ok vt := htarget_eq.trans htgt
        simp [evaluate, hmtO, bind, Except.bind]
        cases apply₁ (UnaryOp.is et) vt <;> simp
    | some ie, hMatch =>
      simp [Option.bind_eq_some_iff] at hMatch
      have ⟨mi, hmi, hres⟩ := hMatch
      subst hres
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
      have ⟨tEos, htEos, htExpr⟩ := hmt
      have htarget_eq : evaluate mt req es = target.evaluate req es :=
        @Cst.AddExpr.toAExpr?_sound target tEos req es htEos mt htExpr
      have hie_trans : ie.toAExpr? = some mi := hmi
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmi
      have ⟨iEos, hiEos, hiExpr⟩ := hmi
      have hinEntity_eq : evaluate mi req es = ie.evaluate req es :=
        @Cst.AddExpr.toAExpr?_sound ie iEos req es hiEos mi hiExpr
      exact rIsIn_some_eval_eq hEt htarget_eq hinEntity_eq hie_trans

termination_by (sizeOf rel, 0)
decreasing_by
  all_goals
    apply Prod.Lex.left
    subst_vars
    simp only [Cst.Relation.rCommon.sizeOf_spec, Cst.Relation.rHas.sizeOf_spec,
      Cst.Relation.rLike.sizeOf_spec, Cst.Relation.rIsIn.sizeOf_spec,
      List.cons.sizeOf_spec, Prod.mk.sizeOf_spec, Option.some.sizeOf_spec] at *
    omega

theorem Cst.AndExpr.toAExpr?_sound
  {ae : Cst.AndExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  ae.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = ae.evaluate req es := by
  intro hae aexp heos
  have hmk : sizeOf ae.initial < sizeOf ae := by cases ae; simp only [Cst.AndExpr.mk.sizeOf_spec]; omega
  have hreq : ∀ r ∈ ae.extended, ∀ (er : Expr), r.toAExpr? = some er →
      evaluate er req es = r.evaluate req es := by
    intro r hr er her
    have hsz : sizeOf r < sizeOf ae := by
      obtain ⟨ai, aext⟩ := ae
      have h1 := List.sizeOf_lt_of_mem hr
      simp only [Cst.AndExpr.mk.sizeOf_spec] at h1 ⊢
      omega
    simp only [Cst.Relation.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at her
    obtain ⟨reos, hreos, her'⟩ := her
    exact Cst.Relation.toAExpr?_sound hreos er her'
  match hext : ae.extended with
  | [] =>
    simp only [Cst.AndExpr.toExprOrSpecial?, hext] at hae
    rw [@Cst.Relation.toAExpr?_sound ae.initial eos req es hae aexp heos]
    simp [Cst.AndExpr.evaluate, hext]
    cases h_init : ae.initial.evaluate req es <;>
      simp [bind, Except.bind, Cst.AndExpr.foldOps]
  | hd :: tl =>
    simp [Cst.AndExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hae
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hae
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [hext] at hreq
    rw [andExprFoldExtended_foldOps_eq req es _ hreq _ _ hres]
    have hfirst_eq : evaluate first req es = ae.initial.evaluate req es := by
      simp only [Cst.Relation.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfirst
      obtain ⟨reos, hreos, hfem⟩ := hfirst
      exact Cst.Relation.toAExpr?_sound hreos first hfem
    rw [hfirst_eq]
    have hall := andExprFoldExtended_some_all_translate _ hres
    have hguard : (ae.extended.all fun r => r.toAExpr?.isSome) = true := by rw [hext]; exact hall
    rw [AndExpr.evaluate_eq hguard, hext]

termination_by (sizeOf ae, 0)
decreasing_by all_goals (apply Prod.Lex.left; (subst_vars; assumption))

theorem Cst.OrExpr.toAExpr?_sound
  {oe : Cst.OrExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  oe.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = oe.evaluate req es := by
  intro hoe aexp heos
  have hmk : sizeOf oe.initial < sizeOf oe := by cases oe; simp only [Cst.OrExpr.mk.sizeOf_spec]; omega
  have hareq : ∀ a ∈ oe.extended, ∀ (ea : Expr), a.toAExpr? = some ea →
      evaluate ea req es = a.evaluate req es := by
    intro a ha ea hea
    have hsz : sizeOf a < sizeOf oe := by
      obtain ⟨oi, oext⟩ := oe
      have h1 := List.sizeOf_lt_of_mem ha
      simp only [Cst.OrExpr.mk.sizeOf_spec] at h1 ⊢
      omega
    simp only [Cst.AndExpr.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hea
    obtain ⟨aeos, haeos, hea'⟩ := hea
    exact Cst.AndExpr.toAExpr?_sound haeos ea hea'
  match hext : oe.extended with
  | [] =>
    simp only [Cst.OrExpr.toExprOrSpecial?, hext] at hoe
    rw [@Cst.AndExpr.toAExpr?_sound oe.initial eos req es hoe aexp heos]
    simp [Cst.OrExpr.evaluate, hext]
    cases h_init : oe.initial.evaluate req es <;>
      simp [bind, Except.bind, Cst.OrExpr.foldOps]
  | hd :: tl =>
    simp [Cst.OrExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hoe
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hoe
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [hext] at hareq
    rw [orExprFoldExtended_foldOps_eq req es _ hareq _ _ hres]
    have hfirst_eq : evaluate first req es = oe.initial.evaluate req es := by
      simp only [Cst.AndExpr.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hfirst
      obtain ⟨aeos, haeos, hfea⟩ := hfirst
      exact Cst.AndExpr.toAExpr?_sound haeos first hfea
    rw [hfirst_eq]
    have hall := orExprFoldExtended_some_all_translate _ hres
    have hguard : (oe.extended.all fun r => r.toAExpr?.isSome) = true := by rw [hext]; exact hall
    rw [OrExpr.evaluate_eq hguard, hext]

termination_by (sizeOf oe, 0)
decreasing_by all_goals (apply Prod.Lex.left; (subst_vars; assumption))

theorem Cst.ExprData.toAExpr?_sound
  {ed : Cst.ExprData} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  ed.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = ed.evaluate req es := by
  intro hed aexp heos
  cases ed with
  | edOr ore =>
    simp [Cst.ExprData.toExprOrSpecial?] at hed
    simp [Cst.ExprData.evaluate]
    have hsz : sizeOf ore < sizeOf (Cst.ExprData.edOr ore) := by
      simp only [Cst.ExprData.edOr.sizeOf_spec]; omega
    exact Cst.OrExpr.toAExpr?_sound hed aexp heos
  | edIf i t f =>
    simp [Cst.ExprData.toExprOrSpecial?, Option.bind_eq_some_iff] at hed
    obtain ⟨eg, hg, et, ht, ef, hf, hres⟩ := hed
    have hguard : (t.toAExpr?.isSome && f.toAExpr?.isSome) = true := by simp [ht, hf]
    rw [← hres] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hg ht hf
    obtain ⟨gEos, hgEos, hgExpr⟩ := hg
    obtain ⟨tEos, htEos, htExpr⟩ := ht
    obtain ⟨fEos, hfEos, hfExpr⟩ := hf
    have hszi : sizeOf i < sizeOf (Cst.ExprData.edIf i t f) := by
      simp only [Cst.ExprData.edIf.sizeOf_spec]; omega
    have hszt : sizeOf t < sizeOf (Cst.ExprData.edIf i t f) := by
      simp only [Cst.ExprData.edIf.sizeOf_spec]; omega
    have hszf : sizeOf f < sizeOf (Cst.ExprData.edIf i t f) := by
      simp only [Cst.ExprData.edIf.sizeOf_spec]; omega
    have hg_eq : evaluate eg req es = i.evaluate req es := Cst.Expr.toAExpr?_sound hgEos eg hgExpr
    have ht_eq : evaluate et req es = t.evaluate req es := Cst.Expr.toAExpr?_sound htEos et htExpr
    have hf_eq : evaluate ef req es = f.evaluate req es := Cst.Expr.toAExpr?_sound hfEos ef hfExpr
    rw [ExprData.evaluate_edIf_eq hguard]
    simp [evaluate, bind, Except.bind, Result.as, Coe.coe]
    rw [hg_eq]
    cases hi : i.evaluate req es with
    | error err => simp
    | ok gv =>
      cases gv with
      | prim p =>
        cases p with
        | bool b =>
          simp [Value.asBool]
          cases b with
          | true => exact ht_eq
          | false => exact hf_eq
        | int _ | string _ | entityUID _ => simp [Value.asBool]
      | set _ | record _ | ext _ => simp [Value.asBool]
termination_by (sizeOf ed, 0)
decreasing_by all_goals (apply Prod.Lex.left; (subst_vars; assumption))

theorem Cst.ExprImpl.toAExpr?_sound
  {ei : Cst.ExprImpl} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  ei.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = ei.evaluate req es := by
  intro hei aexp heos
  simp only [Cst.ExprImpl.toExprOrSpecial?] at hei
  simp [Cst.ExprImpl.evaluate]
  exact Cst.ExprData.toAExpr?_sound hei aexp heos
termination_by (sizeOf ei, 0)
decreasing_by
  apply Prod.Lex.left
  have h : sizeOf ei = 1 + sizeOf ei.expr := by cases ei; simp [Cst.ExprImpl.mk.sizeOf_spec]
  omega

theorem Cst.Expr.toAExpr?_sound
  {e : Cst.Expr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  e.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  evaluate aexp req es = e.evaluate req es := by
  intro he aexp heos
  cases e with
  | expr ei =>
    simp only [Cst.Expr.toExprOrSpecial?] at he
    simp [Cst.Expr.evaluate]
    have hsz : sizeOf ei < sizeOf (Cst.Expr.expr ei) := by
      simp only [Cst.Expr.expr.sizeOf_spec]; omega
    exact Cst.ExprImpl.toAExpr?_sound he aexp heos
termination_by (sizeOf e, 0)
decreasing_by all_goals (apply Prod.Lex.left; (subst_vars; assumption))

theorem expr_to_expr_sound
  {e : Cst.Expr} {aexp : Expr} {req : Request} {es : Entities} :
  e.toAExpr? = some aexp →
  evaluate aexp req es = e.evaluate req es := by
  intro h
  simp [Cst.Expr.toAExpr?] at h
  cases heos : e.toExprOrSpecial? with
  | none => simp [heos] at h
  | some eos =>
    apply Cst.Expr.toAExpr?_sound heos aexp
    simp [heos] at h; exact h

end
