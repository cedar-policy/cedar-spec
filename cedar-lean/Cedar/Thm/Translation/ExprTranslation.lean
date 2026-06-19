import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.Aux
import Cedar.Thm.Data.List.Lemmas

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

set_option maxHeartbeats 1000000

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
/-- If `toExtFun?` succeeds on a string, that string is a function name. -/
theorem toExtFun?_some_isFunctionName {s : String} {xfn : ExtFun}
    (h : CstCommon.String.toExtFun? s = some xfn) :
    CstCommon.String.isFunctionName? s = true := by
  simp only [CstCommon.String.toExtFun?] at h
  split at h <;> simp_all [CstCommon.String.isFunctionName?]

mutual

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
        simp only [Cst.Name.toAName?] at hty
        simp [evaluate, hty]
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

  | expr e =>
    intro hprim aexp heos v
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at hprim
    obtain ⟨ae, hae, heq⟩ := hprim
    rw [← heq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    simp [Cst.Primary.evaluate]
    simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hae
    obtain ⟨eEos, heEos, heExpr⟩ := hae
    exact Cst.Expr.toAExpr?_evaluate heEos ae heExpr v
  | eList xs =>
    intro hprim aexp heos v
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at hprim
    obtain ⟨aes, haes, heq⟩ := hprim
    rw [← heq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    have hperElt : ∀ x ∈ xs, ∀ ax,
        x.toAExpr? = some ax →
        ∀ v, evaluate ax req es = .ok v ↔ x.evaluate req es = .ok v := by
      intro x hx ax hax v
      simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hax
      obtain ⟨xEos, hxEos, hxExpr⟩ := hax
      exact Cst.Expr.toAExpr?_evaluate hxEos ax hxExpr v
    have hbridge := mapM_eval_agrees req es xs aes haes hperElt
    simp [evaluate, Cst.Primary.evaluate, bind, Except.bind,
          List.mapM₁_eq_mapM (evaluate · req es)]
    cases hmes : aes.mapM (fun a => evaluate a req es) with
    | error err =>
      cases hxes : xs.mapM (fun x => x.evaluate req es) with
      | ok vs =>
        have := (hbridge vs).mpr hxes
        rw [this] at hmes; cases hmes
      | error _ => simp
    | ok vs =>
      have := (hbridge vs).mp hmes
      rw [this]
  | rInits r =>
    intro hprim aexp heos v
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at hprim
    obtain ⟨map, hmap, heq⟩ := hprim
    rw [← heq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    -- per-value evaluation agreement (mutual IH on each record value)
    have hperElt : ∀ ri ∈ r, ∀ ax, ri.value.toAExpr? = some ax →
        ∀ v, evaluate ax req es = .ok v ↔ ri.value.evaluate req es = .ok v := by
      intro ri hmem ax hax v
      have hsz : sizeOf ri.value < 1 + sizeOf r := by
        have h1 := List.sizeOf_lt_of_mem hmem
        have hval : sizeOf ri.value < sizeOf ri := by
          cases ri; simp only [Cst.RecInit.mk.sizeOf_spec]; omega
        omega
      simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hax
      obtain ⟨vEos, hvEos, hvExpr⟩ := hax
      exact Cst.Expr.toAExpr?_evaluate hvEos ax hvExpr v
    exact rInits_record_eval_agrees req es r map hmap hperElt v
termination_by (sizeOf prim, 0)
decreasing_by
  all_goals simp_wf
  all_goals first
    | (apply Prod.Lex.left; omega)
    | (apply Prod.Lex.left
       rename_i _ _
       have := List.sizeOf_lt_of_mem hx
       omega)

theorem Cst.Member.toAExpr?_evaluate
  {mem : Cst.Member} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mem.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  mem.evaluate req es = .ok v := by

  intro hmem aexp heos v
  simp only [Cst.Member.toExprOrSpecial?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hmem
  obtain ⟨peos, hitem, accs, haccs, hmem⟩ := hmem
  have harg : ∀ ce : Cst.Expr, sizeOf ce < sizeOf mem.access → ∀ ax, ce.toAExpr? = some ax →
      ∀ w, evaluate ax req es = .ok w ↔ ce.evaluate req es = .ok w := by
    intro ce hsz ax hax w
    simp only [Cst.Expr.toAExpr?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hax
    obtain ⟨ceos, hceos, hax2⟩ := hax
    exact Cst.Expr.toAExpr?_evaluate hceos ax hax2 w
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
        ∀ w, evaluate ax req es = .ok w ↔ ce.evaluate req es = .ok w := by
      intro ce hce ax hax w
      exact harg ce (by
        have := List.sizeOf_lt_of_mem hce
        simp only [Cst.MemAccess.call.sizeOf_spec,
          List.cons.sizeOf_spec]; omega) ax hax w
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
      have hstep : ∀ w, evaluate (Expr.call xfn xs) req es = .ok w ↔
          (do let argVals ← args.mapM (fun a : Cst.Expr => a.evaluate req es); call xfn argVals) = .ok w := by
        intro w
        simp only [evaluate, List.mapM₁_eq_mapM (fun a => evaluate a req es)]
        cases hxe : xs.mapM (fun a => evaluate a req es) with
        | ok vs =>
          rw [(toAExprs?_eval_agrees args xs hxs hargm vs).mp hxe]
        | error e =>
          have hne : ∀ vs, args.mapM (fun ce => ce.evaluate req es) ≠ .ok vs := by
            intro vs hvs
            rw [(toAExprs?_eval_agrees args xs hxs hargm vs).mpr hvs] at hxe; simp at hxe
          cases hae : args.mapM (fun ce => ce.evaluate req es) with
          | ok vs => exact absurd hae (hne vs)
          | error e' => simp [bind, Except.bind]
      rw [evalAccessors_step hstep hb
        (fun hv' hge => evalAccessors_agrees rest rest_ast (.call xfn xs) aexp hv'
          hrest_ast hb hge (fun ce hsz => harg ce (Nat.lt_trans hsz (by
            simp only [Cst.MemAccess.call.sizeOf_spec, List.cons.sizeOf_spec]; omega)))) v]
      simp [bind_assoc]
  case h_2 item access hnfc =>
    simp only [] at hitem haccs harg
    match hpe : peos.toExpr? with
    | some headExpr =>
      have hb : memberAuxB headExpr accs = some aexp := by
        have he := memberAux_toExpr_eq accs hpe
        rw [hmem, Option.bind_some, heos] at he; exact he.symm
      have hheadIff := @Cst.Primary.toAExpr?_evaluate item peos req es hitem headExpr hpe
      cases h_item : item.evaluate req es with
      | error e =>
        have hge : ∃ e', evaluate headExpr req es = .error e' := by
          cases hh : evaluate headExpr req es with
          | error e' => exact ⟨e', rfl⟩
          | ok hv => exact absurd ((hheadIff hv).mp hh) (by rw [h_item]; simp)
        obtain ⟨e', hge⟩ := hge
        obtain ⟨e'', he''⟩ := memberAuxB_eval_error accs headExpr aexp e' hb hge
        simp [he'', bind, Except.bind]
      | ok hv =>
        have hge : evaluate headExpr req es = .ok hv := (hheadIff hv).mpr h_item
        rw [evalAccessors_agrees access accs headExpr aexp hv haccs hb hge harg v]
        simp [bind, Except.bind]
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
  all_goals
    (apply Prod.Lex.left
     first
       | (subst_vars; simp only [Cst.Member.mk.sizeOf_spec]; omega)
       | (cases mem; simp only [Cst.Member.mk.sizeOf_spec] at *; omega))

theorem Cst.Unary.toAExpr?_evaluate
  {u : Cst.Unary} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  u.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  u.evaluate req es = .ok v := by

  intro hu aexp heos v
  match hop : u.op with
  | none =>
    simp [Cst.Unary.toExprOrSpecial?, hop] at hu
    simp [Cst.Unary.evaluate, hop]
    exact Cst.Member.toAExpr?_evaluate hu aexp heos v
  | some (.nDash 0) =>
    simp [Cst.Unary.toExprOrSpecial?, hop] at hu
    simp [Cst.Unary.evaluate, hop]
    exact Cst.Member.toAExpr?_evaluate hu aexp heos v
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
        have hitem_iff : ∀ vp, evaluate iexp req es = .ok vp ↔ u.item.evaluate req es = .ok vp :=
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
          cases h_item : u.item.evaluate req es with
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
    · simp [hn0, Cst.Unary.toExprOrSpecial?, hop] at hu
      simp [Cst.Unary.evaluate, hop, hn0]
      exact Cst.Member.toAExpr?_evaluate hu aexp heos v
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
              have hitem_iff : ∀ vp, evaluate iexp req es = .ok vp ↔ u.item.evaluate req es = .ok vp :=
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
                cases h_item : u.item.evaluate req es with
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
  | some .nOverBang => simp [Cst.Unary.toExprOrSpecial?, hop] at hu
  | some .nOverDash => simp [Cst.Unary.toExprOrSpecial?, hop] at hu
termination_by (sizeOf u, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     cases u; simp only [Cst.Unary.mk.sizeOf_spec]; omega)

theorem multExprFoldExtended_foldOps_agrees
  (req : Request) (es : Entities)
  (xs : List (Cst.MultOp × Cst.Unary))
  {acc_ast : Expr} {result : Expr} :
  Cst.MultExpr.foldExtended acc_ast xs = some result →
  ∀ v, evaluate result req es = .ok v ↔
       (do let acc_v ← evaluate acc_ast req es
           Cst.MultExpr.foldOps acc_v xs req es) = .ok v := by

  intro hfold v
  match xs with
  | [] =>
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

  | (op, u) :: rest =>
    -- Translator only succeeds on .mTimes; other ops fail and contradict hfold.
    cases hop : op with
    | mTimes =>
      simp [Cst.MultExpr.foldExtended, hop] at hfold
      cases hu : u.toAExpr? with
      | none => rw [hu] at hfold; simp at hfold
      | some eu =>
        rw [hu] at hfold
        simp at hfold
        have ih' := multExprFoldExtended_foldOps_agrees req es rest hfold v
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
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at *
     omega)

theorem Cst.MultExpr.toAExpr?_evaluate
  {mult : Cst.MultExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  mult.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  mult.evaluate req es = .ok v := by

  intro hmult aexp heos v
  match hext : mult.extended with
  | [] =>
    simp only [Cst.MultExpr.toExprOrSpecial?, hext] at hmult
    have hu_iff := @Cst.Unary.toAExpr?_evaluate mult.initial eos req es hmult aexp heos v
    rw [hu_iff]
    simp [Cst.MultExpr.evaluate]
    cases h_init : mult.initial.evaluate req es with
    | error err => simp [bind, Except.bind]
    | ok iv => simp [bind, Except.bind, Cst.MultExpr.foldOps, hext]
  | hd :: tl =>
    simp [Cst.MultExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hmult
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hmult
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [multExprFoldExtended_foldOps_agrees req es _ hres v]
    simp [Cst.Unary.toAExpr?, Option.bind_eq_some_iff] at hfirst
    obtain ⟨ueos, hueos, hfeu⟩ := hfirst
    have hu_iff : ∀ vp, evaluate first req es = .ok vp ↔ mult.initial.evaluate req es = .ok vp :=
      Cst.Unary.toAExpr?_evaluate hueos first hfeu
    simp [Cst.MultExpr.evaluate]
    cases h_init : mult.initial.evaluate req es with
    | error err =>
      simp [bind, Except.bind]
      cases h_first : evaluate first req es with
      | ok vp =>
        have := (hu_iff vp).mp h_first
        rw [this] at h_init; cases h_init
      | error _ => simp
    | ok iv =>
      simp [bind, Except.bind, hext]
      have h_first : evaluate first req es = .ok iv := (hu_iff iv).mpr h_init
      rw [h_first]
termination_by (sizeOf mult, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     cases mult
     simp only [Cst.MultExpr.mk.sizeOf_spec]
     try (have h := hext; subst h)
     omega)

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
  match xs with
  | [] =>
    simp [Cst.AddExpr.foldExtended] at hfold
    simp [hfold]; constructor <;> intro h
    · simp [h, bind, Except.bind, Cst.AddExpr.foldOps]
    · cases hres : evaluate result req es with
      | error err => simp [bind, Except.bind, hres] at h
      | ok v' =>
        simp [bind, Except.bind, hres] at h
        simp [Cst.AddExpr.foldOps] at h
        rw [h]
  | (op, m) :: rest =>
    cases hop : op with
    | aPlus =>
      simp [Cst.AddExpr.foldExtended, hop] at hfold
      cases hm : m.toAExpr? with
      | none => rw [hm] at hfold; simp at hfold
      | some em =>
        rw [hm] at hfold
        simp at hfold
        have ih' := addExprFoldExtended_foldOps_agrees req es rest hfold v
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
        have ih' := addExprFoldExtended_foldOps_agrees req es rest hfold v
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
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at *
     omega)

theorem Cst.AddExpr.toAExpr?_evaluate
  {add : Cst.AddExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  add.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  add.evaluate req es = .ok v := by
  intro hadd aexp heos v
  match hext : add.extended with
  | [] =>
    simp only [Cst.AddExpr.toExprOrSpecial?, hext] at hadd
    have hm_iff := @Cst.MultExpr.toAExpr?_evaluate add.initial eos req es hadd aexp heos v
    rw [hm_iff]
    simp [Cst.AddExpr.evaluate]
    cases h_init : add.initial.evaluate req es with
    | error err => simp [bind, Except.bind]
    | ok iv => simp [bind, Except.bind, Cst.AddExpr.foldOps, hext]
  | hd :: tl =>
    simp [Cst.AddExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hadd
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hadd
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [addExprFoldExtended_foldOps_agrees req es _ hres v]
    simp [Cst.MultExpr.toAExpr?, Option.bind_eq_some_iff] at hfirst
    obtain ⟨ueos, hueos, hfeu⟩ := hfirst
    have hu_iff : ∀ vp, evaluate first req es = .ok vp ↔ add.initial.evaluate req es = .ok vp :=
      Cst.MultExpr.toAExpr?_evaluate hueos first hfeu
    simp [Cst.AddExpr.evaluate]
    cases h_init : add.initial.evaluate req es with
    | error err =>
      simp [bind, Except.bind]
      cases h_first : evaluate first req es with
      | ok vp =>
        have := (hu_iff vp).mp h_first
        rw [this] at h_init; cases h_init
      | error _ => simp
    | ok iv =>
      simp [bind, Except.bind, hext]
      have h_first : evaluate first req es = .ok iv := (hu_iff iv).mpr h_init
      rw [h_first]
termination_by (sizeOf add, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     cases add
     simp only [Cst.AddExpr.mk.sizeOf_spec]
     try (have h := hext; subst h)
     omega)


theorem Cst.Relation.toAExpr?_evaluate
  {rel : Cst.Relation} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  rel.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  rel.evaluate req es = .ok v := by
  intro hrel aexp heos v
  cases rel with
  | rCommon initial extended =>
    match hext : extended with
    | [] =>
      simp [Cst.Relation.toExprOrSpecial?] at hrel
      have hadd_iff := @Cst.AddExpr.toAExpr?_evaluate initial eos req es hrel aexp heos v
      simp [Cst.Relation.evaluate]
      exact hadd_iff
    | [(op, x)] =>
      simp [Cst.Relation.toExprOrSpecial?] at hrel
      simp only [Option.bind_eq_some_iff] at hrel
      obtain ⟨ieos, hieos, eFirst, hFirst, eSecond, hSecond, hres⟩ := hrel
      injection hres with hres
      rw [← hres] at heos
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      have hinit_iff :=
        @Cst.AddExpr.toAExpr?_evaluate initial ieos req es hieos eFirst hFirst
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hSecond
      obtain ⟨xeos, hxeos, hxsecond⟩ := hSecond
      have hx_iff : ∀ vp, evaluate eSecond req es = .ok vp ↔ x.evaluate req es = .ok vp :=
        Cst.AddExpr.toAExpr?_evaluate hxeos eSecond hxsecond
      simp [Cst.Relation.evaluate]
      cases h_init : initial.evaluate req es with
      | error err =>
        simp [bind, Except.bind]
        cases h_first : evaluate eFirst req es with
        | ok vp =>
          have := (hinit_iff vp).mp h_first
          rw [this] at h_init; cases h_init
        | error _ =>
          cases op <;>
            simp [constructExprRel, evaluate, h_first, bind, Except.bind]
      | ok iv =>
        simp [bind, Except.bind]
        have h_first : evaluate eFirst req es = .ok iv := (hinit_iff iv).mpr h_init
        cases h_x : x.evaluate req es with
        | error err =>
          cases h_second : evaluate eSecond req es with
          | ok xv =>
            have := (hx_iff xv).mp h_second
            rw [this] at h_x; cases h_x
          | error err' =>
            constructor
            · intro hev
              exfalso
              cases op <;> simp [constructExprRel, evaluate, h_first, h_second,
                                  bind, Except.bind] at hev
            · intro hev
              simp_all
        | ok xv =>
          have h_second : evaluate eSecond req es = .ok xv := (hx_iff xv).mpr h_x
          rw [constructExprRel_applyRelOp_agrees op eFirst eSecond req es iv xv h_first h_second]
    | _ :: _ :: _ =>
      simp [Cst.Relation.toExprOrSpecial?] at hrel
  | rHas target field =>
    simp [Cst.Relation.toExprOrSpecial?, Option.bind_eq_some_iff] at hrel
    obtain ⟨mt, hmt, mf, hmf, hres⟩ := hrel
    simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
    obtain ⟨tEos, htEos, htExpr⟩ := hmt
    have htarget_iff :=
      @Cst.AddExpr.toAExpr?_evaluate target tEos req es htEos mt htExpr
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
        simp [bind, Except.bind]
        cases htgt' : evaluate mt req es with
        | ok vt =>
          have := (htarget_iff vt).mp htgt'
          rw [this] at htgt; cases htgt
        | error _ => simp [evaluate, htgt', bind, Except.bind]
      | ok vt =>
        have htgtMt : evaluate mt req es = .ok vt := (htarget_iff vt).mpr htgt
        simp [evaluate, htgtMt, bind, Except.bind, Cst.rHasChain]
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
          simp [bind, Except.bind]
          cases htgt' : evaluate mt req es with
          | ok vt =>
            have := (htarget_iff vt).mp htgt'
            rw [this] at htgt; cases htgt
          | error _ =>
            cases as with
            | nil => simp [extendedHasAttr, evaluate, htgt', bind, Except.bind]
            | cons b bs => simp [extendedHasAttr, evaluate, htgt', bind, Except.bind,
                                  Result.as]
        | ok vt =>
          have htgtMt : evaluate mt req es = .ok vt := (htarget_iff vt).mpr htgt
          rw [extendedHasAttr_evaluate_agrees mt a as req es vt htgtMt]
          simp [hasRhsToList, bind, Except.bind]
  | rLike target pattern =>
    simp [Cst.Relation.toExprOrSpecial?, Option.bind_eq_some_iff] at hrel
    obtain ⟨mt, hmt, mp, hmp, hres⟩ := hrel
    rw [← hres] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    -- Bridge target via Cst.AddExpr.toAExpr?_evaluate.
    simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
    obtain ⟨tEos, htEos, htExpr⟩ := hmt
    have htarget_iff :=
      @Cst.AddExpr.toAExpr?_evaluate target tEos req es htEos mt htExpr
    -- Bridge pattern via addExpr_toPattern_toPatternString_agrees.
    obtain ⟨s, hpStr, hpToPattern⟩ := addExpr_toPattern_toPatternString_agrees hmp
    simp [Cst.Relation.evaluate, hpStr]
    cases htgt : target.evaluate req es with
    | error err =>
      simp [bind, Except.bind]
      cases htgt' : evaluate mt req es with
      | ok vt =>
        have := (htarget_iff vt).mp htgt'
        rw [this] at htgt; cases htgt
      | error _ =>
        simp [evaluate, htgt', bind, Except.bind]
    | ok vt =>
      have htgtMt : evaluate mt req es = .ok vt := (htarget_iff vt).mpr htgt
      simp [evaluate, htgtMt, bind, Except.bind, hpToPattern]
  | rIsIn target ety inEntity =>
    simp [Cst.Relation.toExprOrSpecial?, Option.bind_eq_some_iff] at hrel
    have ⟨mt, hmt, et, hEt, hMatch⟩ := hrel
    match hinE : inEntity, hMatch with
    | none, hMatch =>
      simp at hMatch
      subst hMatch
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      have hEtyName := addExpr_toEntityType_agrees hEt
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
      have ⟨tEos, htEos, htExpr⟩ := hmt
      have htarget_iff :=
        @Cst.AddExpr.toAExpr?_evaluate target tEos req es htEos mt htExpr
      simp [Cst.Relation.evaluate, hEtyName]
      cases htgt : target.evaluate req es with
      | error err =>
        simp [bind, Except.bind]
        cases htgt' : evaluate mt req es with
        | ok vt =>
          have := (htarget_iff vt).mp htgt'
          rw [this] at htgt; cases htgt
        | error _ =>
          simp [evaluate, htgt', bind, Except.bind]
      | ok vt =>
        have htgtMt : evaluate mt req es = .ok vt := (htarget_iff vt).mpr htgt
        simp only [evaluate, htgtMt, bind, Except.bind]
        cases apply₁ (UnaryOp.is et) vt <;> simp
    | some ie, hMatch =>
      simp [Option.bind_eq_some_iff] at hMatch
      have ⟨mi, hmi, hres⟩ := hMatch
      subst hres
      simp [ExprOrSpecial.toExpr?] at heos
      rw [← heos]
      have hEtyName := addExpr_toEntityType_agrees hEt
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmt
      have ⟨tEos, htEos, htExpr⟩ := hmt
      have htarget_iff :=
        @Cst.AddExpr.toAExpr?_evaluate target tEos req es htEos mt htExpr
      simp [Cst.AddExpr.toAExpr?, Option.bind_eq_some_iff] at hmi
      have ⟨iEos, hiEos, hiExpr⟩ := hmi
      have hinEntity_iff :=
        @Cst.AddExpr.toAExpr?_evaluate ie iEos req es hiEos mi hiExpr
      exact rIsIn_some_eval_agrees hEtyName htarget_iff hinEntity_iff v
termination_by (sizeOf rel, 0)
decreasing_by
  all_goals (apply Prod.Lex.left; decreasing_tactic)


/-- Fold-helper analog for `AndExpr`. Mirrors `addExprFoldExtended_foldOps_agrees`,
    with `Expr.and` replacing `binaryApp` and `Relation` replacing `MultExpr`. -/
theorem andExprFoldExtended_foldOps_agrees
  (req : Request) (es : Entities)
  (xs : List Cst.Relation)
  {acc_ast : Expr} {result : Expr} :
  Cst.AndExpr.foldExtended acc_ast xs = some result →
  ∀ v, evaluate result req es = .ok v ↔
       (do let acc_v ← evaluate acc_ast req es
           Cst.AndExpr.foldOps acc_v xs req es) = .ok v := by
  intro hfold v
  match xs with
  | [] =>
    simp [Cst.AndExpr.foldExtended] at hfold
    simp [hfold]; constructor <;> intro h
    · simp [h, bind, Except.bind, Cst.AndExpr.foldOps]
    · cases hres : evaluate result req es with
      | error err => simp [bind, Except.bind, hres] at h
      | ok v' =>
        simp [bind, Except.bind, hres] at h
        simp [Cst.AndExpr.foldOps] at h
        rw [h]
  | rel :: rest =>
    simp [Cst.AndExpr.foldExtended] at hfold
    cases hrel : rel.toAExpr? with
    | none => rw [hrel] at hfold; simp at hfold
    | some erel =>
      rw [hrel] at hfold
      simp at hfold
      have ih' := andExprFoldExtended_foldOps_agrees req es rest hfold v
      rw [ih']
      simp [Cst.Relation.toAExpr?, Option.bind_eq_some_iff] at hrel
      obtain ⟨reos, hreos, hrm⟩ := hrel
      have hrel_iff : ∀ vp, evaluate erel req es = .ok vp ↔ rel.evaluate req es = .ok vp :=
        Cst.Relation.toAExpr?_evaluate hreos erel hrm
      simp [bind, Except.bind]
      cases h_acc : evaluate acc_ast req es with
      | error err =>
        simp [evaluate, h_acc, bind, Except.bind, Result.as]
      | ok acc_v =>
        simp
        exact expr_and_eval_eq_foldOps_step req es acc_ast erel acc_v rel rest h_acc hrel_iff v
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     simp only [List.cons.sizeOf_spec] at *
     omega)

theorem Cst.AndExpr.toAExpr?_evaluate
  {ae : Cst.AndExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  ae.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  ae.evaluate req es = .ok v := by
  intro hae aexp heos v
  match hext : ae.extended with
  | [] =>
    simp only [Cst.AndExpr.toExprOrSpecial?, hext] at hae
    have hr_iff := @Cst.Relation.toAExpr?_evaluate ae.initial eos req es hae aexp heos v
    rw [hr_iff]
    simp [Cst.AndExpr.evaluate]
    cases h_init : ae.initial.evaluate req es with
    | error err => simp [bind, Except.bind]
    | ok iv => simp [bind, Except.bind, Cst.AndExpr.foldOps, hext]
  | hd :: tl =>
    simp [Cst.AndExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hae
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hae
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [andExprFoldExtended_foldOps_agrees req es _ hres v]
    simp [Cst.Relation.toAExpr?, Option.bind_eq_some_iff] at hfirst
    obtain ⟨reos, hreos, hfeu⟩ := hfirst
    have hr_iff : ∀ vp, evaluate first req es = .ok vp ↔ ae.initial.evaluate req es = .ok vp :=
      Cst.Relation.toAExpr?_evaluate hreos first hfeu
    simp [Cst.AndExpr.evaluate]
    cases h_init : ae.initial.evaluate req es with
    | error err =>
      simp [bind, Except.bind]
      cases h_first : evaluate first req es with
      | ok vp =>
        have := (hr_iff vp).mp h_first
        rw [this] at h_init; cases h_init
      | error _ => simp
    | ok iv =>
      simp [bind, Except.bind, hext]
      have h_first : evaluate first req es = .ok iv := (hr_iff iv).mpr h_init
      rw [h_first]
termination_by (sizeOf ae, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     cases ae
     simp only [Cst.AndExpr.mk.sizeOf_spec]
     try (have h := hext; subst h)
     omega)


/-- Fold-helper analog for `OrExpr`. Mirrors `andExprFoldExtended_foldOps_agrees`,
    with `Expr.or` replacing `Expr.and` and `AndExpr` replacing `Relation`. -/
theorem orExprFoldExtended_foldOps_agrees
  (req : Request) (es : Entities)
  (xs : List Cst.AndExpr)
  {acc_ast : Expr} {result : Expr} :
  Cst.OrExpr.foldExtended acc_ast xs = some result →
  ∀ v, evaluate result req es = .ok v ↔
       (do let acc_v ← evaluate acc_ast req es
           Cst.OrExpr.foldOps acc_v xs req es) = .ok v := by
  intro hfold v
  match xs with
  | [] =>
    simp [Cst.OrExpr.foldExtended] at hfold
    simp [hfold]; constructor <;> intro h
    · simp [h, bind, Except.bind, Cst.OrExpr.foldOps]
    · cases hres : evaluate result req es with
      | error err => simp [bind, Except.bind, hres] at h
      | ok v' =>
        simp [bind, Except.bind, hres] at h
        simp [Cst.OrExpr.foldOps] at h
        rw [h]
  | ande :: rest =>
    simp [Cst.OrExpr.foldExtended] at hfold
    cases hande : ande.toAExpr? with
    | none => rw [hande] at hfold; simp at hfold
    | some eande =>
      rw [hande] at hfold
      simp at hfold
      have ih' := orExprFoldExtended_foldOps_agrees req es rest hfold v
      rw [ih']
      simp [Cst.AndExpr.toAExpr?, Option.bind_eq_some_iff] at hande
      obtain ⟨aeos, haeos, ham⟩ := hande
      have hande_iff : ∀ vp, evaluate eande req es = .ok vp ↔ ande.evaluate req es = .ok vp :=
        Cst.AndExpr.toAExpr?_evaluate haeos eande ham
      simp [bind, Except.bind]
      cases h_acc : evaluate acc_ast req es with
      | error err =>
        simp [evaluate, h_acc, bind, Except.bind, Result.as]
      | ok acc_v =>
        simp
        exact expr_or_eval_eq_foldOps_step req es acc_ast eande acc_v ande rest h_acc hande_iff v
termination_by (sizeOf xs, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     simp only [List.cons.sizeOf_spec] at *
     omega)

theorem Cst.OrExpr.toAExpr?_evaluate
  {oe : Cst.OrExpr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  oe.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  oe.evaluate req es = .ok v := by
  intro hoe aexp heos v
  match hext : oe.extended with
  | [] =>
    simp only [Cst.OrExpr.toExprOrSpecial?, hext] at hoe
    have ha_iff := @Cst.AndExpr.toAExpr?_evaluate oe.initial eos req es hoe aexp heos v
    rw [ha_iff]
    simp [Cst.OrExpr.evaluate]
    cases h_init : oe.initial.evaluate req es with
    | error err => simp [bind, Except.bind]
    | ok iv => simp [bind, Except.bind, Cst.OrExpr.foldOps, hext]
  | hd :: tl =>
    simp [Cst.OrExpr.toExprOrSpecial?, hext, Option.bind_eq_some_iff] at hoe
    obtain ⟨first, hfirst, result, hres, heos_eq⟩ := hoe
    rw [← heos_eq] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    rw [orExprFoldExtended_foldOps_agrees req es _ hres v]
    simp [Cst.AndExpr.toAExpr?, Option.bind_eq_some_iff] at hfirst
    obtain ⟨aeos, haeos, hfeu⟩ := hfirst
    have ha_iff : ∀ vp, evaluate first req es = .ok vp ↔ oe.initial.evaluate req es = .ok vp :=
      Cst.AndExpr.toAExpr?_evaluate haeos first hfeu
    simp [Cst.OrExpr.evaluate]
    cases h_init : oe.initial.evaluate req es with
    | error err =>
      simp [bind, Except.bind]
      cases h_first : evaluate first req es with
      | ok vp =>
        have := (ha_iff vp).mp h_first
        rw [this] at h_init; cases h_init
      | error _ => simp
    | ok iv =>
      simp [bind, Except.bind, hext]
      have h_first : evaluate first req es = .ok iv := (ha_iff iv).mpr h_init
      rw [h_first]
termination_by (sizeOf oe, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     cases oe
     simp only [Cst.OrExpr.mk.sizeOf_spec]
     try (have h := hext; subst h)
     omega)


theorem Cst.ExprData.toAExpr?_evaluate
  {ed : Cst.ExprData} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  ed.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  ed.evaluate req es = .ok v := by
  intro hed aexp heos v
  cases ed with
  | edOr ore =>
    simp [Cst.ExprData.toExprOrSpecial?] at hed
    simp [Cst.ExprData.evaluate]
    exact Cst.OrExpr.toAExpr?_evaluate hed aexp heos v
  | edIf i t f =>
    simp [Cst.ExprData.toExprOrSpecial?, Option.bind_eq_some_iff] at hed
    obtain ⟨eg, hg, et, ht, ef, hf, hres⟩ := hed
    rw [← hres] at heos
    simp [ExprOrSpecial.toExpr?] at heos
    rw [← heos]
    simp [Cst.Expr.toAExpr?, Option.bind_eq_some_iff] at hg ht hf
    obtain ⟨gEos, hgEos, hgExpr⟩ := hg
    obtain ⟨tEos, htEos, htExpr⟩ := ht
    obtain ⟨fEos, hfEos, hfExpr⟩ := hf
    have hg_iff : ∀ vp, evaluate eg req es = .ok vp ↔ i.evaluate req es = .ok vp :=
      Cst.Expr.toAExpr?_evaluate hgEos eg hgExpr
    have ht_iff : ∀ vp, evaluate et req es = .ok vp ↔ t.evaluate req es = .ok vp :=
      Cst.Expr.toAExpr?_evaluate htEos et htExpr
    have hf_iff : ∀ vp, evaluate ef req es = .ok vp ↔ f.evaluate req es = .ok vp :=
      Cst.Expr.toAExpr?_evaluate hfEos ef hfExpr
    simp [evaluate, Cst.ExprData.evaluate, bind, Except.bind, Result.as, Coe.coe]
    cases hg_eval : evaluate eg req es with
    | error err =>
      cases hi : i.evaluate req es with
      | ok iv =>
        have := (hg_iff iv).mpr hi
        rw [this] at hg_eval; cases hg_eval
      | error _ => simp
    | ok gv =>
      have hi_ok : i.evaluate req es = .ok gv := (hg_iff gv).mp hg_eval
      rw [hi_ok]
      cases gv with
      | prim p =>
        cases p with
        | bool b =>
          simp [Value.asBool]
          cases b with
          | true => exact ht_iff v
          | false => exact hf_iff v
        | int _ | string _ | entityUID _ => simp [Value.asBool]
      | set _ | record _ | ext _ => simp [Value.asBool]
termination_by (sizeOf ed, 0)
decreasing_by
  all_goals (apply Prod.Lex.left; decreasing_tactic)

theorem Cst.ExprImpl.toAExpr?_evaluate
  {ei : Cst.ExprImpl} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  ei.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  ei.evaluate req es = .ok v := by
  intro hei aexp heos v
  simp only [Cst.ExprImpl.toExprOrSpecial?] at hei
  simp [Cst.ExprImpl.evaluate]
  exact Cst.ExprData.toAExpr?_evaluate hei aexp heos v
termination_by (sizeOf ei, 0)
decreasing_by
  all_goals
    (apply Prod.Lex.left
     cases ei; simp only [Cst.ExprImpl.mk.sizeOf_spec]; omega)

theorem Cst.Expr.toAExpr?_evaluate
  {e : Cst.Expr} {eos : ExprOrSpecial}
  {req : Request} {es : Entities} :
  e.toExprOrSpecial? = some eos →
  ∀ aexp, eos.toExpr? = some aexp →
  ∀ v, evaluate aexp req es = .ok v ↔
  e.evaluate req es = .ok v := by
  intro he aexp heos v
  cases e with
  | expr ei =>
    simp only [Cst.Expr.toExprOrSpecial?] at he
    simp [Cst.Expr.evaluate]
    exact Cst.ExprImpl.toAExpr?_evaluate he aexp heos v
termination_by (sizeOf e, 0)
decreasing_by
  all_goals (apply Prod.Lex.left; decreasing_tactic)

theorem expr_to_expr_agrees
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

end
