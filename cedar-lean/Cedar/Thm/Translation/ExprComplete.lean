import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.Aux
import Cedar.Thm.Translation.AuxComplete
import Cedar.Thm.Translation.ExprTranslation
import Cedar.Thm.Data.List.Lemmas

/-!
Translation completeness for CST expressions: if a CST expression evaluates
without error, its translation to AST succeeds.

`Cst.Expr.toAExpr?_complete` is currently a `sorry` placeholder; the rest of the
mutual family (`Member`, `Unary`, …, down to `Expr`) will be filled in here.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

mutual

theorem Cst.Primary.toAExpr?_complete
  {prim : Cst.Primary} {req : Request} {es : Entities} {v : Value} :
  prim.evaluate req es = .ok v →
  ∃ eos ae, prim.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro hev
  cases prim with
  | literal lit =>
    cases lit with
    | liTrue =>
      exact ⟨.boolLit true, .lit (.bool true),
             by simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?],
             by simp [ExprOrSpecial.toExpr?]⟩
    | liFalse =>
      exact ⟨.boolLit false, .lit (.bool false),
             by simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?],
             by simp [ExprOrSpecial.toExpr?]⟩
    | liNum n =>
      simp only [Cst.Primary.evaluate] at hev
      cases hn : Int64.ofInt? (n.toNat : Int) with
      | none => rw [hn] at hev; simp at hev
      | some i =>
        refine ⟨.expr (.lit (.int i)), .lit (.int i), ?_, by simp [ExprOrSpecial.toExpr?]⟩
        simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?, hn]
    | liStr s =>
      simp only [Cst.Primary.evaluate, Cst.Str.toUnescapedString] at hev
      cases hs : CstCommon.unescape? s with
      | none => rw [hs] at hev; simp at hev
      | some s' =>
        refine ⟨.strLit s, .lit (.string s'),
                by simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?], ?_⟩
        simp [ExprOrSpecial.toExpr?, hs]
  | name n =>
    cases hvar : n.toVar? with
    | some var =>
      exact ⟨.var var, .var var, by simp [Cst.Primary.toExprOrSpecial?, hvar],
             by simp [ExprOrSpecial.toExpr?]⟩
    | none =>
      exfalso
      obtain ⟨npath, nname⟩ := n
      simp only [Cst.Name.toVar?] at hvar
      cases npath <;> cases nname <;>
        simp_all [Cst.Primary.evaluate]
  | ref r =>
    cases r with
    | uid path eid =>
      let (.string s) := eid
      simp only [Cst.Primary.evaluate, Cst.Str.toUnescapedString] at hev
      cases hs : CstCommon.unescape? s with
      | none => rw [hs] at hev; simp [bind, Except.bind] at hev
      | some s' =>
        rw [hs] at hev
        cases hty : CstCommon.Name.toAName? path with
        | none => simp [hty, bind, Except.bind] at hev
        | some ty =>
          refine ⟨.expr (.lit (.entityUID { ty := ty, eid := s' })),
                  .lit (.entityUID { ty := ty, eid := s' }), ?_, by simp [ExprOrSpecial.toExpr?]⟩
          simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?, Cst.Name.toAName?, hty, hs]
    | ref path rinits =>
      simp [Cst.Primary.evaluate] at hev
  | expr e =>
    simp only [Cst.Primary.evaluate] at hev
    obtain ⟨eos_e, ae, heos_e, hae⟩ := Cst.Expr.toAExpr?_complete hev
    refine ⟨.expr ae, ae, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp [Cst.Primary.toExprOrSpecial?, Cst.Expr.toAExpr?, heos_e, hae]
  | eList xs =>
    simp only [Cst.Primary.evaluate, bind, Except.bind] at hev
    cases hxs : xs.mapM (fun x => x.evaluate req es) with
    | error e => rw [hxs] at hev; simp at hev
    | ok vs =>
      obtain ⟨aes, haes⟩ := list_eval_complete xs vs hxs
        (fun x _hx _v hxv => by
          obtain ⟨eos, ae, heos, hae⟩ := Cst.Expr.toAExpr?_complete hxv
          exact ⟨ae, by simp [Cst.Expr.toAExpr?, heos, hae]⟩)
      refine ⟨.expr (.set aes), .set aes, ?_, by simp [ExprOrSpecial.toExpr?]⟩
      simp [Cst.Primary.toExprOrSpecial?, List.mapM₁_eq_mapM (fun x : Cst.Expr => x.toAExpr?), haes]
  | rInits r =>
    have hCST : (Cst.Primary.rInits r).evaluate req es =
        (r.mapM (fun ri =>
          match ri.key.toAttr? with
          | none => Except.error Error.typeError
          | some attr => do let val ← ri.value.evaluate req es; Except.ok (attr, val))) >>=
        fun avs => Except.ok (Value.record (Map.make avs)) := by
      simp only [Cst.Primary.evaluate]
      congr 1
      exact List.mapM₁_eq_mapM (fun ri : Cst.RecInit =>
        match ri.key.toAttr? with
        | none => Except.error Error.typeError
        | some attr => do let val ← ri.value.evaluate req es; Except.ok (attr, val)) r
    rw [hCST] at hev
    cases hrv : r.mapM (fun ri =>
        match ri.key.toAttr? with
        | none => Except.error Error.typeError
        | some attr => do let val ← ri.value.evaluate req es; Except.ok (attr, val)) with
    | error e => rw [hrv] at hev; simp [bind, Except.bind] at hev
    | ok avs =>
      obtain ⟨map, hmap⟩ := rInits_complete r avs hrv
        (fun ri _hri _v hv => by
          obtain ⟨eos, ae, heos, hae⟩ := Cst.Expr.toAExpr?_complete hv
          exact ⟨ae, by simp [Cst.Expr.toAExpr?, heos, hae]⟩)
      refine ⟨.expr (.record map), .record map, ?_, by simp [ExprOrSpecial.toExpr?]⟩
      simp [Cst.Primary.toExprOrSpecial?, hmap]

theorem Cst.Member.toAExpr?_complete
  {mem : Cst.Member} {req : Request} {es : Entities} {v : Value} :
  mem.evaluate req es = .ok v →
  ∃ eos ae, mem.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro hev
  have harg : ∀ ce : Cst.Expr, sizeOf ce < sizeOf mem.access →
      ∀ w, ce.evaluate req es = .ok w → ∃ ax, ce.toAExpr? = some ax := by
    intro ce _hsz w hcw
    obtain ⟨eos', ae', heos', hae'⟩ := Cst.Expr.toAExpr?_complete hcw
    exact ⟨ae', by simp [Cst.Expr.toAExpr?, heos', hae']⟩
  unfold Cst.Member.evaluate at hev
  split at hev
  case h_1 s args rest =>
    cases hfn : CstCommon.String.toExtFun? s with
    | none => rw [hfn] at hev; simp at hev
    | some xfn =>
      rw [hfn] at hev
      cases hargs : args.mapM (fun a => a.evaluate req es) with
      | error e => rw [hargs] at hev; simp [bind, Except.bind] at hev
      | ok argVals =>
        rw [hargs] at hev; simp only [bind, Except.bind] at hev
        cases hcall : call xfn argVals with
        | error e => rw [hcall] at hev; simp at hev
        | ok callVal =>
          rw [hcall] at hev
          obtain ⟨xs, hxs⟩ := list_eval_complete args argVals hargs
            (fun ce hce w hcw => harg ce (by
              show sizeOf ce < sizeOf (Cst.MemAccess.call args :: rest)
              have := List.sizeOf_lt_of_mem hce
              simp only [List.cons.sizeOf_spec, Cst.MemAccess.call.sizeOf_spec]; omega) w hcw)
          obtain ⟨rest_ast, hrest, _, hmemb⟩ := evalAccessors_complete rest callVal v hev
            (fun ce hsz w hcw => harg ce (by
              show sizeOf ce < sizeOf (Cst.MemAccess.call args :: rest)
              simp only [List.cons.sizeOf_spec, Cst.MemAccess.call.sizeOf_spec] at hsz ⊢; omega)
              w hcw)
          obtain ⟨r, hr⟩ := hmemb (.call xfn xs)
          refine ⟨.expr r, r, ?_, by simp [ExprOrSpecial.toExpr?]⟩
          simp [Cst.Member.toExprOrSpecial?, Cst.Primary.toExprOrSpecial?,
            Cst.Name.toVar?, List.isEmpty_nil, Cst.Name.toAName?, CstCommon.Name.toAName?,
            CstCommon.Ident.toUnrestrictedString?, List.mapM_cons, Cst.MemAccess.toAstAccessor?,
            toAExprs?_eq_mapM, hxs, hrest, memberAux, memberAuxA, Name.toFunc?,
            toExtFun?_some_isFunctionName hfn, hfn, hr]
  case h_2 item access hnfc =>
    simp only [bind, Except.bind] at hev
    cases hitem : item.evaluate req es with
    | error e => rw [hitem] at hev; simp at hev
    | ok head =>
      rw [hitem] at hev; simp only at hev
      obtain ⟨peos, headExpr, hpeos, hpe⟩ := Cst.Primary.toAExpr?_complete hitem
      obtain ⟨accs_ast, haccs, _, hmemb⟩ := evalAccessors_complete access head v hev harg
      obtain ⟨r, hr⟩ := hmemb headExpr
      have hbind : (memberAux peos accs_ast).bind ExprOrSpecial.toExpr? = some r := by
        rw [memberAux_toExpr_eq accs_ast hpe]; exact hr
      rw [Option.bind_eq_some_iff] at hbind
      obtain ⟨eos, hmaux, heos⟩ := hbind
      refine ⟨eos, r, ?_, heos⟩
      simp only [Cst.Member.toExprOrSpecial?, hpeos, haccs, hmaux, Option.bind_some,
        Option.bind_eq_bind]

theorem Cst.Unary.toAExpr?_complete
  {u : Cst.Unary} {req : Request} {es : Entities} {v : Value} :
  u.evaluate req es = .ok v →
  ∃ eos ae, u.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro hev
  match hop : u.op with
  | none =>
    simp only [Cst.Unary.evaluate, hop] at hev
    obtain ⟨eos, ae, heos, hae⟩ := Cst.Member.toAExpr?_complete hev
    exact ⟨eos, ae, by simp [Cst.Unary.toExprOrSpecial?, hop, heos], hae⟩
  | some (.nBang n) =>
    simp only [Cst.Unary.evaluate, hop] at hev
    cases hitem : u.item.evaluate req es with
    | error e => simp [hitem, bind, Except.bind] at hev
    | ok mval =>
      obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.Member.toAExpr?_complete hitem
      exact ⟨.expr (iexpr.bangN n.toNat), iexpr.bangN n.toNat,
             by simp [Cst.Unary.toExprOrSpecial?, hop, hieos, hiexpr],
             by simp [ExprOrSpecial.toExpr?]⟩
  | some (.nDash n) =>
    by_cases hn0 : n = 0
    · subst hn0
      simp only [Cst.Unary.evaluate, hop] at hev
      simp only [beq_self_eq_true, if_true] at hev
      obtain ⟨eos, ae, heos, hae⟩ := Cst.Member.toAExpr?_complete hev
      exact ⟨eos, ae, by simp [Cst.Unary.toExprOrSpecial?, hop, heos], hae⟩
    · simp only [Cst.Unary.evaluate, hop] at hev
      rw [if_neg (by simp [hn0])] at hev
      cases hlit : CstCommon.Member.toLit? u.item with
      | none =>
        simp only [hlit] at hev
        cases hitem : u.item.evaluate req es with
        | error e => rw [hitem] at hev; simp [bind, Except.bind] at hev
        | ok mval =>
          obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.Member.toAExpr?_complete hitem
          exact ⟨.expr (iexpr.dashN n.toNat), iexpr.dashN n.toNat,
                 by simp [Cst.Unary.toExprOrSpecial?, hop, hlit, hieos, hiexpr],
                 by simp [ExprOrSpecial.toExpr?]⟩
      | some lit =>
        cases lit with
        | liNum x =>
          simp only [hlit] at hev
          cases hcmp : compare x.toNat (Int64.MAX + 1).toNat with
          | gt => rw [hcmp] at hev; simp at hev
          | eq =>
            exact ⟨.expr ((Expr.lit (.int Int64.MIN.toInt64)).dashN (n-1).toNat),
                   (Expr.lit (.int Int64.MIN.toInt64)).dashN (n-1).toNat,
                   by simp [Cst.Unary.toExprOrSpecial?, hop, hlit, hcmp],
                   by simp [ExprOrSpecial.toExpr?]⟩
          | lt =>
            simp only [hcmp] at hev
            cases hof : Int64.ofInt? (x.toNat : Int) with
            | none => simp [hof] at hev
            | some y =>
              exact ⟨.expr ((Expr.lit (.int (-y))).dashN (n-1).toNat),
                     (Expr.lit (.int (-y))).dashN (n-1).toNat,
                     by simp [Cst.Unary.toExprOrSpecial?, hop, hlit, hcmp, hof],
                     by simp [ExprOrSpecial.toExpr?]⟩
        | liTrue =>
          simp only [hlit] at hev
          cases hitem : u.item.evaluate req es with
          | error e => rw [hitem] at hev; simp [bind, Except.bind] at hev
          | ok mval =>
            obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.Member.toAExpr?_complete hitem
            exact ⟨.expr (iexpr.dashN n.toNat), iexpr.dashN n.toNat,
                   by simp [Cst.Unary.toExprOrSpecial?, hop, hlit, hieos, hiexpr],
                   by simp [ExprOrSpecial.toExpr?]⟩
        | liFalse =>
          simp only [hlit] at hev
          cases hitem : u.item.evaluate req es with
          | error e => rw [hitem] at hev; simp [bind, Except.bind] at hev
          | ok mval =>
            obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.Member.toAExpr?_complete hitem
            exact ⟨.expr (iexpr.dashN n.toNat), iexpr.dashN n.toNat,
                   by simp [Cst.Unary.toExprOrSpecial?, hop, hlit, hieos, hiexpr],
                   by simp [ExprOrSpecial.toExpr?]⟩
        | liStr s =>
          simp only [hlit] at hev
          cases hitem : u.item.evaluate req es with
          | error e => rw [hitem] at hev; simp [bind, Except.bind] at hev
          | ok mval =>
            obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.Member.toAExpr?_complete hitem
            exact ⟨.expr (iexpr.dashN n.toNat), iexpr.dashN n.toNat,
                   by simp [Cst.Unary.toExprOrSpecial?, hop, hlit, hieos, hiexpr],
                   by simp [ExprOrSpecial.toExpr?]⟩
  | some .nOverBang => simp [Cst.Unary.evaluate, hop] at hev
  | some .nOverDash => simp [Cst.Unary.evaluate, hop] at hev

theorem Cst.MultExpr.toAExpr?_complete
  {mult : Cst.MultExpr} {req : Request} {es : Entities} {v : Value} :
  mult.evaluate req es = .ok v →
  ∃ eos ae, mult.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro hev
  simp only [Cst.MultExpr.evaluate] at hev
  cases hinit : mult.initial.evaluate req es with
  | error e => rw [hinit] at hev; simp [bind, Except.bind] at hev
  | ok b =>
    rw [hinit] at hev
    simp only [bind, Except.bind] at hev
    match hext : mult.extended with
    | [] =>
      obtain ⟨eos, ae, heos, hae⟩ := Cst.Unary.toAExpr?_complete hinit
      exact ⟨eos, ae, by simp [Cst.MultExpr.toExprOrSpecial?, hext, heos], hae⟩
    | hd :: tl =>
      obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.Unary.toAExpr?_complete hinit
      have hinitA : mult.initial.toAExpr? = some iexpr := by
        simp [Cst.Unary.toAExpr?, hieos, hiexpr]
      obtain ⟨result, hresult⟩ :=
        multExprFoldExtended_complete mult.extended b iexpr v hev
          (fun u' _hsz w hw => by
            obtain ⟨eos', ae', heos', hae'⟩ := Cst.Unary.toAExpr?_complete hw
            exact ⟨ae', by simp [Cst.Unary.toAExpr?, heos', hae']⟩)
      refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
      simp only [hext] at hresult
      simp [Cst.MultExpr.toExprOrSpecial?, hext, hinitA, hresult]

theorem Cst.AddExpr.toAExpr?_complete
  {add : Cst.AddExpr} {req : Request} {es : Entities} {v : Value} :
  add.evaluate req es = .ok v →
  ∃ eos ae, add.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro hev
  simp only [Cst.AddExpr.evaluate] at hev
  cases hinit : add.initial.evaluate req es with
  | error e => rw [hinit] at hev; simp [bind, Except.bind] at hev
  | ok b =>
    rw [hinit] at hev
    simp only [bind, Except.bind] at hev
    match hext : add.extended with
    | [] =>
      obtain ⟨eos, ae, heos, hae⟩ := Cst.MultExpr.toAExpr?_complete hinit
      exact ⟨eos, ae, by simp [Cst.AddExpr.toExprOrSpecial?, hext, heos], hae⟩
    | hd :: tl =>
      obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.MultExpr.toAExpr?_complete hinit
      have hinitA : add.initial.toAExpr? = some iexpr := by
        simp [Cst.MultExpr.toAExpr?, hieos, hiexpr]
      obtain ⟨result, hresult⟩ :=
        addExprFoldExtended_complete add.extended b iexpr v hev
          (fun m' _hsz w hw => by
            obtain ⟨eos', ae', heos', hae'⟩ := Cst.MultExpr.toAExpr?_complete hw
            exact ⟨ae', by simp [Cst.MultExpr.toAExpr?, heos', hae']⟩)
      refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
      simp only [hext] at hresult
      simp [Cst.AddExpr.toExprOrSpecial?, hext, hinitA, hresult]

theorem Cst.Relation.toAExpr?_complete
  {rel : Cst.Relation} {req : Request} {es : Entities} {v : Value} :
  rel.evaluate req es = .ok v →
  ∃ eos ae, rel.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro hev
  cases rel with
  | rCommon initial extended =>
    match hext : extended with
    | [] =>
      simp only [Cst.Relation.evaluate] at hev
      obtain ⟨eos, ae, heos, hae⟩ := Cst.AddExpr.toAExpr?_complete hev
      exact ⟨eos, ae, by simp [Cst.Relation.toExprOrSpecial?, heos], hae⟩
    | (op, y) :: rest =>
      match hrest : rest with
      | _ :: _ => simp [Cst.Relation.evaluate] at hev
      | [] =>
        simp only [Cst.Relation.evaluate] at hev
        cases hi : initial.evaluate req es with
        | error e => rw [hi] at hev; simp [bind, Except.bind] at hev
        | ok v₁ =>
          rw [hi] at hev
          cases hy : y.evaluate req es with
          | error e => rw [hy] at hev; simp [bind, Except.bind] at hev
          | ok v₂ =>
            obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.AddExpr.toAExpr?_complete hi
            obtain ⟨yeos, yexpr, hyeos, hyexpr⟩ := Cst.AddExpr.toAExpr?_complete hy
            have hyA : y.toAExpr? = some yexpr := by simp [Cst.AddExpr.toAExpr?, hyeos, hyexpr]
            refine ⟨.expr (constructExprRel op iexpr yexpr), constructExprRel op iexpr yexpr,
                    ?_, by simp [ExprOrSpecial.toExpr?]⟩
            simp [Cst.Relation.toExprOrSpecial?, hieos, hiexpr, hyA]
  | rHas target field =>
    simp only [Cst.Relation.evaluate] at hev
    cases hrhs : field.toHasRhs? with
    | none => rw [hrhs] at hev; simp at hev
    | some rhs =>
      rw [hrhs] at hev
      simp only [Option.isNone_some, Bool.false_eq_true, if_false] at hev
      cases htgt : target.evaluate req es with
      | error e => rw [htgt] at hev; simp [bind, Except.bind] at hev
      | ok vt =>
        obtain ⟨teos, texpr, hteos, htexpr⟩ := Cst.AddExpr.toAExpr?_complete htgt
        have htgtA : target.toAExpr? = some texpr := by simp [Cst.AddExpr.toAExpr?, hteos, htexpr]
        cases rhs with
        | inl f =>
          exact ⟨.expr (.hasAttr texpr f), .hasAttr texpr f,
                 by simp [Cst.Relation.toExprOrSpecial?, htgtA, hrhs], by simp [ExprOrSpecial.toExpr?]⟩
        | inr fs =>
          exact ⟨.expr (extendedHasAttr texpr fs), extendedHasAttr texpr fs,
                 by simp [Cst.Relation.toExprOrSpecial?, htgtA, hrhs], by simp [ExprOrSpecial.toExpr?]⟩
  | rLike target pattern =>
    simp only [Cst.Relation.evaluate] at hev
    cases hpat : pattern.toPattern? with
    | none => rw [hpat] at hev; simp at hev
    | some mp =>
      rw [hpat] at hev
      simp only [Option.isNone_some, Bool.false_eq_true, if_false] at hev
      cases hps : pattern.toPatternString? with
      | none => rw [hps] at hev; simp at hev
      | some s =>
        rw [hps] at hev
        cases htgt : target.evaluate req es with
        | error e => rw [htgt] at hev; simp [bind, Except.bind] at hev
        | ok vt =>
          obtain ⟨teos, texpr, hteos, htexpr⟩ := Cst.AddExpr.toAExpr?_complete htgt
          have htgtA : target.toAExpr? = some texpr := by simp [Cst.AddExpr.toAExpr?, hteos, htexpr]
          exact ⟨.expr (.unaryApp (.like mp) texpr), .unaryApp (.like mp) texpr,
                 by simp [Cst.Relation.toExprOrSpecial?, htgtA, hpat], by simp [ExprOrSpecial.toExpr?]⟩
  | rIsIn target ety inEntity =>
    simp only [Cst.Relation.evaluate] at hev
    cases hety : ety.toEntityType? with
    | none => rw [hety] at hev; simp at hev
    | some etyName =>
      rw [hety] at hev
      cases htgt : target.evaluate req es with
      | error e => rw [htgt] at hev; simp [bind, Except.bind] at hev
      | ok vt =>
        rw [htgt] at hev
        simp only [bind, Except.bind] at hev
        obtain ⟨teos, texpr, hteos, htexpr⟩ := Cst.AddExpr.toAExpr?_complete htgt
        have htgtA : target.toAExpr? = some texpr := by simp [Cst.AddExpr.toAExpr?, hteos, htexpr]
        cases hap : apply₁ (.is etyName) vt with
        | error e => rw [hap] at hev; simp at hev
        | ok isResult =>
          rw [hap] at hev
          match hinE : inEntity with
          | none =>
            exact ⟨.expr (.unaryApp (.is etyName) texpr), .unaryApp (.is etyName) texpr,
                   by simp [Cst.Relation.toExprOrSpecial?, htgtA, hety],
                   by simp [ExprOrSpecial.toExpr?]⟩
          | some ie =>
            cases hie : ie.toAExpr? with
            | none => simp [hie] at hev
            | some mi =>
              exact ⟨.expr (.and (.unaryApp (.is etyName) texpr) (.binaryApp .mem texpr mi)),
                     .and (.unaryApp (.is etyName) texpr) (.binaryApp .mem texpr mi),
                     by simp [Cst.Relation.toExprOrSpecial?, htgtA, hety, hie],
                     by simp [ExprOrSpecial.toExpr?]⟩

theorem Cst.AndExpr.toAExpr?_complete
  {ae : Cst.AndExpr} {req : Request} {es : Entities} {v : Value} :
  ae.evaluate req es = .ok v →
  ∃ eos aexpr, ae.toExprOrSpecial? = some eos ∧ eos.toExpr? = some aexpr := by
  intro hev
  by_cases hall : (ae.extended.all fun r => r.toAExpr?.isSome) = true
  · rw [AndExpr.evaluate_eq hall] at hev
    cases hinit : ae.initial.evaluate req es with
    | error e => rw [hinit] at hev; simp [bind, Except.bind] at hev
    | ok acc =>
      obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.Relation.toAExpr?_complete hinit
      match hext : ae.extended with
      | [] =>
        exact ⟨ieos, iexpr, by simp [Cst.AndExpr.toExprOrSpecial?, hext, hieos], hiexpr⟩
      | hd :: tl =>
        have hinitA : ae.initial.toAExpr? = some iexpr := by
          simp [Cst.Relation.toAExpr?, hieos, hiexpr]
        obtain ⟨result, hresult⟩ := andExprFoldExtended_complete ae.extended hall iexpr
        refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
        simp only [hext] at hresult
        simp [Cst.AndExpr.toExprOrSpecial?, hext, hinitA, hresult]
  · simp [Cst.AndExpr.evaluate, hall] at hev

theorem Cst.OrExpr.toAExpr?_complete
  {oe : Cst.OrExpr} {req : Request} {es : Entities} {v : Value} :
  oe.evaluate req es = .ok v →
  ∃ eos aexpr, oe.toExprOrSpecial? = some eos ∧ eos.toExpr? = some aexpr := by
  intro hev
  by_cases hall : (oe.extended.all fun r => r.toAExpr?.isSome) = true
  · rw [OrExpr.evaluate_eq hall] at hev
    cases hinit : oe.initial.evaluate req es with
    | error e => rw [hinit] at hev; simp [bind, Except.bind] at hev
    | ok acc =>
      obtain ⟨ieos, iexpr, hieos, hiexpr⟩ := Cst.AndExpr.toAExpr?_complete hinit
      match hext : oe.extended with
      | [] =>
        exact ⟨ieos, iexpr, by simp [Cst.OrExpr.toExprOrSpecial?, hext, hieos], hiexpr⟩
      | hd :: tl =>
        have hinitA : oe.initial.toAExpr? = some iexpr := by
          simp [Cst.AndExpr.toAExpr?, hieos, hiexpr]
        obtain ⟨result, hresult⟩ := orExprFoldExtended_complete oe.extended hall iexpr
        refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
        simp only [hext] at hresult
        simp [Cst.OrExpr.toExprOrSpecial?, hext, hinitA, hresult]
  · simp [Cst.OrExpr.evaluate, hall] at hev

theorem Cst.Expr.toAExpr?_complete
  {e : Cst.Expr} {req : Request} {es : Entities} {v : Value} :
  e.evaluate req es = .ok v →
  ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  sorry

end

end Cedar.Thm
