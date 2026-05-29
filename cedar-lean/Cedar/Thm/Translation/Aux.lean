import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

theorem ExprOrSpecial.toExpr?_none (eos : ExprOrSpecial) :
  eos.toExpr? = none →
  (∃ s, eos = .strLit s ∧ CstCommon.unescape? s = none) ∨
  (∃ n, eos = .name n) := by
  intro h
  match eos with
  | .expr e => simp [ExprOrSpecial.toExpr?] at h
  | .var v => simp [ExprOrSpecial.toExpr?] at h
  | .boolLit b => simp [ExprOrSpecial.toExpr?] at h
  | .strLit s =>
    left; exists s; constructor
    · rfl
    · match hs : CstCommon.unescape? s with
      | none => rfl
      | some s' => simp [ExprOrSpecial.toExpr?, hs] at h
  | .name n => right; exists n

/- For Primary -/

theorem Cst.Ident.toUnrestrictedString?_eq_toString
    {i : Cst.Ident} {s : String} :
    Cst.Ident.toUnrestrictedString? i = some s →
    s = CstCommon.Ident.toString i := by
  cases i <;> intro h <;> simp [Cst.Ident.toUnrestrictedString?] at h
  all_goals first | rfl | (rw [← h]; rfl)

/-- If `mapM` over `toUnrestrictedString?` succeeds, the result equals `map toString`. -/
theorem mapM_toUnrestrictedString?_eq_map
    {l : List Cst.Ident} {result : List String} :
    l.mapM Cst.Ident.toUnrestrictedString? = some result →
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
    exact ⟨Cst.Ident.toUnrestrictedString?_eq_toString hs, ih hrest⟩

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
  · exact Cst.Ident.toUnrestrictedString?_eq_toString hid
  · exact mapM_toUnrestrictedString?_eq_map hpath

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

/- For Member -/

def attrAccessorAgrees (acc : AstAccessor) (attr : Attr) : Bool :=
  match acc with
  | .field (.idIdent s) => s = attr
  | .index s => s = attr
  | _ => false

def attrsAccessorsAgree : List AstAccessor → List Attr → Bool
  | [], [] => true
  | acc :: accs, attr :: attrs =>
      attrAccessorAgrees acc attr && attrsAccessorsAgree accs attrs
  | _, _ => false

theorem item_none_member_none (mem : Cst.Member) :
  mem.item.toAExpr? = none →
  mem.toAExpr? = none := by
  obtain ⟨item, acc⟩ := mem
  intro hitem
  simp [Cst.Primary.toAExpr?, Option.bind_eq_none_iff] at hitem
  simp [Cst.Member.toAExpr?, Cst.Member.toExprOrSpecial?, Option.bind_eq_none_iff]
  intro eos hmem_trans
  simp only [Option.bind_eq_some_iff] at hmem_trans
  obtain ⟨ieos, hieos, accessors, haccessors, hmaux⟩ := hmem_trans
  specialize hitem ieos hieos
  cases accessors with
  | nil =>
    simp [memberAux] at hmaux
    rw [← hmaux]; exact hitem
  | cons hd tl =>
    cases ieos with
    | expr e => simp [ExprOrSpecial.toExpr?] at hitem
    | var v => simp [ExprOrSpecial.toExpr?] at hitem
    | boolLit b => simp [ExprOrSpecial.toExpr?] at hitem
    | strLit s => simp [memberAux, hitem] at hmaux
    | name n  =>
      cases hd with
      | field _ => simp [memberAux] at hmaux
      | index _ => simp [memberAux] at hmaux

theorem toAstAccessor_attrChain_agrees (accs : List Cst.MemAccess)
  (ret1 : List AstAccessor) (ret2 : List Attr) :
  accs.mapM (Cst.MemAccess.toAstAccessor?) = some ret1 →
  Cst.AttrChain? accs = some ret2 →
  attrsAccessorsAgree ret1 ret2 := by
  induction accs generalizing ret1 ret2 with
  | nil =>
    intro h1 h2
    simp at h1; simp [Cst.AttrChain?] at h2
    rw [h1, h2]; simp [attrsAccessorsAgree]
  | cons acc tl ih =>
    intro h1 h2
    match acc with
    | .field (.idIdent s) =>
      simp [List.mapM_cons, Option.bind_eq_some_iff] at h1
      obtain ⟨hd1, hhd1, tl1, htl1, hret1⟩ := h1
      simp [Cst.MemAccess.toAstAccessor?] at hhd1
      simp [Cst.AttrChain?] at h2
      match h : (CstCommon.Ident.toUnreservedString? (Cst.Ident.idIdent s)) with
      | none => simp [h] at h2
      | some hd2 =>
        simp [h] at hhd1 h2
        obtain ⟨tl2, htl2, hret2⟩ := h2
        simp [←hret1, ←hret2, attrsAccessorsAgree]; constructor
        · simp [CstCommon.Ident.toUnreservedString?] at h
          obtain ⟨hl, hr⟩ := h
          rw [← hhd1, ← hr]; simp [attrAccessorAgrees]
        · apply (ih tl1 tl2 htl1 htl2)
    | .index e =>
      simp [List.mapM_cons, Option.bind_eq_some_iff] at h1
      obtain ⟨hd1, hhd1, tl1, htl1, hret1⟩ := h1
      simp [Cst.MemAccess.toAstAccessor?] at hhd1
      simp [Cst.AttrChain?] at h2
      match h : (CstCommon.Expr.toUnescapedStringLiteral? e) with
      | none => simp [h] at h2
      | some hd2 =>
        simp [h] at h2 hhd1
        obtain ⟨tl2, htl2, hret2⟩ := h2
        simp [←hret1, ←hret2, attrsAccessorsAgree]; constructor
        · simp [← hhd1, attrAccessorAgrees]
        · apply (ih tl1 tl2 htl1 htl2)

theorem memberAux_foldGetAttr_agrees_aux
  (accs : List AstAccessor) (attrs : List Attr)
  (req : Request) (es : Entities)
  {ieos eos : ExprOrSpecial} {headExpr aexp : Expr} :
  ieos.toExpr? = some headExpr →
  memberAux ieos accs = some eos →
  eos.toExpr? = some aexp →
  attrsAccessorsAgree accs attrs →
  evaluate aexp req es =
    (do let h ← evaluate headExpr req es
        List.foldlM (fun v a => getAttr v a es) h attrs) := by
  induction accs generalizing attrs ieos eos headExpr aexp with
  | nil =>
    intro hheadExpr hmaux haexp hagr
    cases attrs with
    | nil =>
      simp [memberAux] at hmaux
      rw [← hmaux] at haexp
      rw [hheadExpr] at haexp
      simp at haexp
      rw [← haexp]
      simp [List.foldlM]
    | cons _ _ => simp [attrsAccessorsAgree] at hagr
  | cons acc tl ih =>
    intro hheadExpr hmaux haexp hagr
    cases attrs with
    | nil => simp [attrsAccessorsAgree] at hagr
    | cons attr ttl =>
      simp [attrsAccessorsAgree] at hagr
      obtain ⟨hhead, htail⟩ := hagr
      have h_acc_toString : acc.toString = attr := by
        cases acc with
        | field id =>
          cases id <;> simp [attrAccessorAgrees] at hhead
          all_goals (simp [AstAccessor.toString, CstCommon.Ident.toString]; exact hhead)
        | index s =>
          simp [attrAccessorAgrees] at hhead
          simp [AstAccessor.toString]; exact hhead
      cases ieos with
      | expr e =>
        simp [ExprOrSpecial.toExpr?] at hheadExpr
        simp [memberAux] at hmaux
        have hnew : (ExprOrSpecial.expr (e.getAttr acc.toString)).toExpr?
                    = some (e.getAttr acc.toString) := rfl
        have ih' := ih ttl
                       (ieos := .expr (e.getAttr acc.toString))
                       (headExpr := e.getAttr acc.toString)
                       hnew hmaux haexp htail
        rw [ih', ← hheadExpr]
        simp [evaluate, h_acc_toString, List.foldlM]
      | var v =>
        simp [ExprOrSpecial.toExpr?] at hheadExpr
        cases acc with
        | field id =>
          simp [memberAux] at hmaux
          have hnew : (ExprOrSpecial.expr ((Expr.var v).getAttr (CstCommon.Ident.toString id))).toExpr?
                      = some ((Expr.var v).getAttr (CstCommon.Ident.toString id)) := rfl
          have ih' := ih ttl
                         (ieos := .expr ((Expr.var v).getAttr (CstCommon.Ident.toString id)))
                         (headExpr := (Expr.var v).getAttr (CstCommon.Ident.toString id))
                         hnew hmaux haexp htail
          rw [ih', ← hheadExpr]
          simp [AstAccessor.toString] at h_acc_toString
          simp [evaluate, h_acc_toString, List.foldlM]
        | index s =>
          simp [memberAux] at hmaux
          have hnew : (ExprOrSpecial.expr ((Expr.var v).getAttr s)).toExpr?
                      = some ((Expr.var v).getAttr s) := rfl
          have ih' := ih ttl
                         (ieos := .expr ((Expr.var v).getAttr s))
                         (headExpr := (Expr.var v).getAttr s)
                         hnew hmaux haexp htail
          rw [ih', ← hheadExpr]
          simp [AstAccessor.toString] at h_acc_toString
          simp [evaluate, h_acc_toString, List.foldlM]
      | strLit s =>
        simp [ExprOrSpecial.toExpr?, Option.bind_eq_some_iff] at hheadExpr
        obtain ⟨us, hus, hheadEq⟩ := hheadExpr
        simp [memberAux, ExprOrSpecial.toExpr?, hus] at hmaux
        have hnew : (ExprOrSpecial.expr ((Expr.lit (.string us)).getAttr acc.toString)).toExpr?
                    = some ((Expr.lit (.string us)).getAttr acc.toString) := rfl
        have ih' := ih ttl
                       (ieos := .expr ((Expr.lit (.string us)).getAttr acc.toString))
                       (headExpr := (Expr.lit (.string us)).getAttr acc.toString)
                       hnew hmaux haexp htail
        rw [ih']
        simp [evaluate, ← hheadEq, h_acc_toString, List.foldlM]
      | boolLit b =>
        simp [ExprOrSpecial.toExpr?] at hheadExpr
        simp [memberAux, ExprOrSpecial.toExpr?] at hmaux
        have hnew : (ExprOrSpecial.expr ((Expr.lit (.bool b)).getAttr acc.toString)).toExpr?
                    = some ((Expr.lit (.bool b)).getAttr acc.toString) := rfl
        have ih' := ih ttl
                       (ieos := .expr ((Expr.lit (.bool b)).getAttr acc.toString))
                       (headExpr := (Expr.lit (.bool b)).getAttr acc.toString)
                       hnew hmaux haexp htail
        rw [ih', ← hheadExpr]
        simp [evaluate, h_acc_toString, List.foldlM]
      | name n =>
        cases acc with
        | field _ => simp [memberAux] at hmaux
        | index _ => simp [memberAux] at hmaux

theorem memberAux_foldGetAttr_agrees
  (item : Cst.Primary) (head : Value)
  (accs : List AstAccessor) (attrs : List Attr)
  (req : Request) (es : Entities)
  {ieos eos : ExprOrSpecial} {headExpr aexp : Expr} :
  item.toExprOrSpecial? = some ieos →
  ieos.toExpr? = some headExpr →
  memberAux ieos accs = some eos →
  eos.toExpr? = some aexp →
  evaluate headExpr req es = item.evaluate req es →
  item.evaluate req es = .ok head →
  attrsAccessorsAgree accs attrs →
  evaluate aexp req es = List.foldlM (fun v a => getAttr v a es) head attrs := by
  intro _ hheadExpr hmaux haexp hheadEval hitemEval hagr
  rw [memberAux_foldGetAttr_agrees_aux accs attrs req es hheadExpr hmaux haexp hagr]
  rw [hheadEval, hitemEval]
  simp [bind, Except.bind]
