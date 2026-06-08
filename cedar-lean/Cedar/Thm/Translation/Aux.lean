import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Data.List.Lemmas

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

theorem attrChain?_isSome_of_mapM_toAstAccessor?
  (accs : List Cst.MemAccess) (ret : List AstAccessor) :
  accs.mapM (Cst.MemAccess.toAstAccessor?) = some ret →
  Cst.AttrChain? accs ≠ none := by
  induction accs generalizing ret with
  | nil =>
    intro _ h
    simp [Cst.AttrChain?] at h
  | cons hd tl ih =>
    intro h
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨hd_ret, hhd, tl_ret, htl, _⟩ := h
    match hd with
    | .field i =>
      cases i <;> simp [Cst.MemAccess.toAstAccessor?] at hhd
      simp only [Option.bind_eq_some_iff] at hhd
      obtain ⟨s, hs, _⟩ := hhd
      simp [Cst.AttrChain?, hs]
      intro h2
      exact ih tl_ret htl h2
    | .index e =>
      simp [Cst.MemAccess.toAstAccessor?, Option.bind_eq_some_iff] at hhd
      obtain ⟨s, hs, _⟩ := hhd
      simp [Cst.AttrChain?, hs]
      intro h2
      exact ih tl_ret htl h2

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

/- For Unary -/

theorem bangN_evaluate_error (e : Expr) (n : Nat) (req : Request) (es : Entities) (err : Error) :
  evaluate e req es = .error err →
  evaluate (e.bangN n) req es = .error err := by
  induction n generalizing e with
  | zero =>
    intro he
    rw [Expr.bangN]; simp; exact he
  | succ n ih =>
    intro he
    rw [Expr.bangN]; simp
    apply ih (.unaryApp .not e)
    simp [evaluate, he, bind, Except.bind]

theorem bangN_evaluate
  (e : Expr) (n : Nat) (req : Request) (es : Entities) (b : Bool) :
  evaluate e req es = .ok (.prim (.bool b)) →
  evaluate (e.bangN n) req es =
    if n%2 == 0 then .ok (.prim (.bool b)) else .ok (.prim (.bool !b)) := by
  intro he
  induction n generalizing e b with
  | zero => simp [Expr.bangN]; exact he
  | succ n ih =>
    rw [Expr.bangN]; simp
    have hnot : evaluate (Expr.unaryApp UnaryOp.not e) req es = .ok (.prim (.bool !b)) := by
      simp [evaluate, he, bind, Except.bind, apply₁]
    rw [ih (Expr.unaryApp UnaryOp.not e) (!b) hnot]
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · -- n even, n+1 odd
      have h1 : (n % 2 == 0) = true := by simp [hn]
      simp [h1]; omega
    · -- n odd, n+1 even
      have h1 : (n % 2 == 0) = false := by simp [hn]
      simp [h1]; omega

theorem bangN_evaluate_nonBool
  (e : Expr) (n : Nat) (req : Request) (es : Entities) (v : Value) :
  evaluate e req es = .ok v →
  (∀ b, v ≠ .prim (.bool b)) →
  n > 0 →
  evaluate (e.bangN n) req es = .error .typeError := by
  intro he hnb hpos
  cases n with
  | zero => omega
  | succ k =>
    rw [Expr.bangN]; simp
    apply bangN_evaluate_error (.unaryApp .not e) k req es .typeError
    simp [evaluate, he, bind, Except.bind]
    cases v with
    | prim p =>
      cases p with
      | bool b => exact absurd rfl (hnb b)
      | _ => simp [apply₁]
    | _ => simp [apply₁]

theorem bangN_evaluate_ok
  (e : Expr) (n : Nat) (req : Request) (es : Entities) (v : Value) :
  evaluate e req es = .ok v →
  evaluate (e.bangN n) req es = (
    if n == 0 then .ok v
    else match v with
      | .prim (.bool b) =>
        if n % 2 == 0 then .ok (.prim (.bool b)) else .ok (.prim (.bool !b))
      | _ => .error .typeError) := by
  intro hev
  cases hn : n with
  | zero =>
    simp [Expr.bangN, hev]
  | succ k =>
    cases v with
    | prim p =>
      cases p with
      | bool b =>
        rw [bangN_evaluate e (k+1) req es b hev]
        simp
      | int _ | string _ | entityUID _ =>
        rw [bangN_evaluate_nonBool e (k+1) req es _ hev
              (by intro b h; cases h) (by omega)]
        simp
    | set _ | record _ | ext _ =>
      rw [bangN_evaluate_nonBool e (k+1) req es _ hev
            (by intro b h; cases h) (by omega)]
      simp

theorem bangN_evaluate_general
  (e : Expr) (n : Nat) (req : Request) (es : Entities) :
  evaluate (e.bangN n) req es = (match evaluate e req es with
    | .error err => .error err
    | .ok v =>
      if n == 0 then .ok v
      else match v with
        | .prim (.bool b) =>
          if n % 2 == 0 then .ok (.prim (.bool b)) else .ok (.prim (.bool !b))
        | _ => .error .typeError) := by
  cases hev : evaluate e req es with
  | error err =>
    rw [bangN_evaluate_error e n req es err hev]
  | ok v =>
    rw [bangN_evaluate_ok e n req es v hev]

theorem dashN_evaluate_error (e : Expr) (n : Nat) (req : Request) (es : Entities) (err : Error) :
  evaluate e req es = .error err →
  evaluate (e.dashN n) req es = .error err := by
  induction n generalizing e with
  | zero =>
    intro he
    rw [Expr.dashN]; simp; exact he
  | succ n ih =>
    intro he
    rw [Expr.dashN]; simp
    apply ih (.unaryApp .neg e)
    simp [evaluate, he, bind, Except.bind]

theorem dashN_evaluate_nonInt
  (e : Expr) (n : Nat) (req : Request) (es : Entities) (v : Value) :
  evaluate e req es = .ok v →
  (∀ i, v ≠ .prim (.int i)) →
  n > 0 →
  evaluate (e.dashN n) req es = .error .typeError := by
  intro he hni hpos
  cases n with
  | zero => omega
  | succ k =>
    rw [Expr.dashN]; simp
    apply dashN_evaluate_error (.unaryApp .neg e) k req es .typeError
    simp [evaluate, he, bind, Except.bind]
    cases v with
    | prim p =>
      cases p with
      | int i => exact absurd rfl (hni i)
      | _ => simp [apply₁]
    | _ => simp [apply₁]

/-- Helper: `(Int64.ofInt k).toInt = k` when `k` is in the `Int64` range. -/
private theorem toInt_ofInt_of_range {k : Int} (h : Int64.MIN ≤ k ∧ k ≤ Int64.MAX) :
    (Int64.ofInt k).toInt = k := by
  have h1 : -2^63 ≤ k := by simp [Int64.MIN] at h; omega
  have h2 : k < 2^63 := by simp [Int64.MAX] at h; omega
  show BitVec.toInt (BitVec.ofInt 64 k) = k
  rw [BitVec.toInt_ofInt]
  exact Int.bmod_eq_of_le h1 h2

/-- Helper: if `Int64.ofInt? k = some v`, then `v.toInt = k`. -/
private theorem toInt_of_ofInt? {k : Int} {v : Int64}
    (h : Int64.ofInt? k = some v) : v.toInt = k := by
  have hrange : Int64.MIN ≤ k ∧ k ≤ Int64.MAX := by
    by_contra hnr
    have : Int64.ofInt? k = none := by
      apply Int64.ofInt?_none_iff.mp
      by_cases hlo : Int64.MIN ≤ k
      · right; by_contra hhi; apply hnr; exact ⟨hlo, by omega⟩
      · left; omega
    rw [this] at h; cases h
  have hsome : Int64.ofInt? k = some (Int64.ofInt k) := Int64.ofInt?_some_iff.mp hrange
  rw [hsome] at h; injection h with hv
  rw [← hv]
  exact toInt_ofInt_of_range hrange

/-- Double negation on `Int64`: if `i.neg? = some j` then `j.neg? = some i`. -/
theorem Int64.neg?_neg? {i j : Int64} :
    i.neg? = some j → j.neg? = some i := by
  intro h
  rw [Int64.neg?] at h
  have hj : j.toInt = -i.toInt := toInt_of_ofInt? h
  rw [Int64.neg?, hj]
  rw [show -(-i.toInt) = i.toInt from by omega]
  exact Int64.ofInt?_toInt i

/-- `dashN` on an int. Note: when `i = Int64.MIN` (so `i.neg? = none`), the
    AST iterates `apply₁ .neg` and errors on the first step — regardless of
    whether the total count is even or odd. So the `i.neg? = none` arm here
    short-circuits *before* the parity check. -/
theorem dashN_evaluate_int
  (e : Expr) (n : Nat) (req : Request) (es : Entities) (i : Int64) :
  evaluate e req es = .ok (.prim (.int i)) →
  evaluate (e.dashN n) req es =
    (if n == 0 then .ok (.prim (.int i))
     else match i.neg? with
       | none => .error .arithBoundsError
       | some j =>
           if n % 2 == 0 then .ok (.prim (.int i))
           else .ok (.prim (.int j))) := by
  intro he
  induction n generalizing e i with
  | zero => simp [Expr.dashN]; exact he
  | succ n ih =>
    rw [Expr.dashN]; simp
    cases hneg : i.neg? with
    | none =>
      have hev_err : evaluate (Expr.unaryApp UnaryOp.neg e) req es = .error .arithBoundsError := by
        simp [evaluate, he, bind, Except.bind, apply₁, intOrErr, hneg]
      rw [dashN_evaluate_error (Expr.unaryApp UnaryOp.neg e) n req es .arithBoundsError hev_err]
    | some j =>
      have hev_ok : evaluate (Expr.unaryApp UnaryOp.neg e) req es = .ok (.prim (.int j)) := by
        simp [evaluate, he, bind, Except.bind, apply₁, intOrErr, hneg]
      rw [ih (.unaryApp .neg e) j hev_ok]
      have hjneg : j.neg? = some i := Int64.neg?_neg? hneg
      rw [hjneg]
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn
      · -- n even ⇒ n+1 odd
        have h1 : (n % 2 == 0) = true := by simp [hn]
        have h2 : (n + 1) % 2 ≠ 0 := by simp [Nat.add_mod, hn]
        simp [h1, h2]
      · -- n odd ⇒ n+1 even
        have h1 : (n % 2 == 0) = false := by simp [hn]
        have h2 : (n + 1) % 2 = 0 := by simp [Nat.add_mod, hn]
        have h3 : n ≠ 0 := by intro h; rw [h] at hn; simp at hn
        simp [h1, h2, h3]

theorem dashN_evaluate_ok
  (e : Expr) (n : Nat) (req : Request) (es : Entities) (v : Value) :
  evaluate e req es = .ok v →
  evaluate (e.dashN n) req es = (
    if n == 0 then .ok v
    else match v with
      | .prim (.int i) =>
          match i.neg? with
          | none => .error .arithBoundsError
          | some j =>
              if n % 2 == 0 then .ok (.prim (.int i))
              else .ok (.prim (.int j))
      | _ => .error .typeError) := by
  intro hev
  cases hn : n with
  | zero => simp [Expr.dashN, hev]
  | succ k =>
    cases v with
    | prim p =>
      cases p with
      | int i =>
        rw [dashN_evaluate_int e (k+1) req es i hev]
      | bool _ | string _ | entityUID _ =>
        rw [dashN_evaluate_nonInt e (k+1) req es _ hev
              (by intro i h; cases h) (by omega)]
        simp
    | set _ | record _ | ext _ =>
      rw [dashN_evaluate_nonInt e (k+1) req es _ hev
            (by intro i h; cases h) (by omega)]
      simp

/-- Fully-unified `dashN` evaluation. NOTE: the CST evaluator's non-`liNum`
    `nDash` arm in `CstSemantics.lean` will need to validate `i.neg?` *before*
    the parity shortcut to match this spec — otherwise it diverges on
    `Int64.MIN` inputs with even count. -/
theorem dashN_evaluate_general
  (e : Expr) (n : Nat) (req : Request) (es : Entities) :
  evaluate (e.dashN n) req es = (match evaluate e req es with
    | .error err => .error err
    | .ok v =>
      if n == 0 then .ok v
      else match v with
        | .prim (.int i) =>
            match i.neg? with
            | none => .error .arithBoundsError
            | some j =>
                if n % 2 == 0 then .ok (.prim (.int i))
                else .ok (.prim (.int j))
        | _ => .error .typeError) := by
  cases hev : evaluate e req es with
  | error err =>
    rw [dashN_evaluate_error e n req es err hev]
  | ok v =>
    rw [dashN_evaluate_ok e n req es v hev]

/- For Relation -/

/-- The AST expression `constructExprRel op e₁ e₂` evaluates to the same `.ok`
    output as `Cst.applyRelOp op v₁ v₂ es`, when `e₁` evaluates to `v₁` and
    `e₂` evaluates to `v₂`. -/
theorem constructExprRel_applyRelOp_agrees
    (op : Cst.RelOp) (e₁ e₂ : Expr) (req : Request) (es : Entities)
    (v₁ v₂ : Value) :
    evaluate e₁ req es = .ok v₁ →
    evaluate e₂ req es = .ok v₂ →
    ∀ v, evaluate (constructExprRel op e₁ e₂) req es = .ok v ↔
         Cst.applyRelOp op v₁ v₂ es = .ok v := by
  intro he₁ he₂ v
  cases op <;>
    simp [constructExprRel, Cst.applyRelOp, evaluate, he₁, he₂,
          bind, Except.bind]

/-- Collapse the `String ⊕ List String` shape from the translator's `toHasRhs?`
    into a flat `List String`, treating `.inl f` as the singleton `[f]`. -/
def hasRhsToList : String ⊕ List String → List String
  | .inl f => [f]
  | .inr fs => fs

/-- Helper: `fieldChain?` and `constructAttrsAux?` are the same function
    (both filter via `toUnreservedId?`/`toUnreservedString?` on `.field` accessors,
    rejecting `.index`). -/
theorem fieldChain?_eq_constructAttrsAux?
    (xs : List Cst.MemAccess) :
    Cst.fieldChain? xs = constructAttrsAux? xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | field id =>
      simp [Cst.fieldChain?, constructAttrsAux?, ih]
      rfl
    | index e =>
      simp [Cst.fieldChain?, constructAttrsAux?]

/-- For the `rHas` case: `Cst.AddExpr.toHasRhs?` (translation) and `Cst.AddExpr.toAttrs?`
    (evaluation) produce identical attribute lists when collapsed via `hasRhsToList`.

    With the evaluator strengthened to use `toUnreservedId?` (mismatch 2) and
    `unescape?` (mismatch 3), the only structural difference is the `Sum` vs `List`
    output type, which `hasRhsToList` bridges. -/
theorem addExpr_toHasRhs_toAttrs_agrees
    {e : Cst.AddExpr} {rhs : String ⊕ List String} :
    e.toHasRhs? = some rhs →
    e.toAttrs? = some (hasRhsToList rhs) := by
  intro hrhs
  simp [Cst.AddExpr.toHasRhs?] at hrhs
  obtain ⟨⟨⟨he, hm⟩, hu⟩, hbody⟩ := hrhs
  simp [Cst.AddExpr.toAttrs?, he, hm, hu]
  match hmi : e.initial.initial.item.item with
  | .literal lit =>
    rw [hmi] at hbody
    cases lit with
    | liTrue =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at hbody
    | liFalse =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at hbody
    | liNum n =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
            Option.bind_eq_some_iff] at hbody
      obtain ⟨a, ⟨_, _, ha⟩, hmatch⟩ := hbody
      rw [← ha] at hmatch
      simp at hmatch
    | liStr s =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at hbody
      cases haccess : e.initial.initial.item.access with
      | nil =>
        rw [haccess] at hbody
        simp at hbody
        cases hunesc : Cedar.Spec.CstCommon.unescape? s with
        | none => rw [hunesc] at hbody; simp at hbody
        | some s' =>
          rw [hunesc] at hbody
          simp at hbody
          rw [← hbody]
          simp [hasRhsToList, Cst.fieldChain?, hunesc]
      | cons hd tl =>
        rw [haccess] at hbody
        cases hd with
        | field id => simp at hbody
        | index e' => simp at hbody
  | .name n =>
    rw [hmi] at hbody
    simp [Cst.Primary.toExprOrSpecial?] at hbody
    obtain ⟨np, nname⟩ := n
    cases hvar : (Cst.Name.toVar? ⟨np, nname⟩) with
    | some v =>
      rw [hvar] at hbody
      simp [Option.map_eq_some_iff] at hbody
      obtain ⟨attrs, hattrs, hrhsEq⟩ := hbody
      have hagree := Cst.Name.toVar?_agrees hvar
      have hpath : np = [] := hagree.1
      have hname := hagree.2
      simp [constructAttrs?, Option.bind_eq_some_iff] at hattrs
      obtain ⟨tail, htail, hattrsEq⟩ := hattrs
      subst hpath
      cases v with
      | principal =>
        simp at hname; subst hname
        simp [fieldChain?_eq_constructAttrsAux?, htail]
        rw [← hrhsEq]
        simp [hasRhsToList, ← hattrsEq, Cst.Ident.toHasHead?, Var.toString]
      | action =>
        simp at hname; subst hname
        simp [fieldChain?_eq_constructAttrsAux?, htail]
        rw [← hrhsEq]
        simp [hasRhsToList, ← hattrsEq, Cst.Ident.toHasHead?, Var.toString]
      | resource =>
        simp at hname; subst hname
        simp [fieldChain?_eq_constructAttrsAux?, htail]
        rw [← hrhsEq]
        simp [hasRhsToList, ← hattrsEq, Cst.Ident.toHasHead?, Var.toString]
      | context =>
        simp at hname; subst hname
        simp [fieldChain?_eq_constructAttrsAux?, htail]
        rw [← hrhsEq]
        simp [hasRhsToList, ← hattrsEq, Cst.Ident.toHasHead?, Var.toString]
    | none =>
      rw [hvar] at hbody
      cases han : (⟨np, nname⟩ : Cst.Name).toAName? with
      | none => rw [han] at hbody; simp at hbody
      | some an =>
        rw [han] at hbody
        simp [Option.bind_eq_some_iff, Option.map_eq_some_iff] at hbody
        obtain ⟨hp, first, hfirst, attrs, hattrs, hrhseq⟩ := hbody
        have han_eq := Cst.Name.toAName?_agrees han
        have hnpath : np = [] := by
          rw [han_eq] at hp; simp at hp; exact hp
        subst hnpath
        rw [han_eq] at hfirst
        simp at hfirst
        cases hname : nname with
        | idIdent s =>
          rw [hname] at hfirst
          simp [CstCommon.Ident.toString] at hfirst
          have hs_eq_and_unreserved : s = first ∧ Cedar.Spec.CstCommon.Unreserved? s = true := by
            simp [String.toUnreservedId?, Cedar.Spec.CstCommon.Unreserved?] at hfirst ⊢
            split at hfirst <;> rename_i heq
            all_goals (simp_all)
          obtain ⟨hs_first, hs_unreserved⟩ := hs_eq_and_unreserved
          simp [constructAttrs?, Option.bind_eq_some_iff] at hattrs
          obtain ⟨tail, htail, hattrs_eq2⟩ := hattrs
          simp [fieldChain?_eq_constructAttrsAux?, htail]
          rw [← hrhseq]
          simp [hasRhsToList, Cst.Ident.toHasHead?, hs_unreserved,
                ← hs_first, ← hattrs_eq2]
        | idPrincipal | idAction | idResource | idContext
        | idTrue | idFalse | idPermit | idForbid
        | idWhen | idUnless | idIn | idHas | idLike | idIs
        | idIf | idThen | idElse =>
          rw [hname] at hfirst
          simp [CstCommon.Ident.toString, String.toUnreservedId?] at hfirst
  | .ref r =>
    rw [hmi] at hbody; simp at hbody
  | .expr e' =>
    rw [hmi] at hbody; simp at hbody
  | .eList es' =>
    rw [hmi] at hbody; simp at hbody

/-- Helper: `constructAttrs?` always returns a non-empty list when it succeeds. -/
theorem constructAttrs?_nonempty
    {first : String} {rest : List Cst.MemAccess} {result : List String} :
    constructAttrs? first rest = some result → result ≠ [] := by
  intro h
  simp [constructAttrs?, Option.bind_eq_some_iff] at h
  obtain ⟨tail, _, hresult⟩ := h
  simp [← hresult]

/-- `toAttrs?` always produces a non-empty list when it succeeds: the result is
    either `[unescaped_lit]` or `head :: fields`. -/
theorem toAttrs?_nonempty {e : Cst.AddExpr} {fs : List Attr} :
    e.toAttrs? = some fs → fs ≠ [] := by
  intro hattrs
  simp only [Cst.AddExpr.toAttrs?] at hattrs
  split at hattrs; · simp at hattrs
  split at hattrs; · simp at hattrs
  split at hattrs; · simp at hattrs
  split at hattrs; · simp at hattrs
  split at hattrs
  · split at hattrs
    · simp [Option.map_eq_some_iff] at hattrs
      obtain ⟨_, _, hattrs⟩ := hattrs; rw [← hattrs]; simp
    · simp at hattrs
  · simp at hattrs
  · split at hattrs
    · simp at hattrs; rw [← hattrs]; simp
    · simp at hattrs
  · simp at hattrs
  · simp at hattrs

/-- Non-emptiness: `toHasRhs?` always produces a non-empty list when collapsed.
    Used to discharge the evaluator's `some []` arm as vacuous. -/
theorem hasRhsToList_nonempty {rhs : String ⊕ List String}
    {e : Cst.AddExpr} :
    e.toHasRhs? = some rhs →
    hasRhsToList rhs ≠ [] := by
  intro hrhs
  -- The collapsed list `hasRhsToList rhs` equals `e.toAttrs?`, which is always
  -- non-empty by `toAttrs?_nonempty`.
  have hattrs := addExpr_toHasRhs_toAttrs_agrees hrhs
  exact toAttrs?_nonempty hattrs

/-- `hasAttr` always returns a Bool-valued `Value` on success. -/
private theorem hasAttr_isBool {v : Value} {a : Attr} {es : Entities} {r : Value} :
    hasAttr v a es = .ok r → ∃ b, r = .prim (.bool b) := by
  intro h
  simp [hasAttr, bind, Except.bind] at h
  split at h
  case h_1 => simp at h
  all_goals (injection h with hr; rw [← hr]; exact ⟨_, rfl⟩)

/-- `rHasChain` always returns a Bool-valued `Value` on success. -/
private theorem rHasChain_isBool
    (v : Value) (a : Attr) (as : List Attr) (es : Entities) :
    ∀ r, Cst.rHasChain v a as es = .ok r → ∃ b, r = .prim (.bool b) := by
  induction as generalizing v a with
  | nil =>
    intro r h
    simp [Cst.rHasChain] at h
    exact hasAttr_isBool h
  | cons b bs ih =>
    intro r h
    simp [Cst.rHasChain, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i hv
      obtain ⟨b'', hb''⟩ := hasAttr_isBool hv
      rw [hb''] at h
      split at h
      · simp at h; rw [← h]; exact ⟨false, rfl⟩
      · split at h
        · simp at h
        · exact ih _ _ _ h

/-- The AST expression `extendedHasAttr target (a :: as)` evaluates the same as
    the evaluator's `rHasChain v a as`, when `target` evaluates to value `v`. -/
theorem extendedHasAttr_evaluate_agrees
    (target : Expr) (a : Attr) (as : List Attr) (req : Request) (es : Entities) (v : Value) :
    evaluate target req es = .ok v →
    evaluate (extendedHasAttr target (a :: as)) req es = Cst.rHasChain v a as es := by
  intro htarget
  induction as generalizing target a v with
  | nil =>
    simp [extendedHasAttr, evaluate, htarget, bind, Except.bind, Cst.rHasChain]
  | cons b bs ih =>
    cases hh : hasAttr v a es with
    | error err =>
      simp [extendedHasAttr, evaluate, htarget, bind, Except.bind, hh,
            Result.as, Cst.rHasChain]
    | ok hv =>
      obtain ⟨b', hb'⟩ := hasAttr_isBool hh
      subst hb'
      cases b' with
      | false =>
        simp [extendedHasAttr, evaluate, htarget, bind, Except.bind, hh,
              Result.as, Coe.coe, Value.asBool, Cst.rHasChain]
      | true =>
        cases hga : getAttr v a es with
        | error err =>
          have hgetAttr : evaluate (.getAttr target a) req es = .error err := by
            simp [evaluate, htarget, bind, Except.bind, hga]
          cases bs with
          | nil =>
            simp [extendedHasAttr, evaluate, htarget, hgetAttr, bind, Except.bind,
                  hh, hga, Result.as, Coe.coe, Value.asBool, Cst.rHasChain]
          | cons c cs =>
            simp [extendedHasAttr, evaluate, htarget, hgetAttr, bind, Except.bind,
                  hh, hga, Result.as, Coe.coe, Value.asBool, Cst.rHasChain]
        | ok v' =>
          have hgetAttr : evaluate (.getAttr target a) req es = .ok v' := by
            simp [evaluate, htarget, bind, Except.bind, hga]
          have ih' := ih (target := .getAttr target a) (a := b) (v := v') hgetAttr
          simp [extendedHasAttr, evaluate, htarget, bind, Except.bind, hh, hga,
                Result.as, Coe.coe, Value.asBool, Cst.rHasChain]
          rw [ih']
          cases hrhc : Cst.rHasChain v' b bs es with
          | error err => simp
          | ok rv =>
            obtain ⟨b'', hb''⟩ := rHasChain_isBool v' b bs es rv hrhc
            subst hb''
            rfl

/-- Helper: when `memberAux` takes an `.expr ...` input, it always returns
    either `.expr ...` or `none` — never another `ExprOrSpecial` constructor. -/
private theorem memberAux_expr_returns_expr
    (e : Expr) (accs : List AstAccessor) (ret : ExprOrSpecial) :
    memberAux (.expr e) accs = some ret →
    ∃ e', ret = .expr e' := by
  induction accs generalizing e ret with
  | nil =>
    intro h; simp [memberAux] at h; exact ⟨e, h.symm⟩
  | cons acc rest ih =>
    intro h; simp [memberAux] at h; exact ih _ _ h

/-- Helper: `memberAux ieos accs = some (.strLit lit)` requires `accs = []`
    and `ieos = .strLit lit`.  Everything else either fails or routes through
    an `.expr ...` recursion. -/
private theorem memberAux_eq_strLit
    {ieos : ExprOrSpecial} {accs : List AstAccessor} {lit : String} :
    memberAux ieos accs = some (.strLit lit) →
    accs = [] ∧ ieos = .strLit lit := by
  intro h
  cases accs with
  | nil =>
    simp [memberAux] at h
    refine ⟨rfl, ?_⟩; rw [← h]
  | cons acc rest =>
    exfalso
    cases ieos with
    | expr _ =>
      simp [memberAux] at h
      obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h; cases hcontra
    | var _ =>
      cases acc <;> (simp [memberAux] at h
                     obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h
                     cases hcontra)
    | strLit _ =>
      simp [memberAux, ExprOrSpecial.toExpr?, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h; cases hcontra
    | boolLit _ =>
      simp [memberAux, ExprOrSpecial.toExpr?] at h
      obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h; cases hcontra
    | name _ => cases acc <;> simp [memberAux] at h

/-- Helper: `Cst.Primary.toExprOrSpecial? p = some (.strLit lit)` iff
    `p = .literal (.liStr lit)`. -/
private theorem primary_toExprOrSpecial_strLit
    {p : Cst.Primary} {lit : String} :
    p.toExprOrSpecial? = some (.strLit lit) →
    p = .literal (.liStr lit) := by
  intro h
  cases p with
  | literal lit' =>
    cases lit' with
    | liStr s =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at h
      rw [h]
    | liTrue | liFalse =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at h
    | liNum _ =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
            Option.bind_eq_some_iff] at h
  | name _ =>
    simp [Cst.Primary.toExprOrSpecial?] at h
    split at h
    · simp at h
    · simp [Option.bind_eq_some_iff] at h
  | ref r =>
    cases r with
    | uid _ eid =>
      cases eid with
      | string _ =>
        simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?,
              Option.bind_eq_some_iff] at h
    | ref _ _ =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?] at h
  | expr _ =>
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at h
  | eList _ =>
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at h

/-- Helper: `Cst.Member.toExprOrSpecial? m = some (.strLit lit)` iff
    `m.access = []` and `m.item = .literal (.liStr lit)`. -/
private theorem member_toExprOrSpecial_strLit
    {m : Cst.Member} {lit : String} :
    m.toExprOrSpecial? = some (.strLit lit) →
    m.access = [] ∧ m.item = .literal (.liStr lit) := by
  intro h
  simp [Cst.Member.toExprOrSpecial?, Option.bind_eq_some_iff] at h
  obtain ⟨ieos, hieos, accs, haccs, hmaux⟩ := h
  obtain ⟨hAccs, hIeos⟩ := memberAux_eq_strLit hmaux
  subst hAccs
  refine ⟨?_, primary_toExprOrSpecial_strLit (hIeos ▸ hieos)⟩
  cases hAcc : m.access with
  | nil => rfl
  | cons _ _ =>
    rw [hAcc] at haccs
    simp [List.mapM_cons, Option.bind_eq_some_iff] at haccs

/-- For the `rLike` case: if the translator's `toPattern?` succeeds with `p`,
    then the evaluator's `toPatternString?` succeeds with some `s` such that
    `CstCommon.toPattern? s = some p`.

    Both functions enforce the same shape (extended/op/access empty, item is
    a `liStr`) and call `CstCommon.toPattern?` on the same raw string. -/
theorem addExpr_toPattern_toPatternString_agrees
    {e : Cst.AddExpr} {p : Pattern} :
    Cst.AddExpr.toPattern? e = some p →
    ∃ s, Cst.AddExpr.toPatternString? e = some s ∧
         Cedar.Spec.CstCommon.toPattern? s = some p := by
  intro h
  simp [Cst.AddExpr.toPattern?, Option.bind_eq_some_iff] at h
  obtain ⟨eos, heos, hmatch⟩ := h
  -- For the inner match to succeed, eos must be .strLit lit.
  cases eos with
  | expr _ | var _ | name _ | boolLit _ => simp at hmatch
  | strLit lit =>
    simp at hmatch
    refine ⟨lit, ?_, hmatch⟩
    -- Trace `e.toExprOrSpecial? = some (.strLit lit)` through the chain.
    -- The chain delegates to the underlying member only when extended/mext
    -- are empty AND op is `none` or `.nDash 0`.
    obtain ⟨⟨⟨op, member⟩, mext⟩, ext⟩ := e
    simp [Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
          Cst.Unary.toExprOrSpecial?] at heos
    -- ext = [] required; otherwise produces .expr.
    cases ext with
    | cons _ _ =>
      simp [Option.bind_eq_some_iff] at heos
    | nil =>
      simp at heos
      cases mext with
      | cons _ _ =>
        simp [Option.bind_eq_some_iff] at heos
      | nil =>
        simp at heos
        -- Now the unary's match on `op` runs. Show op ∈ {none, .nDash 0}.
        cases op with
        | none =>
          obtain ⟨hAccNil, hItem⟩ := member_toExprOrSpecial_strLit heos
          simp [Cst.AddExpr.toPatternString?, hAccNil, hItem]
        | some op' =>
          cases op' with
          | nDash n =>
            by_cases hn : n = 0
            · subst hn
              obtain ⟨hAccNil, hItem⟩ := member_toExprOrSpecial_strLit heos
              simp [Cst.AddExpr.toPatternString?, hAccNil, hItem]
            · simp at heos
              -- For non-zero n, falls into the toLit?/eos chain producing .expr/none.
              split at heos
              · split at heos
                · simp at heos
                · split at heos
                  · simp at heos
                  · simp at heos
                · simp at heos
              · simp [Option.bind_eq_some_iff] at heos
          | nBang _ =>
            simp [Option.bind_eq_some_iff] at heos
          | nOverBang | nOverDash => simp at heos

/-- Helper: `memberAux ieos accs = some (.name an)` requires `accs = []`
    and `ieos = .name an`. -/
private theorem memberAux_eq_name
    {ieos : ExprOrSpecial} {accs : List AstAccessor} {an : Spec.Name} :
    memberAux ieos accs = some (.name an) →
    accs = [] ∧ ieos = .name an := by
  intro h
  cases accs with
  | nil =>
    simp [memberAux] at h
    refine ⟨rfl, ?_⟩; rw [← h]
  | cons acc rest =>
    exfalso
    cases ieos with
    | expr _ =>
      simp [memberAux] at h
      obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h; cases hcontra
    | var _ =>
      cases acc <;> (simp [memberAux] at h
                     obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h
                     cases hcontra)
    | strLit _ =>
      simp [memberAux, ExprOrSpecial.toExpr?, Option.bind_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h; cases hcontra
    | boolLit _ =>
      simp [memberAux, ExprOrSpecial.toExpr?] at h
      obtain ⟨_, hcontra⟩ := memberAux_expr_returns_expr _ _ _ h; cases hcontra
    | name _ => cases acc <;> simp [memberAux] at h

/-- Helper: `Cst.Primary.toExprOrSpecial? p = some (.name an)` requires `p` to
    be a `.name n` with `n.toAName? = some an`. -/
private theorem primary_toExprOrSpecial_name
    {p : Cst.Primary} {an : Spec.Name} :
    p.toExprOrSpecial? = some (.name an) →
    ∃ n, p = .name n ∧ n.toAName? = some an := by
  intro h
  cases p with
  | literal lit' =>
    cases lit' with
    | liStr s =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at h
    | liTrue | liFalse =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?] at h
    | liNum _ =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
            Option.bind_eq_some_iff] at h
  | name n =>
    have hdef : Cst.Primary.toExprOrSpecial? (.name n) =
      (match n.toVar? with
       | some v => some (ExprOrSpecial.var v)
       | none => n.toAName?.map ExprOrSpecial.name) := by
      simp [Cst.Primary.toExprOrSpecial?]
      cases n.toVar? with
      | some v => rfl
      | none =>
        simp [Option.bind, Option.map]
        cases n.toAName? with
        | none => rfl
        | some a => rfl
    rw [hdef] at h
    cases hv : n.toVar? with
    | some v => simp [hv] at h
    | none =>
      simp [hv, Option.map] at h
      cases hname : n.toAName? with
      | none => simp [hname] at h
      | some a => simp [hname] at h; exact ⟨n, rfl, h ▸ hname⟩
  | ref r =>
    cases r with
    | uid _ eid =>
      cases eid with
      | string _ =>
        simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?,
              Option.bind_eq_some_iff] at h
    | ref _ _ =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?] at h
  | expr _ =>
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at h
  | eList _ =>
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_some_iff] at h

/-- Helper: `Cst.Member.toExprOrSpecial? m = some (.name an)` requires
    `m.access = []` and `m.item = .name n` with `n.toAName? = some an`. -/
private theorem member_toExprOrSpecial_name
    {m : Cst.Member} {an : Spec.Name} :
    m.toExprOrSpecial? = some (.name an) →
    m.access = [] ∧ ∃ n, m.item = .name n ∧ n.toAName? = some an := by
  intro h
  simp [Cst.Member.toExprOrSpecial?, Option.bind_eq_some_iff] at h
  obtain ⟨ieos, hieos, accs, haccs, hmaux⟩ := h
  obtain ⟨hAccs, hIeos⟩ := memberAux_eq_name hmaux
  subst hAccs
  obtain ⟨n, hItem, hAName⟩ := primary_toExprOrSpecial_name (hIeos ▸ hieos)
  refine ⟨?_, n, hItem, hAName⟩
  cases hAcc : m.access with
  | nil => rfl
  | cons _ _ =>
    rw [hAcc] at haccs
    simp [List.mapM_cons, Option.bind_eq_some_iff] at haccs

/-- For the `rIsIn` case: when the translator's `toEntityType?` succeeds with
    `et`, the evaluator's structural `toEntityTypeName?` succeeds with the same
    `et`.  Both enforce the same shape (extended/mext empty, op `none` or
    `.nDash 0`, access empty, item a `.name`); the translator additionally
    requires the name be non-reserved, and on those names `toAName?` produces
    exactly the `toString`-based name the evaluator builds. -/
theorem addExpr_toEntityType_agrees
    {e : Cst.AddExpr} {et : EntityType} :
    Cst.AddExpr.toEntityType? e = some et →
    Cst.AddExpr.toEntityTypeName? e = some et := by
  intro h
  simp [Cst.AddExpr.toEntityType?, Option.bind_eq_some_iff] at h
  obtain ⟨eos, heos, hmatch⟩ := h
  cases eos with
  | expr _ | var _ | boolLit _ | strLit _ => simp at hmatch
  | name an =>
    simp at hmatch
    subst hmatch
    obtain ⟨⟨⟨op, member⟩, mext⟩, ext⟩ := e
    simp [Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
          Cst.Unary.toExprOrSpecial?] at heos
    cases ext with
    | cons _ _ => simp [Option.bind_eq_some_iff] at heos
    | nil =>
      simp at heos
      cases mext with
      | cons _ _ => simp [Option.bind_eq_some_iff] at heos
      | nil =>
        simp at heos
        cases op with
        | none =>
          obtain ⟨hAccNil, n, hItem, hAName⟩ := member_toExprOrSpecial_name heos
          have hagree := Cst.Name.toAName?_agrees hAName
          simp [Cst.AddExpr.toEntityTypeName?, hAccNil, hItem, hagree]
        | some op' =>
          cases op' with
          | nDash k =>
            by_cases hk : k = 0
            · subst hk
              obtain ⟨hAccNil, n, hItem, hAName⟩ := member_toExprOrSpecial_name heos
              have hagree := Cst.Name.toAName?_agrees hAName
              simp [Cst.AddExpr.toEntityTypeName?, hAccNil, hItem, hagree]
            · simp at heos
              split at heos
              · split at heos
                · simp at heos
                · split at heos <;> simp at heos
                · simp at heos
              · simp [Option.bind_eq_some_iff] at heos
          | nBang _ => simp [Option.bind_eq_some_iff] at heos
          | nOverBang | nOverDash => simp at heos

/-- `apply₂ .mem` only ever yields a boolean value (or an error), so its result
    survives the `.as Bool` coercion the translated `.and` applies to it. -/
theorem apply₂_mem_returns_bool {v₁ v₂ : Value} {es : Entities} {r : Value} :
    apply₂ BinaryOp.mem v₁ v₂ es = .ok r → ∃ b : Bool, r = .prim (.bool b) := by
  intro h
  simp only [apply₂] at h
  split at h <;> simp_all only [reduceCtorEq, Except.ok.injEq, inₛ, bind, Except.bind]
  · exact ⟨_, h.symm⟩
  · split at h
    · simp at h
    · simp only [Except.ok.injEq] at h; exact ⟨_, h.symm⟩

/-- For the `rIsIn` case with `inEntity = some ie`: the translated AST
    `(is et target) && (target in ie)` agrees with the CST evaluation. Takes the
    target/inEntity bridging iffs as hypotheses so the mutual recursion stays in
    the main proof. -/
theorem rIsIn_some_eval_agrees
    {target ety ie : Cst.AddExpr} {mt mi : Expr} {et : EntityType}
    {req : Request} {es : Entities}
    (hEtyName : ety.toEntityTypeName? = some et)
    (htarget_iff : ∀ v, evaluate mt req es = .ok v ↔ target.evaluate req es = .ok v)
    (hinEntity_iff : ∀ v, evaluate mi req es = .ok v ↔ ie.evaluate req es = .ok v) :
    ∀ v, evaluate (Expr.and (.unaryApp (.is et) mt) (.binaryApp .mem mt mi)) req es = .ok v ↔
         (Cst.Relation.rIsIn target ety (some ie)).evaluate req es = .ok v := by
  intro v
  simp only [Cst.Relation.evaluate, hEtyName, evaluate]
  cases htgt : evaluate mt req es with
  | error e =>
    cases htgtC : target.evaluate req es with
    | ok vt => exact absurd ((htarget_iff vt).mpr htgtC) (by rw [htgt]; simp)
    | error e' => simp [bind, Except.bind, Result.as]
  | ok vt =>
    have htgtC : target.evaluate req es = .ok vt := (htarget_iff vt).mp htgt
    simp only [htgtC, bind, Except.bind]
    cases hIs : apply₁ (.is et) vt with
    | error e => simp [Result.as]
    | ok isVal =>
      cases isVal with
      | prim p =>
        cases p with
        | bool b =>
          cases b with
          | false => simp [Result.as, Coe.coe, Value.asBool]
          | true =>
            simp only [Result.as, Coe.coe, Value.asBool, Bool.not_true,
                       Bool.false_eq_true, if_false]
            cases hie : evaluate mi req es with
            | error e =>
              cases hieC : ie.evaluate req es with
              | ok vi => exact absurd ((hinEntity_iff vi).mpr hieC) (by rw [hie]; simp)
              | error e' => simp []
            | ok v₂ =>
              have hieC : ie.evaluate req es = .ok v₂ := (hinEntity_iff v₂).mp hie
              simp only [hieC]
              cases hmem : apply₂ .mem vt v₂ es with
              | error e => simp []
              | ok memv =>
                have ⟨b', hb'⟩ := apply₂_mem_returns_bool hmem
                subst hb'
                simp [pure, Except.pure]
        | int _ | string _ | entityUID _ => simp [Result.as, Coe.coe, Value.asBool]
      | set _ | record _ | ext _ => simp [Result.as, Coe.coe, Value.asBool]

/- For AndExpr -/

/-- `foldOps` short-circuits on `.bool false`: it ignores `rest` and returns
    `.ok (.bool false)`. -/
theorem andExprFoldOps_false_short_circuits
    (req : Request) (es : Entities) (rest : List Cst.Relation) :
    Cst.AndExpr.foldOps (.prim (.bool false)) rest req es = .ok (.prim (.bool false)) := by
  cases rest with
  | nil => simp [Cst.AndExpr.foldOps]
  | cons _ _ => simp [Cst.AndExpr.foldOps, Value.asBool, bind, Except.bind]

/-- Bridge one fold step: `evaluate (Expr.and acc_ast rhs)` followed by
    `foldOps ... rest` matches `foldOps acc_v (rel :: rest)`. -/
theorem expr_and_eval_eq_foldOps_step
    (req : Request) (es : Entities)
    (acc_ast rhs : Expr) (acc_v : Value) (rel : Cst.Relation)
    (rest : List Cst.Relation) :
    evaluate acc_ast req es = .ok acc_v →
    (∀ vp, evaluate rhs req es = .ok vp ↔ rel.evaluate req es = .ok vp) →
    ∀ v,
      (do let v' ← evaluate (Expr.and acc_ast rhs) req es
          Cst.AndExpr.foldOps v' rest req es) = .ok v ↔
      Cst.AndExpr.foldOps acc_v (rel :: rest) req es = .ok v := by
  intro hacc hrel_iff v
  simp [Cst.AndExpr.foldOps, evaluate, hacc, bind, Except.bind, Result.as, Coe.coe]
  cases hAccBool : acc_v.asBool with
  | error _ => simp
  | ok bAcc =>
    cases bAcc with
    | false =>
      simp
      rw [andExprFoldOps_false_short_circuits]
      exact ⟨fun h => by injection h, fun h => by rw [← h]⟩
    | true =>
      simp
      cases h_rhs : evaluate rhs req es with
      | error err =>
        cases h_rel : rel.evaluate req es with
        | ok rv =>
          have := (hrel_iff rv).mpr h_rel
          rw [this] at h_rhs; cases h_rhs
        | error err' => simp
      | ok rv =>
        have h_rel_ok : rel.evaluate req es = .ok rv := (hrel_iff rv).mp h_rhs
        rw [h_rel_ok]
        cases rv with
        | prim p =>
          cases p with
          | bool _ => simp [Value.asBool, pure, Except.pure]
          | int _ | string _ | entityUID _ => simp [Value.asBool]
        | set _ | record _ | ext _ => simp [Value.asBool]

/- For OrExpr -/

/-- `foldOps` short-circuits on `.bool true`: it ignores `rest` and returns
    `.ok (.bool true)`. -/
theorem orExprFoldOps_true_short_circuits
    (req : Request) (es : Entities) (rest : List Cst.AndExpr) :
    Cst.OrExpr.foldOps (.prim (.bool true)) rest req es = .ok (.prim (.bool true)) := by
  cases rest with
  | nil => simp [Cst.OrExpr.foldOps]
  | cons _ _ => simp [Cst.OrExpr.foldOps, Value.asBool, bind, Except.bind]

/-- Bridge one fold step: `evaluate (Expr.or acc_ast rhs)` followed by
    `foldOps ... rest` matches `foldOps acc_v (ande :: rest)`. -/
theorem expr_or_eval_eq_foldOps_step
    (req : Request) (es : Entities)
    (acc_ast rhs : Expr) (acc_v : Value) (ande : Cst.AndExpr)
    (rest : List Cst.AndExpr) :
    evaluate acc_ast req es = .ok acc_v →
    (∀ vp, evaluate rhs req es = .ok vp ↔ ande.evaluate req es = .ok vp) →
    ∀ v,
      (do let v' ← evaluate (Expr.or acc_ast rhs) req es
          Cst.OrExpr.foldOps v' rest req es) = .ok v ↔
      Cst.OrExpr.foldOps acc_v (ande :: rest) req es = .ok v := by
  intro hacc hrel_iff v
  simp [Cst.OrExpr.foldOps, evaluate, hacc, bind, Except.bind, Result.as, Coe.coe]
  cases hAccBool : acc_v.asBool with
  | error _ => simp
  | ok bAcc =>
    cases bAcc with
    | true =>
      simp
      rw [orExprFoldOps_true_short_circuits]
      exact ⟨fun h => by injection h, fun h => by rw [← h]⟩
    | false =>
      simp
      cases h_rhs : evaluate rhs req es with
      | error err =>
        cases h_rel : ande.evaluate req es with
        | ok rv =>
          have := (hrel_iff rv).mpr h_rel
          rw [this] at h_rhs; cases h_rhs
        | error err' => simp
      | ok rv =>
        have h_rel_ok : ande.evaluate req es = .ok rv := (hrel_iff rv).mp h_rhs
        rw [h_rel_ok]
        cases rv with
        | prim p =>
          cases p with
          | bool _ => simp [Value.asBool, pure, Except.pure]
          | int _ | string _ | entityUID _ => simp [Value.asBool]
        | set _ | record _ | ext _ => simp [Value.asBool]

/- For Primary's eList case -/

/-- Generic element-wise bridge: when each element of `xs` translates to an AST
    expression and the per-element iff holds, then evaluating the translated
    list element-wise agrees with evaluating the original list element-wise.
    The signature uses `.val` form to match `List.mapM₁_eq_mapM`. -/
theorem mapM_eval_agrees
    (req : Request) (es : Entities) :
    ∀ (xs : List Cst.Expr) (aes : List Expr),
      xs.mapM₁ (fun x => x.val.toAExpr?) = some aes →
      (∀ x ∈ xs, ∀ ax,
        x.toAExpr? = some ax →
        ∀ v, evaluate ax req es = .ok v ↔ x.evaluate req es = .ok v) →
      ∀ vs, aes.mapM (fun a => evaluate a req es) = .ok vs ↔
            xs.mapM (fun x => x.evaluate req es) = .ok vs := by
  intro xs aes htrans hperElt vs
  rw [List.mapM₁_eq_mapM (fun (x : Cst.Expr) => x.toAExpr?)] at htrans
  induction xs generalizing aes vs with
  | nil =>
    simp [List.mapM_nil] at htrans
    subst htrans
    simp [List.mapM_nil]
  | cons hd tl ih =>
    simp [List.mapM_cons, Option.bind_eq_some_iff] at htrans
    obtain ⟨ahd, hahd, atl, hatl, haes⟩ := htrans
    subst haes
    have hhd_iff : ∀ vp, evaluate ahd req es = .ok vp ↔ hd.evaluate req es = .ok vp :=
      hperElt hd List.mem_cons_self ahd hahd
    have htl_perElt : ∀ x ∈ tl, ∀ ax,
        x.toAExpr? = some ax →
        ∀ v, evaluate ax req es = .ok v ↔ x.evaluate req es = .ok v := by
      intro x hx ax hax v
      exact hperElt x (List.mem_cons_of_mem _ hx) ax hax v
    have ih' := ih atl hatl htl_perElt
    simp [List.mapM_cons, bind, Except.bind]
    cases hev_ahd : evaluate ahd req es with
    | error err =>
      cases hev_hd : hd.evaluate req es with
      | ok vp =>
        have := (hhd_iff vp).mpr hev_hd
        rw [this] at hev_ahd; cases hev_ahd
      | error _ => simp
    | ok ahdv =>
      have hev_hd : hd.evaluate req es = .ok ahdv := (hhd_iff ahdv).mp hev_ahd
      rw [hev_hd]
      simp
      cases hev_atl : atl.mapM (fun a => evaluate a req es) with
      | error err =>
        cases hev_tl : tl.mapM (fun x => x.evaluate req es) with
        | ok vstl =>
          have := (ih' vstl).mpr hev_tl
          rw [this] at hev_atl; cases hev_atl
        | error _ => simp
      | ok atlvs =>
        have hev_tl : tl.mapM (fun x => x.evaluate req es) = .ok atlvs :=
          (ih' atlvs).mp hev_atl
        rw [hev_tl]

/- Lifting round-trips and entity-UID translation agreement -/

/-- Lifting a CST expr to a `Relation` and translating round-trips. -/
theorem toRelation_toAExpr (e : Cst.Expr) :
    (Cst.Expr.toRelation e).toAExpr? = e.toAExpr? := by
  simp [Cst.Expr.toRelation, Cst.Expr.toPrimary, Cst.Primary.toMember,
    Cst.Member.toUnary, Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toRelation,
    Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?,
    Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
    Cst.Primary.toExprOrSpecial?, memberAux, ExprOrSpecial.toExpr?, Cst.Expr.toAExpr?,
    Option.bind_assoc]

/-- Lifting a CST expr to an `AddExpr` and translating round-trips. -/
theorem toAddExpr_toAExpr (e : Cst.Expr) :
    (Cst.Expr.toAddExpr e).toAExpr? = e.toAExpr? := by
  simp [Cst.Expr.toAddExpr, Cst.Expr.toPrimary, Cst.Primary.toMember,
    Cst.Member.toUnary, Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr,
    Cst.AddExpr.toAExpr?, Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
    Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?, Cst.Primary.toExprOrSpecial?,
    memberAux, ExprOrSpecial.toExpr?, Cst.Expr.toAExpr?, Option.bind_assoc]

/- The entity-UID extractor agrees with the AST translation on the produced
    expression: a `Primary`/`Expr` that `toMultipleEntityUID?` reads as a single
    UID (or list of UIDs) translates (via `toAExpr?`) to the corresponding entity
    literal (or set of entity literals). -/
def memToExpr : EntityUID ⊕ List EntityUID → Expr
  | .inl uid  => .lit (.entityUID uid)
  | .inr uids => .set (uids.map (fun u => .lit (.entityUID u)))

mutual
theorem prim_mem_toAExpr {p : Cst.Primary} {r : EntityUID ⊕ List EntityUID} :
    p.toMultipleEntityUID? = some r → p.toAExpr? = some (memToExpr r) := by
  intro h
  cases p with
  | literal _ => simp [Cst.Primary.toMultipleEntityUID?] at h
  | name _ => simp [Cst.Primary.toMultipleEntityUID?] at h
  | ref rf =>
    cases rf with
    | uid path eid =>
      cases eid with
      | string s =>
        simp [Cst.Primary.toMultipleEntityUID?, Option.bind_eq_some_iff] at h
        obtain ⟨p', hp', eid', heid', heq⟩ := h
        subst heq
        simp [Cst.Primary.toAExpr?, Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?,
          hp', heid', ExprOrSpecial.toExpr?, memToExpr]
    | ref _ _ => simp [Cst.Primary.toMultipleEntityUID?] at h
  | expr e' =>
    simp only [Cst.Primary.toMultipleEntityUID?] at h
    have hih := expr_mem_toAExpr h
    simp [Cst.Primary.toAExpr?, Cst.Primary.toExprOrSpecial?, ExprOrSpecial.toExpr?,
      Cst.Expr.toAExpr?, Option.bind_assoc] at hih ⊢
    exact hih
  | eList es =>
    simp [Cst.Primary.toMultipleEntityUID?, Option.bind_eq_some_iff] at h
    obtain ⟨uids, huids, heq⟩ := h
    subst heq
    have hlist := list_mem_toAExpr huids
    unfold Cst.Primary.toAExpr? Cst.Primary.toExprOrSpecial?
    rw [List.mapM₁_eq_mapM (fun x : Cst.Expr => x.toAExpr?), hlist]
    simp [ExprOrSpecial.toExpr?, memToExpr]
termination_by (sizeOf p, 0)
decreasing_by all_goals (simp_wf; first | assumption | decreasing_tactic)

theorem expr_mem_toAExpr {e : Cst.Expr} {r : EntityUID ⊕ List EntityUID} :
    e.toMultipleEntityUID? = some r → e.toAExpr? = some (memToExpr r) := by
  intro h
  match he : e with
  | .expr ⟨.edIf _ _ _⟩ => simp [Cst.Expr.toMultipleEntityUID?] at h
  | .expr ⟨.edOr o⟩ =>
    simp only [Cst.Expr.toMultipleEntityUID?] at h
    split at h
    · simp at h
    · rename_i hc1
      split at h <;> try simp at h
      rename_i ae ext heq
      simp at hc1
      obtain ⟨hoext, hoiext⟩ := hc1
      obtain ⟨⟨⟨⟨⟨hext, haeext⟩, hmext⟩, hop⟩, hacc⟩, hinner⟩ := h
      have hsz : sizeOf ae.initial.initial.item.item < sizeOf e := by
        have h1 := sizeOf_addExpr_primary_lt_orExpr o ae ext heq
        have h2 : sizeOf o < sizeOf e := by rw [he]; decreasing_tactic
        exact Nat.lt_trans h1 h2
      have hih := prim_mem_toAExpr hinner
      simp [Cst.Expr.toAExpr?, Cst.Expr.toExprOrSpecial?, Cst.ExprImpl.toExprOrSpecial?,
        Cst.ExprData.toExprOrSpecial?, Cst.OrExpr.toExprOrSpecial?, hoext, hoiext, heq,
        Cst.AndExpr.toExprOrSpecial?, Cst.Relation.toExprOrSpecial?, hext,
        Cst.AddExpr.toExprOrSpecial?, haeext, Cst.MultExpr.toExprOrSpecial?, hmext,
        Cst.Unary.toExprOrSpecial?, hop, Cst.Member.toExprOrSpecial?, hacc, memberAux,
        Cst.Primary.toAExpr?] at hih ⊢
      exact hih
termination_by (sizeOf e, 1)
decreasing_by all_goals (simp_wf; first | assumption | decreasing_tactic)

theorem list_mem_toAExpr {es : List Cst.Expr} {uids : List EntityUID} :
    es.mapM (fun x => match x.toMultipleEntityUID? with | some (.inl e) => some e | _ => none) = some uids →
    es.mapM (fun x => x.toAExpr?) = some (uids.map (fun u => Expr.lit (.entityUID u))) := by
  intro h
  cases es with
  | nil => simp_all
  | cons x xs =>
    rw [List.mapM_cons] at h
    simp [Option.bind_eq_some_iff] at h
    obtain ⟨eref, href, restU, hrest, rfl⟩ := h
    have hxm : x.toMultipleEntityUID? = some (.inl eref) := by
      cases hx : x.toMultipleEntityUID? with
      | none => rw [hx] at href; simp at href
      | some rr =>
        cases rr with
        | inl e => rw [hx] at href; simp at href; subst href; rfl
        | inr _ => rw [hx] at href; simp at href
    have hxa := expr_mem_toAExpr hxm
    have hxsa := list_mem_toAExpr hrest
    simp [List.mapM_cons, hxa, hxsa, memToExpr]
termination_by (sizeOf es, 2)
decreasing_by all_goals (simp_wf; first | assumption | decreasing_tactic)
end

/- Forward translation helpers (used by the policy-translation soundness proof) -/

/-- `toEntityUID?` agrees with the AST translation on the produced literal. -/
theorem toEntityUID_toAExpr {e : Cst.Expr} {uid : EntityUID} :
    e.toEntityUID? = some uid → e.toAExpr? = some (.lit (.entityUID uid)) := by
  intro h
  simp [Cst.Expr.toEntityUID?, Option.bind_eq_some_iff] at h
  obtain ⟨erefs, herefs, hmatch⟩ := h
  cases erefs with
  | inl eref => simp only [Option.some.injEq] at hmatch; subst hmatch; exact expr_mem_toAExpr herefs
  | inr _ => simp at hmatch

/-- `Cst.Expr.not` translates to an AST `.not`. -/
theorem cond_not_toAExpr {e : Cst.Expr} {b : Expr} :
    e.toAExpr? = some b → (Cst.Expr.not e).toAExpr? = some (Expr.unaryApp .not b) := by
  intro h
  simp [Cst.Expr.not, Cst.Expr.toPrimary, Cst.Primary.toMember,
    Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toRelation, Cst.Relation.toAndExpr,
    Cst.AndExpr.toOrExpr, Cst.OrExpr.toExpr, Cst.Expr.toAExpr?, Cst.Expr.toExprOrSpecial?,
    Cst.ExprImpl.toExprOrSpecial?, Cst.ExprData.toExprOrSpecial?, Cst.OrExpr.toExprOrSpecial?,
    Cst.AndExpr.toExprOrSpecial?, Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?,
    Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
    Cst.Primary.toExprOrSpecial?, memberAux, Expr.bangN, ExprOrSpecial.toExpr?, h]

/-- If both halves of an append `mapM`-translate, so does the whole list. -/
theorem mapM_append_isSome {α β : Type} {f : α → Option β} :
    ∀ {l1 l2 : List α},
    (∃ r1, l1.mapM f = some r1) → (∃ r2, l2.mapM f = some r2) →
    ∃ r, (l1 ++ l2).mapM f = some r := by
  intro l1 l2 h1 h2
  obtain ⟨r1, hr1⟩ := h1
  obtain ⟨r2, hr2⟩ := h2
  induction l1 generalizing r1 with
  | nil =>
    simp only [List.nil_append]
    exact ⟨r2, hr2⟩
  | cons hd tl ih =>
    simp [List.mapM_cons, Option.bind_eq_some_iff] at hr1
    obtain ⟨b, hb, rest, hrest, _⟩ := hr1
    obtain ⟨r, hr⟩ := ih rest hrest
    refine ⟨b :: r, ?_⟩
    rw [List.cons_append]
    simp [List.mapM_cons, hb, hr]

/-- Collapsing a single-relation `AndExpr` through the translation chain. -/
theorem andExpr_single_collapse (r : Cst.Relation) :
    ({initial := r, extended := []} : Cst.AndExpr).toOrExpr.toExpr.toAExpr? = r.toAExpr? := by
  simp [Cst.AndExpr.toOrExpr, Cst.OrExpr.toExpr, Cst.Expr.toAExpr?, Cst.Expr.toExprOrSpecial?,
    Cst.ExprImpl.toExprOrSpecial?, Cst.ExprData.toExprOrSpecial?, Cst.OrExpr.toExprOrSpecial?,
    Cst.AndExpr.toExprOrSpecial?, Cst.Relation.toAExpr?]

/-- Forward leaf translation for principal/resource scope variables: when
    `toPRScope?` succeeds and the variable translates to an `Expr.var`, the
    variable definition's expression translates to AST. -/
theorem toPRScope_leaf_isSome {vd : Cst.VariableDef} {scope : Scope} {v : Var}
    (hv : (vd.var.varToAddExpr).toExprOrSpecial? = some (ExprOrSpecial.var v))
    (hscope : vd.toPRScope? = some scope) :
    ∃ leaf, vd.toExpr.toAExpr? = some leaf := by
  have hv2 : (vd.var.varToAddExpr).toAExpr? = some (Expr.var v) := by
    simp [Cst.AddExpr.toAExpr?, hv, ExprOrSpecial.toExpr?]
  obtain ⟨var, et, ineq⟩ := vd
  simp only [Cst.VariableDef.toExpr, Cst.VariableDef.toAndExpr]
  match ineq, et, hscope with
  | none, none, hscope =>
    rw [andExpr_single_collapse]
    simp [Cst.Relation.tt, Cst.Primary.toMember, Cst.Member.toUnary, Cst.Unary.toMultExpr,
      Cst.MultExpr.toAddExpr, Cst.AddExpr.toRelation, Cst.Relation.toAExpr?,
      Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
      Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?, Cst.Primary.toExprOrSpecial?,
      Cst.Literal.toExprOrSpecial?, memberAux, ExprOrSpecial.toExpr?]
  | none, some t, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨ety, hety, _⟩ := hscope
    rw [andExpr_single_collapse]
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv2, hety,
      ExprOrSpecial.toExpr?]
  | some (.rEq, e), none, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨uid, huid, _⟩ := hscope
    rw [andExpr_single_collapse]
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, constructExprRel,
      toAddExpr_toAExpr, toEntityUID_toAExpr huid, ExprOrSpecial.toExpr?]
  | some (.rIn, e), none, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨uid, huid, _⟩ := hscope
    rw [andExpr_single_collapse]
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, constructExprRel,
      toAddExpr_toAExpr, toEntityUID_toAExpr huid, ExprOrSpecial.toExpr?]
  | some (.rIn, e), some t, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨uid, huid, ety, hety, _⟩ := hscope
    rw [andExpr_single_collapse]
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv2, hety,
      toAddExpr_toAExpr, toEntityUID_toAExpr huid, ExprOrSpecial.toExpr?]
  | some (.rEq, e), some t, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rLess, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rLessEq, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rGreater, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rGreaterEq, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rNotEq, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope

/-- Forward leaf translation for the action scope variable. -/
theorem action_leaf_isSome {va : Cst.VariableDef} {as : ActionScope}
    (has : va.toActionScope? = some as) :
    ∃ leaf, va.toExpr.toAExpr? = some leaf := by
  obtain ⟨var, et, ineq⟩ := va
  simp only [Cst.VariableDef.toExpr, Cst.VariableDef.toAndExpr]
  cases var
  case idAction =>
    have hv : (Cst.Ident.idAction.varToAddExpr).toExprOrSpecial? = some (ExprOrSpecial.var .action) := by
      simp [Cst.Ident.varToAddExpr, Cst.Primary.toMember, Cst.Member.toUnary, Cst.Unary.toMultExpr,
        Cst.MultExpr.toAddExpr, Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
        Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?, Cst.Primary.toExprOrSpecial?,
        Cst.Name.toVar?, memberAux]
    have hv2 : (Cst.Ident.idAction.varToAddExpr).toAExpr? = some (Expr.var .action) := by
      simp [Cst.AddExpr.toAExpr?, hv, ExprOrSpecial.toExpr?]
    cases et
    case some t =>
      simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?] at has
    case none =>
      cases ineq with
      | none =>
        rw [andExpr_single_collapse]
        simp [Cst.Relation.tt, Cst.Primary.toMember, Cst.Member.toUnary, Cst.Unary.toMultExpr,
          Cst.MultExpr.toAddExpr, Cst.AddExpr.toRelation, Cst.Relation.toAExpr?,
          Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
          Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?, Cst.Primary.toExprOrSpecial?,
          Cst.Literal.toExprOrSpecial?, memberAux, ExprOrSpecial.toExpr?]
      | some opE =>
        obtain ⟨op, e⟩ := opE
        cases op with
        | rEq =>
          cases huid : e.toEntityUID? with
          | none => simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?, huid] at has
          | some uid =>
            rw [andExpr_single_collapse]
            simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, constructExprRel,
              toAddExpr_toAExpr, toEntityUID_toAExpr huid, ExprOrSpecial.toExpr?]
        | rIn =>
          cases hr : e.toMultipleEntityUID? with
          | none => simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?,
              Cst.Expr.toEntityUIDs?, hr] at has
          | some r =>
            have hmem := expr_mem_toAExpr hr
            rw [andExpr_single_collapse]
            simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, constructExprRel,
              toAddExpr_toAExpr, hmem, ExprOrSpecial.toExpr?]
        | rLess => simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?] at has
        | rLessEq => simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?] at has
        | rGreater => simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?] at has
        | rGreaterEq => simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?] at has
        | rNotEq => simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?] at has
  all_goals simp [Cst.VariableDef.toActionScope?, Cst.VariableDef.toActionScopeAux?] at has

/-- Forward leaf translation for a condition. -/
theorem cond_leaf_isSome {c : Cst.Cond} {cond : Condition}
    (hcond : c.toCondition? = some cond) :
    ∃ leaf, (Cst.Cond.toExpr c).toAExpr? = some leaf := by
  obtain ⟨ccond, cexpr⟩ := c
  cases ccond <;> cases cexpr <;>
    simp_all [Cst.Cond.toCondition?, Cst.Ident.toConditionKind?, Cst.Cond.toExpr,
      Option.bind_eq_some_iff]
  case idWhen.some e =>
    obtain ⟨body, hbody, _⟩ := hcond
    exact ⟨body, hbody⟩
  case idUnless.some e =>
    obtain ⟨body, hbody, _⟩ := hcond
    exact ⟨_, cond_not_toAExpr hbody⟩

/-- Principal-scope variable translates. -/
theorem principal_leaf_isSome {vp : Cst.VariableDef} {ps : PrincipalScope}
    (hps : vp.toPrincipalScope? = some ps) :
    ∃ leaf, vp.toExpr.toAExpr? = some leaf := by
  simp only [Cst.VariableDef.toPrincipalScope?] at hps
  split at hps <;> [skip; simp at hps]
  rename_i hvar
  simp [Option.bind_eq_some_iff] at hps
  obtain ⟨scope, hscope, _⟩ := hps
  have hv : (vp.var.varToAddExpr).toExprOrSpecial? = some (ExprOrSpecial.var .principal) := by
    rw [hvar]; simp [Cst.Ident.varToAddExpr, Cst.Primary.toMember, Cst.Member.toUnary,
      Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toExprOrSpecial?,
      Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
      Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?, memberAux]
  exact toPRScope_leaf_isSome hv hscope

/-- Resource-scope variable translates. -/
theorem resource_leaf_isSome {vr : Cst.VariableDef} {rs : ResourceScope}
    (hrs : vr.toResourceScope? = some rs) :
    ∃ leaf, vr.toExpr.toAExpr? = some leaf := by
  simp only [Cst.VariableDef.toResourceScope?] at hrs
  split at hrs <;> [skip; simp at hrs]
  rename_i hvar
  simp [Option.bind_eq_some_iff] at hrs
  obtain ⟨scope, hscope, _⟩ := hrs
  have hv : (vr.var.varToAddExpr).toExprOrSpecial? = some (ExprOrSpecial.var .resource) := by
    rw [hvar]; simp [Cst.Ident.varToAddExpr, Cst.Primary.toMember, Cst.Member.toUnary,
      Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toExprOrSpecial?,
      Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
      Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?, memberAux]
  exact toPRScope_leaf_isSome hv hscope

/-- All condition leaves translate when `toConditions?` succeeds. -/
theorem conds_mapM_toAExpr_isSome {conds : List Cst.Cond} {acconds : Conditions}
    (h : conds.mapM (·.toCondition?) = some acconds) :
    ∃ r, (conds.map Cst.Cond.toExpr).mapM Cst.Expr.toAExpr? = some r := by
  induction conds generalizing acconds with
  | nil => exact ⟨[], by simp⟩
  | cons hd tl ih =>
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨c0, hc0, crest, hcrest, _⟩ := h
    obtain ⟨leaf, hleaf⟩ := cond_leaf_isSome hc0
    obtain ⟨r, hr⟩ := ih hcrest
    refine ⟨leaf :: r, ?_⟩
    rw [List.map_cons, List.mapM_cons]
    simp [hleaf, hr]

/- Helpers for the policy-list translation soundness proof -/

/-- `toPolicy?` always produces a policy whose `id` field is empty. -/
theorem toPolicy?_id_empty {cp : Cst.Policy} {ap : Spec.Policy} :
    cp.toPolicy? = some ap → ap.id = "" := by
  intro h
  obtain ⟨p⟩ := cp
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨eff, heff, ⟨ps, as, rs⟩, hsc, conds, hconds, heq⟩ := h
  rw [← heq]

/-- `filterMap` congruence across two lists related pointwise. -/
theorem filterMap_congr_forall₂ {α β γ : Type} {f : α → Option γ} {g : β → Option γ}
    {R : α → β → Prop} {xs : List α} {ys : List β} :
    List.Forall₂ R xs ys → (∀ a b, R a b → f a = g b) →
    xs.filterMap f = ys.filterMap g := by
  intro h hfg
  induction h with
  | nil => rfl
  | cons hhd htl ih =>
    rename_i a b xs' ys'
    simp only [List.filterMap, hfg _ _ hhd, ih]

/-- Index-generalized consistency: zipping `policy{k+i}` ids onto the CST policies
    is pointwise related to id-stamping the translated AST policies. This is the
    structural bridge between `Cst.Policies.withIDs` and `Cst.Policies.toPolicies?`. -/
theorem withIDs_toPolicies_aux :
    ∀ (k : Nat) (ps : List Cst.Policy) (rets : List Spec.Policy),
    ps.mapM Cst.Policy.toPolicy? = some rets →
    List.Forall₂ (fun (pr : PolicyID × Cst.Policy) (ap : Spec.Policy) =>
        pr.1 = ap.id ∧ pr.2.toPolicy? = some {ap with id := ""})
      (List.zip ((List.range' k ps.length).map (fun i => s!"policy{i}")) ps)
      (rets.mapIdx (fun i p => {p with id := s!"policy{k+i}"})) := by
  intro k ps
  induction ps generalizing k with
  | nil =>
    intro rets hrets
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at hrets
    subst hrets
    simp
  | cons hd tl ih =>
    intro rets hrets
    simp [List.mapM_cons, Option.bind_eq_some_iff] at hrets
    obtain ⟨a0, ha0, restRets, hrest, hretseq⟩ := hrets
    subst hretseq
    rw [List.length_cons, List.range'_succ, List.map_cons, List.zip_cons_cons,
      List.mapIdx_cons]
    apply List.Forall₂.cons
    · refine ⟨by simp, ?_⟩
      rw [ha0]
      have hid := toPolicy?_id_empty ha0
      obtain ⟨id, e, pp, aa, rr, cc⟩ := a0
      subst hid
      rfl
    · have hfun : (fun (i : Nat) (p : Spec.Policy) => ({p with id := s!"policy{k + (i + 1)}"} : Spec.Policy))
                = (fun i p => {p with id := s!"policy{(k + 1) + i}"}) := by
        funext i p
        have : k + (i + 1) = (k + 1) + i := by omega
        rw [this]
      rw [hfun]
      exact ih (k + 1) restRets hrest

/-- `Cst.Policies.withIDs` generates a list of `(id, policy)` pairs that is
    pointwise consistent with `Cst.Policies.toPolicies?`: each id matches the
    stamped AST policy's id, and each CST policy translates to that AST policy
    (modulo the id field). -/
theorem withIDs_toPolicies_forall₂ {cps : Cst.Policies} {aps : Spec.Policies} :
    cps.toPolicies? = some aps →
    List.Forall₂ (fun (pr : PolicyID × Cst.Policy) (ap : Spec.Policy) =>
        pr.1 = ap.id ∧ pr.2.toPolicy? = some {ap with id := ""})
      cps.withIDs aps := by
  intro htrans
  simp only [Cst.Policies.toPolicies?, bind, Option.bind_eq_some_iff, Option.some.injEq] at htrans
  obtain ⟨rets, hrets, hapeq⟩ := htrans
  have haux := withIDs_toPolicies_aux 0 cps.ps rets hrets
  have hfun : (fun (i : Nat) (p : Spec.Policy) => ({p with id := s!"policy{0 + i}"} : Spec.Policy))
            = (fun i p => {p with id := s!"policy{i}"}) := by
    funext i p
    have : 0 + i = i := by omega
    rw [this]
  rw [hfun, ← List.range_eq_range'] at haux
  rw [← hapeq]
  exact haux
