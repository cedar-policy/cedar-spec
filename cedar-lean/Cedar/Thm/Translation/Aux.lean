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
