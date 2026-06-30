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
  cases i <;> intro h <;>
    simp_all [Cst.Ident.toUnrestrictedString?, CstCommon.Ident.toUnrestrictedString?,
      CstCommon.Ident.toString]

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
  simp [Cst.Name.toAName?, CstCommon.Name.toAName?, Option.bind_eq_some_iff] at h
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
    | call args =>
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
        | call args => simp at hbody
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
  | .rInits r =>
    rw [hmi] at hbody; simp at hbody

/-- `fieldChain?` returns the empty list only for an empty access list. -/
theorem fieldChain?_eq_nil {access : List Cst.MemAccess} :
    Cst.fieldChain? access = some [] → access = [] := by
  intro h
  cases access with
  | nil => rfl
  | cons hd tl =>
    cases hd with
    | field id =>
      simp [Cst.fieldChain?, Option.bind_eq_some_iff] at h
    | index _ => simp [Cst.fieldChain?] at h
    | call _ => simp [Cst.fieldChain?] at h

/-- Converse direction (eval ⟹ translate) for `rHas`: if the evaluator's
    `toAttrs?` succeeds, then the translator's `toHasRhs?` also succeeds.  Both
    accept exactly the same bare field-chain shapes: the evaluator was
    strengthened to use `toHasHead?`/`toUnreservedId?`/`unescape?`, and
    `fieldChain? = constructAttrsAux?`. -/
theorem addExpr_toAttrs_toHasRhs {e : Cst.AddExpr} {attrs : List Attr} :
    e.toAttrs? = some attrs →
    ∃ rhs, e.toHasRhs? = some rhs := by
  intro h
  obtain ⟨⟨⟨op, ⟨prim, access⟩⟩, mext⟩, ext⟩ := e
  simp only [Cst.AddExpr.toAttrs?] at h
  cases ext with
  | cons _ _ => simp at h
  | nil =>
    cases mext with
    | cons _ _ => simp at h
    | nil =>
      cases op with
      | some o => simp at h
      | none =>
        cases hfc : Cst.fieldChain? access with
        | none => rw [hfc] at h; simp at h
        | some fields =>
          rw [hfc] at h
          have hcaeq : constructAttrsAux? access = some fields := by
            rw [← fieldChain?_eq_constructAttrsAux?]; exact hfc
          cases prim with
          | literal lit =>
            cases lit with
            | liStr s =>
              cases hfe : fields.isEmpty with
              | false => simp [hfe] at h
              | true =>
                have hfields : fields = [] := by simpa using hfe
                have hacc : access = [] := fieldChain?_eq_nil (hfields ▸ hfc)
                subst hacc
                cases hun : Cedar.Spec.CstCommon.unescape? s with
                | none => simp [hfe, hun] at h
                | some s' =>
                  exact ⟨.inl s', by
                    simp [Cst.AddExpr.toHasRhs?, Cst.Primary.toExprOrSpecial?,
                          Cst.Literal.toExprOrSpecial?, hun]⟩
            | liTrue | liFalse | liNum _ => simp at h
          | name n =>
            obtain ⟨np, nname⟩ := n
            cases np with
            | cons _ _ => simp at h
            | nil =>
              cases hhh : Cst.Ident.toHasHead? nname with
              | none => simp [hhh] at h
              | some idStr =>
                cases nname with
                | idPrincipal =>
                  exact ⟨.inr ("principal" :: fields), by
                    simp [Cst.AddExpr.toHasRhs?, Cst.Primary.toExprOrSpecial?,
                          Cst.Name.toVar?, Var.toString, constructAttrs?, hcaeq]⟩
                | idAction =>
                  exact ⟨.inr ("action" :: fields), by
                    simp [Cst.AddExpr.toHasRhs?, Cst.Primary.toExprOrSpecial?,
                          Cst.Name.toVar?, Var.toString, constructAttrs?, hcaeq]⟩
                | idResource =>
                  exact ⟨.inr ("resource" :: fields), by
                    simp [Cst.AddExpr.toHasRhs?, Cst.Primary.toExprOrSpecial?,
                          Cst.Name.toVar?, Var.toString, constructAttrs?, hcaeq]⟩
                | idContext =>
                  exact ⟨.inr ("context" :: fields), by
                    simp [Cst.AddExpr.toHasRhs?, Cst.Primary.toExprOrSpecial?,
                          Cst.Name.toVar?, Var.toString, constructAttrs?, hcaeq]⟩
                | idIdent s =>
                  simp only [Cst.Ident.toHasHead?] at hhh
                  split at hhh
                  · rename_i hunres
                    have htus : String.toUnreservedId? s = some s := by
                      simp only [String.toUnreservedId?]
                      simp only [Cedar.Spec.CstCommon.Unreserved?] at hunres
                      split <;> simp_all
                    refine ⟨.inr (s :: fields), ?_⟩
                    simp [Cst.AddExpr.toHasRhs?, Cst.Primary.toExprOrSpecial?,
                          Cst.Name.toVar?, Cst.Name.toAName?,
                          CstCommon.Name.toAName?,
                          CstCommon.Ident.toUnrestrictedString?,
                          htus, constructAttrs?, hcaeq]
                  · simp at hhh
                | idTrue | idFalse | idPermit | idForbid | idWhen | idUnless
                | idIn | idHas | idLike | idIs | idIf | idThen | idElse =>
                  simp [Cst.Ident.toHasHead?] at hhh
          | ref _ | expr _ | eList _ | rInits _ => simp at h
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

/-- Reduction: with no accessors, `memberAux` returns the head unchanged. -/
theorem memberAux_nil (ieos : ExprOrSpecial) :
    memberAux ieos [] = some ieos := rfl

/-- Reduction: feeding an `.expr e` head through `memberAux` is the same as
    running `memberAuxB` on `e` and wrapping the result back up as an `.expr`. -/
private theorem memberAux_expr_eq (e : Expr) (accs : List AstAccessor) :
    memberAux (.expr e) accs = (memberAuxB e accs).bind (fun r => some (.expr r)) := by
  cases accs with
  | nil => rfl
  | cons acc rest => rfl

/-- Helper: when `memberAux` takes an `.expr ...` input, it always returns
    either `.expr ...` or `none` — never another `ExprOrSpecial` constructor. -/
private theorem memberAux_expr_returns_expr
    (e : Expr) (accs : List AstAccessor) (ret : ExprOrSpecial) :
    memberAux (.expr e) accs = some ret →
    ∃ e', ret = .expr e' := by
  intro h
  rw [memberAux_expr_eq] at h
  simp only [Option.bind_eq_some_iff] at h
  obtain ⟨e', _, hret⟩ := h
  exact ⟨e', (Option.some.inj hret).symm⟩

/-- On a non-empty accessor list, `memberAuxA` never returns `.inl` — the
    `.inl` (pass-through) result only arises for the empty accessor list. -/
private theorem memberAuxA_cons_ne_inl
    (ieos : ExprOrSpecial) (acc : AstAccessor) (rest : List AstAccessor) (eos : ExprOrSpecial) :
    memberAuxA ieos (acc :: rest) ≠ some (.inl eos) := by
  intro h
  cases ieos <;> cases acc <;>
    (try (cases rest <;> (try (rename_i a2 _; cases a2)))) <;>
    simp_all [memberAuxA, ExprOrSpecial.toExpr?, Option.bind_eq_some_iff]

/-- If `memberAux` succeeds, either there were no accessors (and the result is
    the unchanged head) or the result is an `.expr`. -/
theorem memberAux_some_cases {ieos r : ExprOrSpecial} {accs : List AstAccessor} :
    memberAux ieos accs = some r →
    (accs = [] ∧ r = ieos) ∨ (∃ e, r = .expr e) := by
  cases accs with
  | nil =>
    intro h
    rw [memberAux_nil] at h
    exact Or.inl ⟨rfl, (Option.some.inj h).symm⟩
  | cons acc rest =>
    intro h
    refine Or.inr ?_
    cases hA : memberAuxA ieos (acc :: rest) with
    | none => simp [memberAux, hA] at h
    | some reta =>
      cases reta with
      | inl eos => exact absurd hA (memberAuxA_cons_ne_inl ieos acc rest eos)
      | inr p =>
        obtain ⟨e, rest'⟩ := p
        simp [memberAux, hA, Option.bind_eq_some_iff] at h
        obtain ⟨ret, _, hr⟩ := h
        subst hr
        exact ⟨ret, rfl⟩

/-- Helper: `memberAux ieos accs = some (.strLit lit)` requires `accs = []`
    and `ieos = .strLit lit`. -/
private theorem memberAux_eq_strLit
    {ieos : ExprOrSpecial} {accs : List AstAccessor} {lit : String} :
    memberAux ieos accs = some (.strLit lit) →
    accs = [] ∧ ieos = .strLit lit := by
  intro h
  rcases memberAux_some_cases h with ⟨haccs, hr⟩ | ⟨_, hr⟩
  · exact ⟨haccs, hr.symm⟩
  · exact absurd hr (by simp)

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
  | rInits _ =>
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

/-- Converse direction (eval ⟹ translate) for `rLike`: if the evaluator's
    `toPatternString?` succeeds with `s`, then the AddExpr translates to the
    string-literal special form `.strLit s`.  Both functions accept exactly the
    bare string-literal shape (extended/op/access empty, item a `liStr`). -/
theorem addExpr_toPatternString_toExprOrSpecial {e : Cst.AddExpr} {s : String} :
    Cst.AddExpr.toPatternString? e = some s →
    e.toExprOrSpecial? = some (.strLit s) := by
  intro h
  obtain ⟨⟨⟨op, ⟨prim, access⟩⟩, mext⟩, ext⟩ := e
  simp only [Cst.AddExpr.toPatternString?] at h
  cases ext with
  | cons _ _ => simp at h
  | nil =>
    cases mext with
    | cons _ _ => simp at h
    | nil =>
      cases op with
      | none =>
        cases access with
        | cons _ _ => simp at h
        | nil =>
          cases prim with
          | literal lit =>
            cases lit with
            | liStr str =>
              simp at h; subst h
              simp [Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
                    Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
                    Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
                    memberAux, memberAuxA, List.mapM_nil]
            | liTrue | liFalse | liNum _ => simp at h
          | ref _ | name _ | expr _ | eList _ | rInits _ => simp at h
      | some o =>
        cases o with
        | nDash n =>
          by_cases hn : n = 0
          · subst hn
            cases access with
            | cons _ _ => simp at h
            | nil =>
              cases prim with
              | literal lit =>
                cases lit with
                | liStr str =>
                  simp at h; subst h
                  simp [Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
                        Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
                        Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
                        memberAux, memberAuxA, List.mapM_nil]
                | liTrue | liFalse | liNum _ => simp at h
              | ref _ | name _ | expr _ | eList _ | rInits _ => simp at h
          · simp [hn] at h
        | nBang _ | nOverBang | nOverDash => simp at h

/-- Helper: `memberAux ieos accs = some (.name an)` requires `accs = []`
    and `ieos = .name an`. -/
private theorem memberAux_eq_name
    {ieos : ExprOrSpecial} {accs : List AstAccessor} {an : Spec.Name} :
    memberAux ieos accs = some (.name an) →
    accs = [] ∧ ieos = .name an := by
  intro h
  rcases memberAux_some_cases h with ⟨haccs, hr⟩ | ⟨_, hr⟩
  · exact ⟨haccs, hr.symm⟩
  · exact absurd hr (by simp)

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
  | rInits _ =>
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

/-- Helper: `memberAux ieos accs = some (.var v)` requires `accs = []`. -/
private theorem memberAux_eq_var
    {ieos : ExprOrSpecial} {accs : List AstAccessor} {v : Var} :
    memberAux ieos accs = some (.var v) → accs = [] := by
  intro h
  rcases memberAux_some_cases h with ⟨haccs, _⟩ | ⟨_, hr⟩
  · exact haccs
  · exact absurd hr (by simp)

/-- A member with non-empty access never yields a valid record-key attribute. -/
private theorem member_nonempty_validAttr {m : Cst.Member} (h : m.access ≠ []) :
    m.toExprOrSpecial?.bind ExprOrSpecial.toValidAttr? = none := by
  cases heos : m.toExprOrSpecial? with
  | none => rfl
  | some eos =>
    cases eos with
    | expr e => rfl
    | boolLit b => rfl
    | strLit lit => exact absurd (member_toExprOrSpecial_strLit heos).1 h
    | name an => exact absurd (member_toExprOrSpecial_name heos).1 h
    | var v =>
      exfalso
      simp [Cst.Member.toExprOrSpecial?, Option.bind_eq_some_iff] at heos
      obtain ⟨ieos, hieos, accs, haccs, hmaux⟩ := heos
      have haccsNil := memberAux_eq_var hmaux
      subst haccsNil
      cases hAcc : m.access with
      | nil => exact h hAcc
      | cons _ _ => rw [hAcc] at haccs; simp [List.mapM_cons, Option.bind_eq_some_iff] at haccs

/-- Definitional reductions for `memberAuxB` (sidestep overlapping-pattern simp). -/
private theorem memberAuxB_index (he : Expr) (id : String) (rest : List AstAccessor) :
    memberAuxB he (.index id :: rest) = memberAuxB (.getAttr he id) rest := rfl
private theorem memberAuxB_field_call (he : Expr) (id : Cst.Ident) (args : List Expr) (rest : List AstAccessor) :
    memberAuxB he (.field id :: .call args :: rest)
      = (id.toMeth? he args).bind (fun h' => memberAuxB h' rest) := rfl
private theorem memberAuxB_field_nil (he : Expr) (id : Cst.Ident) :
    memberAuxB he [.field id] = some (.getAttr he (CstCommon.Ident.toString id)) := rfl
private theorem memberAuxB_field_field (he : Expr) (id id2 : Cst.Ident) (rest2 : List AstAccessor) :
    memberAuxB he (.field id :: .field id2 :: rest2)
      = memberAuxB (.getAttr he (CstCommon.Ident.toString id)) (.field id2 :: rest2) := rfl
private theorem memberAuxB_field_index (he : Expr) (id : Cst.Ident) (id2 : String) (rest2 : List AstAccessor) :
    memberAuxB he (.field id :: .index id2 :: rest2)
      = memberAuxB (.getAttr he (CstCommon.Ident.toString id)) (.index id2 :: rest2) := rfl

/-- If a method-call translation succeeds and its receiver expression errors,
    the resulting expression errors. -/
private theorem toMeth?_eval_error
    {req : Request} {es : Entities} {id : Cst.Ident} {he head' : Expr}
    {args : List Expr} {err : Error}
    (hm : Cst.Ident.toMeth? id he args = some head')
    (herr : evaluate he req es = .error err) :
    ∃ err', evaluate head' req es = .error err' := by
  cases id with
  | idIdent s =>
    cases hop : CstCommon.String.toMethodOp? s with
    | none => simp [Cst.Ident.toMeth?, hop] at hm
    | some op =>
      cases op with
      | inl bop =>
        cases args with
        | nil => simp [Cst.Ident.toMeth?, hop, oneArg?] at hm
        | cons a as =>
          cases as with
          | cons _ _ => simp [Cst.Ident.toMeth?, hop, oneArg?] at hm
          | nil =>
            simp [Cst.Ident.toMeth?, hop, oneArg?] at hm
            subst hm
            exact ⟨err, by simp [evaluate, herr, bind, Except.bind]⟩
      | inr uop =>
        cases hargs : args.isEmpty with
        | false => simp [Cst.Ident.toMeth?, hop, hargs] at hm
        | true =>
          simp [Cst.Ident.toMeth?, hop, hargs] at hm
          subst hm
          exact ⟨err, by simp [evaluate, herr, bind, Except.bind]⟩
  | _ => simp [Cst.Ident.toMeth?] at hm

/-- If the head expression of an AST member-access spine errors, so does the
    whole spine. -/
theorem memberAuxB_eval_error
    {req : Request} {es : Entities} :
    (accs : List AstAccessor) → (he bexp : Expr) → (err : Error) →
    memberAuxB he accs = some bexp → evaluate he req es = .error err →
    ∃ err', evaluate bexp req es = .error err'
  | [], _, bexp, err, hb, herr => by
    simp only [memberAuxB, Option.some.injEq] at hb; subst hb; exact ⟨err, herr⟩
  | .call args :: rest, _, bexp, _, hb, _ => by
    simp [memberAuxB] at hb
  | .index id :: rest, he, bexp, err, hb, herr => by
    rw [memberAuxB_index] at hb
    exact memberAuxB_eval_error rest _ bexp err hb (by simp [evaluate, herr, bind, Except.bind])
  | .field id :: [], he, bexp, err, hb, herr => by
    rw [memberAuxB_field_nil] at hb; simp only [Option.some.injEq] at hb; subst hb
    exact ⟨err, by simp [evaluate, herr, bind, Except.bind]⟩
  | .field id :: .call args :: rest2, he, bexp, err, hb, herr => by
    rw [memberAuxB_field_call, Option.bind_eq_some_iff] at hb
    obtain ⟨head', hmeth, hrec⟩ := hb
    obtain ⟨err', herr'⟩ := toMeth?_eval_error hmeth herr
    exact memberAuxB_eval_error rest2 head' bexp err' hrec herr'
  | .field id :: .field id2 :: rest2, he, bexp, err, hb, herr => by
    rw [memberAuxB_field_field] at hb
    exact memberAuxB_eval_error (.field id2 :: rest2) _ bexp err hb
      (by simp [evaluate, herr, bind, Except.bind])
  | .field id :: .index id2 :: rest2, he, bexp, err, hb, herr => by
    rw [memberAuxB_field_index] at hb
    exact memberAuxB_eval_error (.index id2 :: rest2) _ bexp err hb
      (by simp [evaluate, herr, bind, Except.bind])
termination_by accs => accs.length
decreasing_by all_goals (simp_wf <;> omega)

/-- Bridge: collapsing `memberAux` of a (non-name) head through `toExpr?` equals
    running `memberAuxB` on the collapsed head expression. -/
theorem memberAux_toExpr_eq
    {peos : ExprOrSpecial} {headExpr : Expr} (accs : List AstAccessor)
    (hpe : peos.toExpr? = some headExpr) :
    (memberAux peos accs).bind ExprOrSpecial.toExpr? = memberAuxB headExpr accs := by
  cases peos with
  | name n => simp [ExprOrSpecial.toExpr?] at hpe
  | expr e =>
    simp only [ExprOrSpecial.toExpr?, Option.some.injEq] at hpe; subst hpe
    rw [memberAux_expr_eq]; cases memberAuxB e accs <;> rfl
  | boolLit b =>
    simp only [ExprOrSpecial.toExpr?, Option.some.injEq] at hpe; subst hpe
    cases accs with
    | nil => rfl
    | cons acc rest =>
      simp [memberAux, memberAuxA, ExprOrSpecial.toExpr?]
      cases memberAuxB (Expr.lit (.bool b)) (acc :: rest) <;> rfl
  | strLit s =>
    cases hus : CstCommon.unescape? s with
    | none => simp [ExprOrSpecial.toExpr?, hus] at hpe
    | some us =>
      simp [ExprOrSpecial.toExpr?, hus] at hpe
      subst hpe
      cases accs with
      | nil => simp [memberAux_nil, ExprOrSpecial.toExpr?, hus]; rfl
      | cons acc rest =>
        simp [memberAux, memberAuxA, ExprOrSpecial.toExpr?, hus]
        cases memberAuxB (Expr.lit (.string us)) (acc :: rest) <;> rfl
  | var v =>
    simp only [ExprOrSpecial.toExpr?, Option.some.injEq] at hpe; subst hpe
    cases accs with
    | nil => rfl
    | cons acc rest =>
      cases acc with
      | call args => rfl
      | index id =>
        simp [memberAux, memberAuxA, memberAuxB_index]
        cases memberAuxB (Expr.getAttr (.var v) id) rest <;> rfl
      | field id =>
        cases rest with
        | nil => rfl
        | cons acc2 rest2 =>
          cases acc2 with
          | call args =>
            rw [memberAuxB_field_call]
            cases hm : Cst.Ident.toMeth? id (.var v) args with
            | none => simp [memberAux, memberAuxA, ExprOrSpecial.toExpr?, hm]
            | some e =>
              simp [memberAux, memberAuxA, ExprOrSpecial.toExpr?, hm]
              cases memberAuxB e rest2 <;> rfl
          | field id2 =>
            simp [memberAux, memberAuxA, memberAuxB_field_field]
            cases memberAuxB (Expr.getAttr (.var v) (CstCommon.Ident.toString id)) (.field id2 :: rest2) <;> rfl
          | index id2 =>
            simp [memberAux, memberAuxA, memberAuxB_field_index]
            cases memberAuxB (Expr.getAttr (.var v) (CstCommon.Ident.toString id)) (.index id2 :: rest2) <;> rfl

/-- One step of the member-access agreement.  `he'` is the AST expression for
    this step's new head; `cstStep` is the evaluator's result for it.  They need
    only agree on `ok` results (method arguments agree only on `ok`). -/
theorem evalAccessors_step
    {req : Request} {es : Entities} {he' bexp : Expr} {cstStep : Result Value}
    {rest_cst : List Cst.MemAccess} {rest_ast : List AstAccessor}
    (hstep : ∀ w, evaluate he' req es = .ok w ↔ cstStep = .ok w)
    (hbrec : memberAuxB he' rest_ast = some bexp)
    (htail : ∀ hv', evaluate he' req es = .ok hv' →
               ∀ v, evaluate bexp req es = .ok v ↔ Cst.Member.evalAccessors hv' rest_cst req es = .ok v) :
    ∀ v, evaluate bexp req es = .ok v ↔
      (do let hv ← cstStep; Cst.Member.evalAccessors hv rest_cst req es) = .ok v := by
  intro v
  cases hcs : cstStep with
  | error e =>
    have hge : ∃ e'', evaluate he' req es = .error e'' := by
      cases h : evaluate he' req es with
      | error e'' => exact ⟨e'', rfl⟩
      | ok w => exact absurd ((hstep w).mp h) (by rw [hcs]; simp)
    obtain ⟨e'', hge⟩ := hge
    obtain ⟨e', he'eq⟩ := memberAuxB_eval_error rest_ast he' bexp e'' hbrec hge
    simp [he'eq, bind, Except.bind]
  | ok hv' =>
    have hge : evaluate he' req es = .ok hv' := (hstep hv').mpr hcs
    rw [htail hv' hge v]
    exact Iff.rfl

/-- A `.field`-headed CST accessor list translates to a `.field`-headed AST list. -/
private theorem mapM_toAst_field_head {i2 : Cst.Ident} {rest2 : List Cst.MemAccess}
    {tl_ast : List AstAccessor} :
    (Cst.MemAccess.field i2 :: rest2).mapM Cst.MemAccess.toAstAccessor? = some tl_ast →
    ∃ id r, tl_ast = .field id :: r := by
  intro h
  simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a2, ha2, r2, _, rfl⟩ := h
  cases i2 with
  | idIdent s2 =>
    simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at ha2
    obtain ⟨s2, _, rfl⟩ := ha2
    exact ⟨_, _, rfl⟩
  | _ => simp [Cst.MemAccess.toAstAccessor?] at ha2

/-- An `.index`-headed CST accessor list translates to an `.index`-headed AST list. -/
private theorem mapM_toAst_index_head {ex2 : Cst.Expr} {rest2 : List Cst.MemAccess}
    {tl_ast : List AstAccessor} :
    (Cst.MemAccess.index ex2 :: rest2).mapM Cst.MemAccess.toAstAccessor? = some tl_ast →
    ∃ id r, tl_ast = .index id :: r := by
  intro h
  simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨a2, ha2, r2, _, rfl⟩ := h
  simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at ha2
  obtain ⟨s2, _, rfl⟩ := ha2
  exact ⟨_, _, rfl⟩

/-- Core member-access agreement: the AST built by `memberAuxB` over a head
    expression `headExpr` evaluates in agreement (on `ok` results) with the CST
    evaluator `Member.evalAccessors` run on the same accessors, provided the
    head expression evaluates to the head value and every argument
    sub-expression agrees (the latter supplied by the mutual `Expr` induction). -/
theorem evalAccessors_agrees
    {req : Request} {es : Entities} :
    (accs_cst : List Cst.MemAccess) → (accs_ast : List AstAccessor) →
    (headExpr bexp : Expr) → (head : Value) →
    accs_cst.mapM Cst.MemAccess.toAstAccessor? = some accs_ast →
    memberAuxB headExpr accs_ast = some bexp →
    evaluate headExpr req es = .ok head →
    (∀ ce : Cst.Expr, sizeOf ce < sizeOf accs_cst → ∀ ax, ce.toAExpr? = some ax →
      ∀ w, evaluate ax req es = .ok w ↔ ce.evaluate req es = .ok w) →
    ∀ v, evaluate bexp req es = .ok v ↔ Cst.Member.evalAccessors head accs_cst req es = .ok v
  | [], accs_ast, headExpr, bexp, head, htrans, hb, hhead, _ => by
    intro v
    simp at htrans; subst htrans
    simp only [memberAuxB, Option.some.injEq] at hb; subst hb
    rw [hhead]; simp [Cst.Member.evalAccessors]
  | .call args :: rest, accs_ast, headExpr, bexp, head, htrans, hb, hhead, _ => by
    intro v
    rw [List.mapM_cons] at htrans
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htrans
    obtain ⟨a_ast, ha_ast, rest_ast, _, rfl⟩ := htrans
    simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha_ast
    obtain ⟨xs, _, rfl⟩ := ha_ast
    simp [memberAuxB] at hb
  | .index ex :: rest, accs_ast, headExpr, bexp, head, htrans, hb, hhead, harg => by
    intro v
    rw [List.mapM_cons] at htrans
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htrans
    obtain ⟨a_ast, ha_ast, rest_ast, hrest, rfl⟩ := htrans
    simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha_ast
    obtain ⟨s, hs, rfl⟩ := ha_ast
    rw [memberAuxB_index] at hb
    have hev : Cst.Member.evalAccessors head (.index ex :: rest) req es
             = (do let hv ← getAttr head s es; Cst.Member.evalAccessors hv rest req es) := by
      simp [Cst.Member.evalAccessors, hs]
    rw [hev]
    exact evalAccessors_step (he' := .getAttr headExpr s) (cstStep := getAttr head s es)
      (fun w => by simp [evaluate, hhead, bind, Except.bind]) hb
      (fun hv' hge => evalAccessors_agrees rest rest_ast (.getAttr headExpr s) bexp hv'
        hrest hb hge (fun ce hsz => harg ce (Nat.lt_trans hsz (by simp only [List.cons.sizeOf_spec]; omega)))) v
  | .field i :: [], accs_ast, headExpr, bexp, head, htrans, hb, hhead, harg => by
    intro v
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at htrans
    obtain ⟨a_ast, ha_ast, rest_ast, hrest, rfl⟩ := htrans
    cases i with
    | idIdent s0 =>
      simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha_ast
      obtain ⟨s, hs, rfl⟩ := ha_ast
      subst hrest
      rw [memberAuxB_field_nil] at hb
      have hev : Cst.Member.evalAccessors head [.field (.idIdent s0)] req es
               = (do let hv ← getAttr head s es; Cst.Member.evalAccessors hv [] req es) := by
        simp [Cst.Member.evalAccessors, hs]
      have hstep : ∀ w, evaluate (Expr.getAttr headExpr (CstCommon.Ident.toString (.idIdent s))) req es = .ok w
                   ↔ getAttr head s es = .ok w := by
        intro w; simp [evaluate, hhead, CstCommon.Ident.toString, bind, Except.bind]
      have hbrec : memberAuxB (Expr.getAttr headExpr (CstCommon.Ident.toString (.idIdent s))) [] = some bexp := hb
      rw [hev]
      exact evalAccessors_step hstep hbrec
        (fun hv' hge => evalAccessors_agrees [] [] _ bexp hv' (by simp) hbrec hge
          (fun ce hsz => harg ce (Nat.lt_trans hsz (by simp only [List.cons.sizeOf_spec]; omega)))) v
    | _ => simp [Cst.MemAccess.toAstAccessor?] at ha_ast
  | .field i :: .call args :: rest2, accs_ast, headExpr, bexp, head, htrans, hb, hhead, harg => by
    intro v
    rw [List.mapM_cons] at htrans
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htrans
    obtain ⟨a_ast, ha_ast, tl_ast, htl, rfl⟩ := htrans
    cases i with
    | idIdent s0 =>
      simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha_ast
      obtain ⟨s, hs, rfl⟩ := ha_ast
      rw [List.mapM_cons] at htl
      simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htl
      obtain ⟨a2_ast, ha2_ast, rest2_ast, hrest2, rfl⟩ := htl
      simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha2_ast
      obtain ⟨xs, hxs, rfl⟩ := ha2_ast
      rw [memberAuxB_field_call] at hb
      cases hop : CstCommon.String.toMethodOp? s with
      | none => simp [Cst.Ident.toMeth?, hop] at hb
      | some op =>
        cases op with
        | inl bop =>
          cases args with
          | nil => simp [Cst.Expr.toAExprs?] at hxs; subst hxs; simp [Cst.Ident.toMeth?, hop, oneArg?] at hb
          | cons arg rest_args =>
            cases rest_args with
            | cons a2 r2 =>
              simp only [Cst.Expr.toAExprs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hxs
              obtain ⟨ax, hax, xs2, hxs2, rfl⟩ := hxs
              obtain ⟨bx, hbx, xs3, hxs3, rfl⟩ := hxs2
              simp [Cst.Ident.toMeth?, hop, oneArg?] at hb
            | nil =>
              simp only [Cst.Expr.toAExprs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hxs
              obtain ⟨ax, hax, a, rfl, rfl⟩ := hxs
              simp only [Cst.Ident.toMeth?, hop, oneArg?, Option.bind_eq_bind, Option.bind_some] at hb
              have hagr := harg arg (by simp only [List.cons.sizeOf_spec, Cst.MemAccess.call.sizeOf_spec]; omega) ax hax
              have hstep : ∀ w, evaluate (Expr.binaryApp bop headExpr ax) req es = .ok w
                           ↔ (do let argVal ← arg.evaluate req es; apply₂ bop head argVal es) = .ok w := by
                intro w
                cases hae : arg.evaluate req es with
                | ok argVal =>
                  have hax_ok : evaluate ax req es = .ok argVal := (hagr argVal).mpr hae
                  simp [evaluate, hhead, hax_ok, bind, Except.bind]
                | error e =>
                  cases hax2 : evaluate ax req es with
                  | ok w' => rw [(hagr w').mp hax2] at hae; simp at hae
                  | error e' => simp [evaluate, hhead, hax2, bind, Except.bind]
              have hev : Cst.Member.evalAccessors head (.field (.idIdent s0) :: .call [arg] :: rest2) req es
                       = (do let hv ← (do let argVal ← arg.evaluate req es; apply₂ bop head argVal es);
                             Cst.Member.evalAccessors hv rest2 req es) := by
                simp [Cst.Member.evalAccessors, hs, hop, bind_assoc]
              rw [hev]
              exact evalAccessors_step hstep hb
                (fun hv' hge => evalAccessors_agrees rest2 rest2_ast (.binaryApp bop headExpr ax) bexp hv'
                  hrest2 hb hge (fun ce hsz => harg ce (Nat.lt_trans hsz
                    (by simp only [List.cons.sizeOf_spec, Cst.MemAccess.call.sizeOf_spec]; omega)))) v
        | inr uop =>
          cases args with
          | cons arg rest_args =>
            simp only [Cst.Expr.toAExprs?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hxs
            obtain ⟨ax, hax, xs2, hxs2, rfl⟩ := hxs
            simp [Cst.Ident.toMeth?, hop] at hb
          | nil =>
            simp only [Cst.Expr.toAExprs?, Option.some.injEq] at hxs; subst hxs
            simp only [Cst.Ident.toMeth?, hop, List.isEmpty_nil, if_true] at hb
            have hstep : ∀ w, evaluate (Expr.unaryApp uop headExpr) req es = .ok w
                         ↔ apply₁ uop head = .ok w := by
              intro w; simp [evaluate, hhead, bind, Except.bind]
            have hev : Cst.Member.evalAccessors head (.field (.idIdent s0) :: .call [] :: rest2) req es
                     = (do let hv ← apply₁ uop head; Cst.Member.evalAccessors hv rest2 req es) := by
              simp [Cst.Member.evalAccessors, hs, hop, bind, Except.bind]
            rw [hev]
            exact evalAccessors_step hstep hb
              (fun hv' hge => evalAccessors_agrees rest2 rest2_ast (.unaryApp uop headExpr) bexp hv'
                hrest2 hb hge (fun ce hsz => harg ce (Nat.lt_trans hsz
                  (by simp only [List.cons.sizeOf_spec, Cst.MemAccess.call.sizeOf_spec]; omega)))) v
    | _ => simp [Cst.MemAccess.toAstAccessor?] at ha_ast
  | .field i :: .field i2 :: rest2, accs_ast, headExpr, bexp, head, htrans, hb, hhead, harg => by
    intro v
    rw [List.mapM_cons] at htrans
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htrans
    obtain ⟨a_ast, ha_ast, tl_ast, htl, rfl⟩ := htrans
    cases i with
    | idIdent s0 =>
      simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha_ast
      obtain ⟨s, hs, rfl⟩ := ha_ast
      obtain ⟨id2, r2, htl_shape⟩ := mapM_toAst_field_head htl
      rw [htl_shape, memberAuxB_field_field, ← htl_shape] at hb
      have hev : Cst.Member.evalAccessors head (.field (.idIdent s0) :: .field i2 :: rest2) req es
               = (do let hv ← getAttr head s es; Cst.Member.evalAccessors hv (.field i2 :: rest2) req es) := by
        simp [Cst.Member.evalAccessors, hs]
      have hstep : ∀ w, evaluate (Expr.getAttr headExpr (CstCommon.Ident.toString (.idIdent s))) req es = .ok w
                   ↔ getAttr head s es = .ok w := by
        intro w; simp [evaluate, hhead, CstCommon.Ident.toString, bind, Except.bind]
      rw [hev]
      exact evalAccessors_step hstep hb
        (fun hv' hge => evalAccessors_agrees (.field i2 :: rest2) tl_ast _ bexp hv'
          htl hb hge (fun ce hsz => harg ce (Nat.lt_trans hsz (by simp only [List.cons.sizeOf_spec]; omega)))) v
    | _ => simp [Cst.MemAccess.toAstAccessor?] at ha_ast
  | .field i :: .index ex2 :: rest2, accs_ast, headExpr, bexp, head, htrans, hb, hhead, harg => by
    intro v
    rw [List.mapM_cons] at htrans
    simp only [Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at htrans
    obtain ⟨a_ast, ha_ast, tl_ast, htl, rfl⟩ := htrans
    cases i with
    | idIdent s0 =>
      simp only [Cst.MemAccess.toAstAccessor?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at ha_ast
      obtain ⟨s, hs, rfl⟩ := ha_ast
      obtain ⟨id2, r2, htl_shape⟩ := mapM_toAst_index_head htl
      rw [htl_shape, memberAuxB_field_index, ← htl_shape] at hb
      have hev : Cst.Member.evalAccessors head (.field (.idIdent s0) :: .index ex2 :: rest2) req es
               = (do let hv ← getAttr head s es; Cst.Member.evalAccessors hv (.index ex2 :: rest2) req es) := by
        simp [Cst.Member.evalAccessors, hs]
      have hstep : ∀ w, evaluate (Expr.getAttr headExpr (CstCommon.Ident.toString (.idIdent s))) req es = .ok w
                   ↔ getAttr head s es = .ok w := by
        intro w; simp [evaluate, hhead, CstCommon.Ident.toString, bind, Except.bind]
      rw [hev]
      exact evalAccessors_step hstep hb
        (fun hv' hge => evalAccessors_agrees (.index ex2 :: rest2) tl_ast _ bexp hv'
          htl hb hge (fun ce hsz => harg ce (Nat.lt_trans hsz (by simp only [List.cons.sizeOf_spec]; omega)))) v
    | _ => simp [Cst.MemAccess.toAstAccessor?] at ha_ast
termination_by accs_cst _ _ _ _ _ _ _ _ => accs_cst.length
decreasing_by all_goals (simp_wf <;> omega)

/-- If a primary translates to a (path-free, function-named) name, it is
    syntactically `.name ⟨[], .idIdent s⟩`. -/
theorem toExprOrSpecial_name_func {item : Cst.Primary} {an : Spec.Name}
    (h : item.toExprOrSpecial? = some (.name an))
    (hp : an.path = []) (hf : CstCommon.String.isFunctionName? an.id = true) :
    ∃ s, item = .name { path := [], name := .idIdent s } := by
  cases item with
  | name n =>
    obtain ⟨npath, nname⟩ := n
    simp only [Cst.Primary.toExprOrSpecial?] at h
    cases hv : Cst.Name.toVar? ⟨npath, nname⟩ with
    | some v => rw [hv] at h; simp at h
    | none =>
      rw [hv] at h
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        ExprOrSpecial.name.injEq] at h
      obtain ⟨an', han', rfl⟩ := h
      have hagree := Cst.Name.toAName?_agrees han'
      rw [hagree] at hp hf
      simp only [List.map_eq_nil_iff] at hp
      subst hp
      cases nname with
      | idIdent s => exact ⟨s, rfl⟩
      | _ => exact absurd hf (by simp [CstCommon.Ident.toString, CstCommon.String.isFunctionName?])
  | literal l =>
    cases l <;>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
        Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  | ref r =>
    cases r with
    | uid path eid =>
      cases eid with
      | string s =>
        simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?,
          Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    | ref a b =>
      simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?] at h
  | expr e =>
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  | eList es =>
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  | rInits r =>
    simp [Cst.Primary.toExprOrSpecial?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h

/-- For the `rIsIn` case: when the translator's `toEntityType?` succeeds with
    `et`, the evaluator's structural `toEntityTypeName?` succeeds with the same
    `et`.  Both enforce the same shape (extended/mext empty, op `none` or
    `.nDash 0`, access empty, item a `.name`), and both now build the entity-type
    name via the shared `CstCommon.Name.toAName?`, so they agree. -/
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
          simp [Cst.AddExpr.toEntityTypeName?, hAccNil, hItem]
          exact hAName
        | some op' =>
          cases op' with
          | nDash k =>
            by_cases hk : k = 0
            · subst hk
              obtain ⟨hAccNil, n, hItem, hAName⟩ := member_toExprOrSpecial_name heos
              simp [Cst.AddExpr.toEntityTypeName?, hAccNil, hItem]
              exact hAName
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
    (hEt : ety.toEntityType? = some et)
    (htarget_iff : ∀ v, evaluate mt req es = .ok v ↔ target.evaluate req es = .ok v)
    (hinEntity_iff : ∀ v, evaluate mi req es = .ok v ↔ ie.evaluate req es = .ok v)
    (hie_trans : ie.toAExpr? = some mi) :
    ∀ v, evaluate (Expr.and (.unaryApp (.is et) mt) (.binaryApp .mem mt mi)) req es = .ok v ↔
         (Cst.Relation.rIsIn target ety (some ie)).evaluate req es = .ok v := by
  intro v
  simp only [Cst.Relation.evaluate, hEt, evaluate, hie_trans, Option.isNone_some,
             Bool.false_eq_true, if_false]
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

/-- If `foldExtended` succeeds on `xs`, every conjunct in `xs` translates. Used
    to discharge the `AndExpr.evaluate` translatability guard. -/
theorem andExprFoldExtended_some_all_translate (xs : List Cst.Relation) :
    ∀ {acc result : Expr}, Cst.AndExpr.foldExtended acc xs = some result →
    xs.all (fun r => r.toAExpr?.isSome) = true := by
  induction xs with
  | nil => intro acc result _; rfl
  | cons rel rest ih =>
    intro acc result h
    simp [Cst.AndExpr.foldExtended] at h
    cases hrel : rel.toAExpr? with
    | none => rw [hrel] at h; simp at h
    | some aval =>
      rw [hrel] at h
      simp at h
      simp [List.all_cons, hrel, ih h]

/-- When every conjunct translates, `AndExpr.evaluate`'s guard is a no-op and it
    reduces to the plain `initial`-then-`foldOps` evaluation. -/
theorem AndExpr.evaluate_eq {e : Cst.AndExpr} {req : Request} {es : Entities}
    (h : (e.extended.all fun r => r.toAExpr?.isSome) = true) :
    Cst.AndExpr.evaluate e req es =
      (do let acc ← e.initial.evaluate req es; Cst.AndExpr.foldOps acc e.extended req es) := by
  simp only [Cst.AndExpr.evaluate, if_pos h]

/-- If `foldExtended` succeeds on `xs`, every disjunct in `xs` translates. -/
theorem orExprFoldExtended_some_all_translate (xs : List Cst.AndExpr) :
    ∀ {acc result : Expr}, Cst.OrExpr.foldExtended acc xs = some result →
    xs.all (fun r => r.toAExpr?.isSome) = true := by
  induction xs with
  | nil => intro acc result _; rfl
  | cons rel rest ih =>
    intro acc result h
    simp [Cst.OrExpr.foldExtended] at h
    cases hrel : rel.toAExpr? with
    | none => rw [hrel] at h; simp at h
    | some aval =>
      rw [hrel] at h
      simp at h
      simp [List.all_cons, hrel, ih h]

/-- When every disjunct translates, `OrExpr.evaluate`'s guard is a no-op and it
    reduces to the plain `initial`-then-`foldOps` evaluation. -/
theorem OrExpr.evaluate_eq {e : Cst.OrExpr} {req : Request} {es : Entities}
    (h : (e.extended.all fun r => r.toAExpr?.isSome) = true) :
    Cst.OrExpr.evaluate e req es =
      (do let acc ← e.initial.evaluate req es; Cst.OrExpr.foldOps acc e.extended req es) := by
  simp only [Cst.OrExpr.evaluate, if_pos h]

/-- When both branches translate, `ExprData.evaluate`'s `edIf` guard is a no-op
    and it reduces to the plain conditional evaluation. -/
theorem ExprData.evaluate_edIf_eq {i t f : Cst.Expr} {req : Request} {es : Entities}
    (h : (t.toAExpr?.isSome && f.toAExpr?.isSome) = true) :
    Cst.ExprData.evaluate (.edIf i t f) req es =
      (do let b ← (i.evaluate req es).as Bool;
          if b then t.evaluate req es else f.evaluate req es) := by
  simp only [Cst.ExprData.evaluate, if_pos h]

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

/-- `toAExprs?` is `mapM` of `toAExpr?`. -/
theorem toAExprs?_eq_mapM (args : List Cst.Expr) :
    Cst.Expr.toAExprs? args = args.mapM (fun ce => ce.toAExpr?) := by
  induction args with
  | nil => simp [Cst.Expr.toAExprs?, List.mapM_nil]
  | cons ce rest ih => simp [Cst.Expr.toAExprs?, List.mapM_cons, ih]

/-- Agreement for translated argument lists: evaluating the AST args agrees (on
    `ok`) with evaluating the CST args, given per-argument agreement. -/
theorem toAExprs?_eval_agrees {req : Request} {es : Entities}
    (args : List Cst.Expr) (xs : List Expr)
    (htr : Cst.Expr.toAExprs? args = some xs)
    (harg : ∀ ce ∈ args, ∀ ax, ce.toAExpr? = some ax →
      ∀ w, evaluate ax req es = .ok w ↔ ce.evaluate req es = .ok w) :
    ∀ vs, xs.mapM (fun a => evaluate a req es) = .ok vs ↔
          args.mapM (fun ce => ce.evaluate req es) = .ok vs := by
  apply mapM_eval_agrees req es args xs ?_ harg
  simp only [List.mapM₁_eq_mapM (fun ce : Cst.Expr => ce.toAExpr?), ← toAExprs?_eq_mapM]
  exact htr

/- Lifting round-trips and entity-UID translation agreement -/

/- For Primary's rInits (record) case -/

/-- The CST-native record-key attribute extractor on a `Primary` agrees with the
    translator's `toExprOrSpecial? >>= toValidAttr?`. -/
theorem Cst.Primary.toAttr?_consistent (p : Cst.Primary) :
    Cst.Primary.toAttr? p = p.toExprOrSpecial?.bind ExprOrSpecial.toValidAttr? := by
  cases p with
  | literal l =>
    cases l with
    | liTrue | liFalse | liStr s =>
      simp [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
            ExprOrSpecial.toValidAttr?]
    | liNum n =>
      simp [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?,
            Option.bind]
      cases Int64.ofInt? (n.toNat : Int) <;> simp [ExprOrSpecial.toValidAttr?]
  | name n =>
    obtain ⟨path, name⟩ := n
    cases path with
    | nil =>
      cases name <;>
        simp [Cst.Primary.toAttr?, Cst.Ident.toAttr?, Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?,
              Cst.Name.toAName?, CstCommon.Name.toAName?,
              CstCommon.Ident.toUnrestrictedString?, ExprOrSpecial.toValidAttr?,
              Var.toString]
    | cons hd tl =>
      simp only [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?,
        List.isEmpty_cons, Bool.not_false, ite_true]
      cases hAN : Cst.Name.toAName? ⟨hd :: tl, name⟩ with
      | none => simp
      | some an =>
        have heq := Cst.Name.toAName?_agrees hAN
        simp [ExprOrSpecial.toValidAttr?, heq]
  | ref r =>
    cases r with
    | uid path eid =>
      cases eid with
      | string s =>
        simp [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?,
              Option.bind]
        cases (Cst.Name.toAName? path) <;>
          cases (CstCommon.unescape? s) <;> simp [ExprOrSpecial.toValidAttr?]
    | ref _ _ =>
      simp [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?]
  | expr e =>
    simp [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Option.bind]
    cases (e.toAExpr?) <;> simp [ExprOrSpecial.toValidAttr?]
  | eList es =>
    simp [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Option.bind]
    cases (es.mapM₁ (fun x => x.val.toAExpr?)) <;> simp [ExprOrSpecial.toValidAttr?]
  | rInits r =>
    simp [Cst.Primary.toAttr?, Cst.Primary.toExprOrSpecial?, Option.bind]
    cases (rInitsToMap? r) <;> simp [ExprOrSpecial.toValidAttr?]

/-- A translation result that always produces an `.expr` is never a valid attribute. -/
private theorem bind_validAttr_expr {α : Type} (o : Option α) (g : α → Expr) :
    (o.bind (fun a => some (ExprOrSpecial.expr (g a)))).bind ExprOrSpecial.toValidAttr? = none := by
  cases o <;> simp [ExprOrSpecial.toValidAttr?]

set_option linter.unusedSimpArgs false in
/-- The CST-native record-key attribute extractor on an `Expr` agrees with the
    translator's `toExprOrSpecial? >>= toValidAttr?`.  Peeling lemma: the key must
    reduce to a bare primary; analogous to the `addExpr_to*_agrees` peeling proofs. -/
theorem Cst.Expr.toAttr?_consistent (e : Cst.Expr) :
    Cst.Expr.toAttr? e = e.toExprOrSpecial?.bind ExprOrSpecial.toValidAttr? := by
  match e with
  | .expr ⟨.edIf i t f⟩ =>
    simp only [Cst.Expr.toAttr?, Cst.Expr.toExprOrSpecial?, Cst.ExprImpl.toExprOrSpecial?,
      Cst.ExprData.toExprOrSpecial?]
    cases i.toAExpr? <;> cases t.toAExpr? <;> cases f.toAExpr? <;>
      simp [ExprOrSpecial.toValidAttr?]
  | .expr ⟨.edOr o⟩ =>
    have hred : Cst.Expr.toExprOrSpecial? (.expr ⟨.edOr o⟩) = o.toExprOrSpecial? := by
      simp [Cst.Expr.toExprOrSpecial?, Cst.ExprImpl.toExprOrSpecial?, Cst.ExprData.toExprOrSpecial?]
    rw [hred]
    cases hoe : o.extended with
    | cons _ _ =>
      simp only [Cst.Expr.toAttr?, hoe, List.isEmpty_cons, Bool.not_false, Bool.true_or, if_true]
      rw [Cst.OrExpr.toExprOrSpecial?, hoe]
      simp [ExprOrSpecial.toValidAttr?, Option.bind_assoc]
    | nil =>
      rw [Cst.OrExpr.toExprOrSpecial?, hoe]
      cases hae : o.initial.extended with
      | cons _ _ =>
        simp only [Cst.Expr.toAttr?, hoe, hae, List.isEmpty_nil, List.isEmpty_cons,
          Bool.not_true, Bool.not_false, Bool.or_true, if_true]
        rw [Cst.AndExpr.toExprOrSpecial?, hae]
        simp [ExprOrSpecial.toValidAttr?, Option.bind_assoc]
      | nil =>
        rw [Cst.AndExpr.toExprOrSpecial?, hae]
        cases hrel : o.initial.initial with
        | rHas tgt fld =>
          have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
            simp [Cst.Expr.toAttr?, hoe, hae, hrel]
          rw [hL, Cst.Relation.toExprOrSpecial?]
          cases tgt.toAExpr? with
          | none => simp
          | some t =>
            cases fld.toHasRhs? with
            | none => simp
            | some mf => cases mf <;> simp [ExprOrSpecial.toValidAttr?]
        | rLike tgt pat =>
          have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
            simp [Cst.Expr.toAttr?, hoe, hae, hrel]
          rw [hL, Cst.Relation.toExprOrSpecial?]
          cases tgt.toAExpr? with
          | none => simp
          | some t => cases pat.toPattern? <;> simp [ExprOrSpecial.toValidAttr?]
        | rIsIn tgt ety inE =>
          have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
            simp [Cst.Expr.toAttr?, hoe, hae, hrel]
          rw [hL, Cst.Relation.toExprOrSpecial?]
          cases tgt.toAExpr? with
          | none => simp
          | some t =>
            cases ety.toEntityType? with
            | none => simp
            | some et =>
              cases inE with
              | none => simp [ExprOrSpecial.toValidAttr?]
              | some ie => cases ie.toAExpr? <;> simp [ExprOrSpecial.toValidAttr?, Option.bind_assoc]
        | rCommon ae ext =>
          cases hext : ext with
          | cons hd tl =>
            have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
              simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext]
            rw [hL]
            cases tl with
            | cons _ _ => simp [Cst.Relation.toExprOrSpecial?]
            | nil =>
              simp [Cst.Relation.toExprOrSpecial?, ExprOrSpecial.toValidAttr?, Option.bind_assoc]
          | nil =>
            cases hax : ae.extended with
            | cons _ _ =>
              have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax]
              rw [hL]
              simp [Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?, hax,
                ExprOrSpecial.toValidAttr?, Option.bind_assoc]
            | nil =>
              cases hmx : ae.initial.extended with
              | cons _ _ =>
                have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                  simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx]
                rw [hL]
                simp [Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?,
                  Cst.MultExpr.toExprOrSpecial?, hax, hmx, ExprOrSpecial.toValidAttr?,
                  Option.bind_assoc]
              | nil =>
                have hredRel : (Cst.Relation.rCommon ae []).toExprOrSpecial?
                    = ae.initial.initial.toExprOrSpecial? := by
                  simp [Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?,
                    Cst.MultExpr.toExprOrSpecial?, hax, hmx]
                rw [hredRel, Cst.Unary.toExprOrSpecial?]
                cases hop : ae.initial.initial.op with
                | none =>
                  cases hacc : ae.initial.initial.item.access with
                  | nil =>
                    have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩)
                        = Cst.Primary.toAttr? ae.initial.initial.item.item := by
                      simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hacc, hop]
                    rw [hL, Cst.Member.toExprOrSpecial?, hacc]
                    simp [List.mapM_nil, memberAuxA, memberAux, Cst.Primary.toAttr?_consistent]
                  | cons hd tl =>
                    have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                      simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hacc]
                    rw [hL]
                    exact (member_nonempty_validAttr (by rw [hacc]; simp)).symm
                | some np =>
                  cases np with
                  | nDash n =>
                    by_cases hn : n = 0
                    · subst hn
                      cases hacc : ae.initial.initial.item.access with
                      | nil =>
                        have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩)
                            = Cst.Primary.toAttr? ae.initial.initial.item.item := by
                          simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hacc, hop]
                        rw [hL, Cst.Member.toExprOrSpecial?, hacc]
                        simp [List.mapM_nil, memberAuxA, memberAux, Cst.Primary.toAttr?_consistent]
                      | cons hd tl =>
                        have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                          simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hacc]
                        rw [hL]
                        exact (member_nonempty_validAttr (by rw [hacc]; simp)).symm
                    · have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                        simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hop, hn]
                      rw [hL]
                      simp only [hn]
                      repeat' split
                      all_goals simp [ExprOrSpecial.toValidAttr?, Option.bind_assoc]
                  | nBang n =>
                    have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                      simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hop]
                    rw [hL]
                    simp [ExprOrSpecial.toValidAttr?, Option.bind_assoc]
                  | nOverBang =>
                    have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                      simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hop]
                    rw [hL]; simp
                  | nOverDash =>
                    have hL : Cst.Expr.toAttr? (.expr ⟨.edOr o⟩) = none := by
                      simp [Cst.Expr.toAttr?, hoe, hae, hrel, hext, hax, hmx, hop]
                    rw [hL]; simp


/-- Lift an element-wise `Except`-result agreement through one `mapM` cons step. -/
private theorem except_bind_cons_iff {β γ : Type} {X Y : Except γ (List β)} {hd : β}
    {vs : List β} (h : ∀ vs', X = .ok vs' ↔ Y = .ok vs') :
    (X >>= fun tl => Except.ok (hd :: tl)) = .ok vs ↔
    (Y >>= fun tl => Except.ok (hd :: tl)) = .ok vs := by
  cases hX : X with
  | error e =>
    cases hY : Y with
    | error e' => simp [bind, Except.bind]
    | ok vsy => have := (h vsy).mpr hY; rw [hX] at this; cases this
  | ok vsx =>
    have hY := (h vsx).mp hX
    rw [hY]

/-- Record-level bridge: when `rInitsToMap? r = some map`, evaluating the
    translated AST record entries (`map`) agrees element-wise with the CST
    `.rInits` evaluation, given the per-value evaluation agreement. -/
theorem rInits_eval_agrees (req : Request) (es : Entities) :
    ∀ (r : List Cst.RecInit) (map : List (Attr × Expr)),
      rInitsToMap? r = some map →
      (∀ ri ∈ r, ∀ ax, ri.value.toAExpr? = some ax →
        ∀ v, evaluate ax req es = .ok v ↔ ri.value.evaluate req es = .ok v) →
      ∀ vs, map.mapM (fun x => bindAttr x.fst (evaluate x.snd req es)) = .ok vs ↔
            r.mapM (fun ri =>
              match ri.key.toAttr? with
              | none => Except.error (Error.cstError CstError.stringError)
              | some attr => do let val ← ri.value.evaluate req es; .ok (attr, val)) = .ok vs := by
  intro r
  induction r with
  | nil =>
    intro map hmap _ vs
    simp [rInitsToMap?] at hmap
    subst hmap
    simp [List.mapM_nil]
  | cons ri rs ih =>
    intro map hmap hperElt vs
    simp [rInitsToMap?, Option.bind_eq_some_iff] at hmap
    obtain ⟨attr_eos, hattr_eos, attr, hattr, vexpr, hvexpr, rest, hrest, hmapeq⟩ := hmap
    subst hmapeq
    -- attr consistency: `ri.key.toAttr? = some attr`
    have hkey : ri.key.toAttr? = some attr := by
      rw [Cst.Expr.toAttr?_consistent, hattr_eos]; simpa using hattr
    -- per-value iff for the head
    have hhd_iff : ∀ vp, evaluate vexpr req es = .ok vp ↔ ri.value.evaluate req es = .ok vp :=
      hperElt ri List.mem_cons_self vexpr hvexpr
    -- IH for the tail
    have htl_perElt : ∀ x ∈ rs, ∀ ax, x.value.toAExpr? = some ax →
        ∀ v, evaluate ax req es = .ok v ↔ x.value.evaluate req es = .ok v := by
      intro x hx ax hax v
      exact hperElt x (List.mem_cons_of_mem _ hx) ax hax v
    have ih' := ih rest hrest htl_perElt
    -- head-element agreement (attr + value)
    have head_iff : ∀ p, bindAttr attr (evaluate vexpr req es) = .ok p ↔
        (do let val ← ri.value.evaluate req es; Except.ok (attr, val)) = .ok p := by
      intro p
      simp only [bindAttr, bind, Except.bind, pure, Except.pure]
      cases hev : evaluate vexpr req es with
      | error e =>
        cases hev2 : ri.value.evaluate req es with
        | error e' => simp
        | ok v => have := (hhd_iff v).mpr hev2; rw [this] at hev; cases hev
      | ok hv => have := (hhd_iff hv).mp hev; rw [this]
    simp only [List.mapM_cons, hkey]
    cases hHd : bindAttr attr (evaluate vexpr req es) with
    | error e =>
      cases hCst : (do let val ← ri.value.evaluate req es; Except.ok (attr, val)) with
      | ok p => have := (head_iff p).mpr hCst; rw [this] at hHd; cases hHd
      | error e' => simp [bind, Except.bind]
    | ok p =>
      have hCst := (head_iff p).mp hHd
      rw [hCst]
      exact except_bind_cons_iff (hd := p) (vs := vs) ih'

/-- Lift an element-wise `Except`-result agreement through a common wrapper. -/
private theorem except_bind_iff {β δ γ : Type} {X Y : Except γ β} {g : β → δ} {v : δ}
    (h : ∀ b, X = .ok b ↔ Y = .ok b) :
    (X >>= fun b => Except.ok (g b)) = .ok v ↔ (Y >>= fun b => Except.ok (g b)) = .ok v := by
  cases hX : X with
  | error e =>
    cases hY : Y with
    | error e' => simp [bind, Except.bind]
    | ok b => have := (h b).mpr hY; rw [hX] at this; cases this
  | ok b =>
    have hY := (h b).mp hX
    rw [hY]

/-- Evaluate-level record bridge: the translated AST record `Expr.record map`
    and the CST `.rInits r` evaluate to the same value. -/
theorem rInits_record_eval_agrees (req : Request) (es : Entities)
    (r : List Cst.RecInit) (map : List (Attr × Expr))
    (hmap : rInitsToMap? r = some map)
    (hperElt : ∀ ri ∈ r, ∀ ax, ri.value.toAExpr? = some ax →
        ∀ v, evaluate ax req es = .ok v ↔ ri.value.evaluate req es = .ok v) :
    ∀ v, evaluate (Expr.record map) req es = .ok v ↔
         (Cst.Primary.rInits r).evaluate req es = .ok v := by
  intro v
  have hbridge := rInits_eval_agrees req es r map hmap hperElt
  have hAST : evaluate (Expr.record map) req es =
      (map.mapM (fun x => bindAttr x.fst (evaluate x.snd req es))) >>=
      fun avs => Except.ok (Value.record (Map.make avs)) := by
    simp only [evaluate, List.mapM₂_eq_mapM (fun x => bindAttr x.fst (evaluate x.snd req es))]
  have hCST : (Cst.Primary.rInits r).evaluate req es =
      (r.mapM (fun ri =>
        match ri.key.toAttr? with
        | none => Except.error (Error.cstError CstError.stringError)
        | some attr => do let val ← ri.value.evaluate req es; Except.ok (attr, val))) >>=
      fun avs => Except.ok (Value.record (Map.make avs)) := by
    simp only [Cst.Primary.evaluate]
    congr 1
    exact List.mapM₁_eq_mapM (fun ri : Cst.RecInit =>
      match ri.key.toAttr? with
      | none => Except.error (Error.cstError CstError.stringError)
      | some attr => do let val ← ri.value.evaluate req es; Except.ok (attr, val)) r
  rw [hAST, hCST]
  exact except_bind_iff hbridge

/-- Lifting a CST expr to a `Relation` and translating round-trips. -/
theorem toRelation_toAExpr (e : Cst.Expr) :
    (Cst.Expr.toRelation e).toAExpr? = e.toAExpr? := by
  simp [Cst.Expr.toRelation, Cst.Expr.toPrimary, Cst.Primary.toMember,
    Cst.Member.toUnary, Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toRelation,
    Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?,
    Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
    Cst.Primary.toExprOrSpecial?, memberAuxA, memberAux, ExprOrSpecial.toExpr?, Cst.Expr.toAExpr?,
    Option.bind_assoc]

/-- Lifting a CST expr to an `AddExpr` and translating round-trips. -/
theorem toAddExpr_toAExpr (e : Cst.Expr) :
    (Cst.Expr.toAddExpr e).toAExpr? = e.toAExpr? := by
  simp [Cst.Expr.toAddExpr, Cst.Expr.toPrimary, Cst.Primary.toMember,
    Cst.Member.toUnary, Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr,
    Cst.AddExpr.toAExpr?, Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
    Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?, Cst.Primary.toExprOrSpecial?,
    memberAuxA, memberAux, ExprOrSpecial.toExpr?, Cst.Expr.toAExpr?, Option.bind_assoc]

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
  | rInits _ =>
    simp [Cst.Primary.toMultipleEntityUID?] at h
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
        Cst.Unary.toExprOrSpecial?, hop, Cst.Member.toExprOrSpecial?, hacc, memberAuxA, memberAux,
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
    Cst.Primary.toExprOrSpecial?, memberAuxA, memberAux, Expr.bangN, ExprOrSpecial.toExpr?, h]

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
      Cst.Literal.toExprOrSpecial?, memberAuxA, memberAux, ExprOrSpecial.toExpr?]
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
        Cst.Name.toVar?, memberAuxA, memberAux]
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
          Cst.Literal.toExprOrSpecial?, memberAuxA, memberAux, ExprOrSpecial.toExpr?]
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
      Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?, memberAuxA, memberAux]
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
      Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?, memberAuxA, memberAux]
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

/-- `toPolicy?` produces a policy whose `id` field is the CST policy's `id`. -/
theorem toPolicy?_id_eq {cp : Cst.Policy} {ap : Spec.Policy} :
    cp.toPolicy? = some ap → ap.id = cp.id := by
  intro h
  obtain ⟨p⟩ := cp
  simp only [Cst.Policy.toPolicy?, Cst.PolicyImpl.toPolicy?, bind, Option.bind_eq_some_iff,
    Option.some.injEq] at h
  obtain ⟨eff, heff, ⟨ps, as, rs⟩, hsc, conds, hconds, heq⟩ := h
  simp only [← heq, Cst.Policy.id]

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

/-- `Cst.Policies.toPolicies?` relates the original CST policies to the translated
    AST policies pointwise: each CST policy translates (via `toPolicy?`) to the
    corresponding AST policy. The id is carried through by `toPolicy?` itself (see
    `toPolicy?_id_eq`). -/
theorem toPolicies?_forall₂ {cps : Cst.Policies} {aps : Spec.Policies} :
    cps.toPolicies? = some aps →
    List.Forall₂ (fun (cp : Cst.Policy) (ap : Spec.Policy) => cp.toPolicy? = some ap)
      cps.ps aps := by
  simp only [Cst.Policies.toPolicies?]
  generalize cps.ps = ps
  induction ps generalizing aps with
  | nil =>
    intro htrans
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at htrans
    subst htrans
    exact List.Forall₂.nil
  | cons hd tl ih =>
    intro htrans
    simp [List.mapM_cons, Option.bind_eq_some_iff] at htrans
    obtain ⟨a0, ha0, restRets, hrest, hretseq⟩ := htrans
    subst hretseq
    exact List.Forall₂.cons ha0 (ih hrest)
