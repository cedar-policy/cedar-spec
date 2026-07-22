import Cedar.Spec.CstErrorCollector
import Cedar.Thm.Data.Set
import Cedar.Thm.Translation.AuxSound

/-!
Theorems about the CST error collector (`Cedar/Spec/CstErrorCollector.lean`).

A (non-`module`) `Thm` file, so the CST evaluator's definitions and the
`Set` membership lemmas (`Cedar.Data.Set.mem_union`, …) are available.
-/

namespace Cedar.Spec

open Cedar.Data

def Error.isCstError (e : Error) : Bool :=
  match e with
  | .cstError _ => true
  | _           => false

def noCstError (es : Set Error) : Bool :=
  ∀ e ∈ es, ¬ (Error.isCstError e)

theorem noCstError_union (es1 es2 : Set Error) :
    noCstError es1 ∧ noCstError es2 ↔ noCstError (es1 ∪ es2) := by
  simp only [noCstError, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩ e he
    rcases (Set.mem_union es1 es2 e).mp he with h | h
    · exact h1 e h
    · exact h2 e h
  · intro h
    exact ⟨fun e he => h e ((Set.mem_union es1 es2 e).mpr (Or.inl he)),
           fun e he => h e ((Set.mem_union es1 es2 e).mpr (Or.inr he))⟩

theorem noCstError_empty : noCstError (∅ : Set Error) := by
  simp only [noCstError, decide_eq_true_eq]
  intro e he
  exact absurd he (Set.not_mem_empty e)

theorem noCstError_singleton (e : Error) :
    noCstError (Set.singleton e) ↔ e.isCstError = false := by
  simp only [noCstError, decide_eq_true_eq]
  constructor
  · intro h
    have he := h e (Set.mem_singleton_self e)
    simpa using he
  · intro hf x hx
    rw [Set.mem_singleton] at hx
    subst hx
    simp [hf]

theorem noCstError_ofResult (r : Result Value) :
    noCstError (Cst.CollectResult.ofResult r).1 ↔ ∀ e, r = .error e → e.isCstError = false := by
  cases r with
  | ok v =>
    simp only [Cst.CollectResult.ofResult]
    constructor
    · intro _ e he; simp at he
    · intro _; exact noCstError_empty
  | error e =>
    simp only [Cst.CollectResult.ofResult]
    rw [noCstError_singleton]
    simp

-- Helper lemmas

theorem collectExprList_no_cst (xs : List Cst.Expr) (req : Request) (es : Entities) :
    noCstError (Cst.collectExprList xs req es).1 →
    ∀ x ∈ xs, noCstError (x.collectErrors req es).1 := by
  induction xs with
  | nil => intro _ x hx; cases hx
  | cons hd tl ih =>
    intro h x hx
    unfold Cst.collectExprList at h
    obtain ⟨hHd, hTl⟩ := (noCstError_union _ _).mpr h
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hHd
    · exact ih hTl x hmem

theorem collectMults_no_cst (xs : List (Cst.MultOp × Cst.Unary)) (req : Request) (es : Entities) :
    noCstError (Cst.collectMults xs req es) →
    ∀ x ∈ xs, x.1 = .mTimes ∧ noCstError (x.2.collectErrors req es).1 := by
  induction xs with
  | nil => intro _ x hx; cases hx
  | cons hd tl ih =>
    obtain ⟨op, u⟩ := hd
    intro h x hx
    unfold Cst.collectMults at h
    obtain ⟨hAB, hC⟩ := (noCstError_union _ _).mpr h
    obtain ⟨hA, hB⟩ := (noCstError_union _ _).mpr hAB
    have hop : op = .mTimes := by
      cases op with
      | mTimes => rfl
      | _ =>
        rw [noCstError_singleton] at hA
        simp [Error.isCstError] at hA
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact ⟨hop, hB⟩
    · exact ih hC x hmem

theorem collectAdds_no_cst (xs : List (Cst.AddOp × Cst.MultExpr)) (req : Request) (es : Entities) :
    noCstError (Cst.collectAdds xs req es) →
    ∀ x ∈ xs, noCstError (x.2.collectErrors req es).1 := by
  induction xs with
  | nil => intro _ x hx; cases hx
  | cons hd tl ih =>
    obtain ⟨op, m⟩ := hd
    intro h x hx
    unfold Cst.collectAdds at h
    obtain ⟨hHd, hTl⟩ := (noCstError_union _ _).mpr h
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hHd
    · exact ih hTl x hmem

theorem collectRels_no_cst (xs : List (Cst.RelOp × Cst.AddExpr)) (req : Request) (es : Entities) :
    noCstError (Cst.collectRels xs req es) →
    ∀ x ∈ xs, noCstError (x.2.collectErrors req es).1 := by
  induction xs with
  | nil => intro _ x hx; cases hx
  | cons hd tl ih =>
    obtain ⟨op, a⟩ := hd
    intro h x hx
    unfold Cst.collectRels at h
    obtain ⟨hHd, hTl⟩ := (noCstError_union _ _).mpr h
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hHd
    · exact ih hTl x hmem

theorem collectRelations_no_cst (xs : List Cst.Relation) (req : Request) (es : Entities) :
    noCstError (Cst.collectRelations xs req es) →
    ∀ x ∈ xs, noCstError (x.collectErrors req es).1 := by
  induction xs with
  | nil => intro _ x hx; cases hx
  | cons hd tl ih =>
    intro h x hx
    unfold Cst.collectRelations at h
    obtain ⟨hHd, hTl⟩ := (noCstError_union _ _).mpr h
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hHd
    · exact ih hTl x hmem

theorem collectAndExprs_no_cst (xs : List Cst.AndExpr) (req : Request) (es : Entities) :
    noCstError (Cst.collectAndExprs xs req es) →
    ∀ x ∈ xs, noCstError (x.collectErrors req es).1 := by
  induction xs with
  | nil => intro _ x hx; cases hx
  | cons hd tl ih =>
    intro h x hx
    unfold Cst.collectAndExprs at h
    obtain ⟨hHd, hTl⟩ := (noCstError_union _ _).mpr h
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hHd
    · exact ih hTl x hmem

theorem collectRInits_no_cst (r : List Cst.RecInit) (req : Request) (es : Entities) :
    noCstError (Cst.collectRInits r req es) →
    ∀ ri ∈ r, ri.key.toAttr?.isSome ∧ noCstError (ri.value.collectErrors req es).1 := by
  induction r with
  | nil => intro _ ri hri; cases hri
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    intro h ri hri
    unfold Cst.collectRInits at h
    obtain ⟨hAB, hC⟩ := (noCstError_union _ _).mpr h
    obtain ⟨hA, hB⟩ := (noCstError_union _ _).mpr hAB
    have hattr : k.toAttr?.isSome := by
      cases hk : k.toAttr? with
      | some a => simp
      | none => simp [hk, noCstError_singleton, Error.isCstError] at hA
    rcases List.mem_cons.mp hri with rfl | hmem
    · exact ⟨hattr, hB⟩
    · exact ih hC ri hmem

theorem multFoldExtended_complete (xs : List (Cst.MultOp × Cst.Unary)) (acc : Expr)
    (hop : ∀ x ∈ xs, x.1 = .mTimes) (htr : ∀ x ∈ xs, (x.2.toAExpr?).isSome) :
    ∃ result, Cst.MultExpr.foldExtended acc xs = some result := by
  induction xs generalizing acc with
  | nil => exact ⟨acc, by simp [Cst.MultExpr.foldExtended]⟩
  | cons hd tl ih =>
    obtain ⟨op, u⟩ := hd
    have hoph : op = .mTimes := hop (op, u) List.mem_cons_self
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp (htr (op, u) List.mem_cons_self)
    subst hoph
    obtain ⟨result, hresult⟩ := ih (Cedar.Spec.Expr.binaryApp .mul acc ae)
      (fun x hx => hop x (List.mem_cons_of_mem _ hx))
      (fun x hx => htr x (List.mem_cons_of_mem _ hx))
    exact ⟨result, by simp [Cst.MultExpr.foldExtended, hae, hresult]⟩

theorem addFoldExtended_complete (xs : List (Cst.AddOp × Cst.MultExpr)) (acc : Expr)
    (htr : ∀ x ∈ xs, (x.2.toAExpr?).isSome) :
    ∃ result, Cst.AddExpr.foldExtended acc xs = some result := by
  induction xs generalizing acc with
  | nil => exact ⟨acc, by simp [Cst.AddExpr.foldExtended]⟩
  | cons hd tl ih =>
    obtain ⟨op, m⟩ := hd
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp (htr (op, m) List.mem_cons_self)
    have htl := fun x hx => htr x (List.mem_cons_of_mem _ hx)
    cases op with
    | aPlus =>
      obtain ⟨result, hresult⟩ := ih (Cedar.Spec.Expr.binaryApp .add acc ae) htl
      exact ⟨result, by simp [Cst.AddExpr.foldExtended, hae, hresult]⟩
    | aMinus =>
      obtain ⟨result, hresult⟩ := ih (Cedar.Spec.Expr.binaryApp .sub acc ae) htl
      exact ⟨result, by simp [Cst.AddExpr.foldExtended, hae, hresult]⟩

theorem andFoldExtended_complete (xs : List Cst.Relation) (acc : Expr)
    (htr : ∀ x ∈ xs, x.toAExpr?.isSome) :
    ∃ result, Cst.AndExpr.foldExtended acc xs = some result := by
  induction xs generalizing acc with
  | nil => exact ⟨acc, by simp [Cst.AndExpr.foldExtended]⟩
  | cons hd tl ih =>
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp (htr hd List.mem_cons_self)
    obtain ⟨result, hresult⟩ := ih (Cedar.Spec.Expr.and acc ae)
      (fun x hx => htr x (List.mem_cons_of_mem _ hx))
    exact ⟨result, by simp [Cst.AndExpr.foldExtended, hae, hresult]⟩

theorem orFoldExtended_complete (xs : List Cst.AndExpr) (acc : Expr)
    (htr : ∀ x ∈ xs, x.toAExpr?.isSome) :
    ∃ result, Cst.OrExpr.foldExtended acc xs = some result := by
  induction xs generalizing acc with
  | nil => exact ⟨acc, by simp [Cst.OrExpr.foldExtended]⟩
  | cons hd tl ih =>
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp (htr hd List.mem_cons_self)
    obtain ⟨result, hresult⟩ := ih (Cedar.Spec.Expr.or acc ae)
      (fun x hx => htr x (List.mem_cons_of_mem _ hx))
    exact ⟨result, by simp [Cst.OrExpr.foldExtended, hae, hresult]⟩

-- If every element of a list translates, the list translates (`mapM` succeeds).
theorem list_toAExpr_complete (xs : List Cst.Expr)
    (h : ∀ x ∈ xs, x.toAExpr?.isSome) : ∃ aes, xs.mapM (fun x => x.toAExpr?) = some aes := by
  induction xs with
  | nil => exact ⟨[], by simp⟩
  | cons hd tl ih =>
    obtain ⟨ahd, hahd⟩ := Option.isSome_iff_exists.mp (h hd List.mem_cons_self)
    obtain ⟨atl, hatl⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨ahd :: atl, by simp [List.mapM_cons, hahd, hatl]⟩

-- If every record key is a valid attribute and every value translates, the
-- record translates (`rInitsToMap?` succeeds).
theorem rInitsToMap?_complete (r : List Cst.RecInit)
    (h : ∀ ri ∈ r, ri.key.toAttr?.isSome ∧ ri.value.toAExpr?.isSome) :
    ∃ map, rInitsToMap? r = some map := by
  induction r with
  | nil => exact ⟨[], by simp [rInitsToMap?]⟩
  | cons ri rs ih =>
    obtain ⟨hkey, hval⟩ := h ri List.mem_cons_self
    obtain ⟨attr, hattr⟩ := Option.isSome_iff_exists.mp hkey
    have hcons := Cedar.Thm.Cst.Expr.toAttr?_consistent ri.key
    rw [hattr] at hcons
    obtain ⟨eos, heos, hvalid⟩ := Option.bind_eq_some_iff.mp hcons.symm
    obtain ⟨aval, haval⟩ := Option.isSome_iff_exists.mp hval
    obtain ⟨mtl, hmtl⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact ⟨(attr, aval) :: mtl, by simp [rInitsToMap?, heos, hvalid, haval, hmtl]⟩


mutual

theorem Cst.Primary.collect_complete {e : Cst.Primary} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  match e with
  | .expr ex =>
    unfold Cst.Primary.collectErrors at h
    obtain ⟨eos_e, ae, heos_e, hae⟩ := Cst.Expr.collect_complete h
    refine ⟨.expr ae, ae, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp [Cst.Primary.toExprOrSpecial?, Cst.Expr.toAExpr?, heos_e, hae]
  | .eList xs =>
    unfold Cst.Primary.collectErrors at h
    have htr : ∀ x ∈ xs, x.toAExpr?.isSome := by
      intro x hx
      obtain ⟨_, _, heosx, haex⟩ := Cst.Expr.collect_complete (collectExprList_no_cst xs req es h x hx)
      simp [Cst.Expr.toAExpr?, heosx, haex]
    obtain ⟨aes, haes⟩ := list_toAExpr_complete xs htr
    refine ⟨.expr (.set aes), .set aes, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp [Cst.Primary.toExprOrSpecial?, List.mapM₁_eq_mapM (fun x : Cst.Expr => x.toAExpr?), haes]
  | .rInits r =>
    unfold Cst.Primary.collectErrors at h
    have htr : ∀ ri ∈ r, ri.key.toAttr?.isSome ∧ ri.value.toAExpr?.isSome := by
      intro ri hri
      obtain ⟨hkey, hval⟩ := collectRInits_no_cst r req es h ri hri
      refine ⟨hkey, ?_⟩
      obtain ⟨_, _, heosv, haev⟩ := Cst.Expr.collect_complete hval
      simp [Cst.Expr.toAExpr?, heosv, haev]
    obtain ⟨map, hmap⟩ := rInitsToMap?_complete r htr
    refine ⟨.expr (.record map), .record map, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp [Cst.Primary.toExprOrSpecial?, hmap]
  | .literal l =>
    unfold Cst.Primary.collectErrors at h
    have hev := (noCstError_ofResult _).mp h
    cases l with
    | liTrue =>
      exact ⟨.boolLit true, .lit (.bool true),
             by simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?],
             by simp [ExprOrSpecial.toExpr?]⟩
    | liFalse =>
      exact ⟨.boolLit false, .lit (.bool false),
             by simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?],
             by simp [ExprOrSpecial.toExpr?]⟩
    | liNum n =>
      cases hn : Int64.ofInt? (n.toNat) with
      | none =>
        exfalso
        have := hev (.cstError .primaryOverflowError) (by simp [Cst.Primary.evaluate, hn])
        simp [Error.isCstError] at this
      | some i =>
        refine ⟨.expr (.lit (.int i)), .lit (.int i), ?_, by simp [ExprOrSpecial.toExpr?]⟩
        simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?, hn]
    | liStr s =>
      cases hs : CstCommon.unescape? s with
      | none =>
        exfalso
        have := hev (.cstError .stringError)
          (by simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString, hs])
        simp [Error.isCstError] at this
      | some s' =>
        refine ⟨.strLit s, .lit (.string s'),
                by simp [Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?], ?_⟩
        simp [ExprOrSpecial.toExpr?, hs]
  | .name n =>
    unfold Cst.Primary.collectErrors at h
    have hev := (noCstError_ofResult _).mp h
    cases hvar : n.toVar? with
    | some var =>
      exact ⟨.var var, .var var, by simp [Cst.Primary.toExprOrSpecial?, hvar],
             by simp [ExprOrSpecial.toExpr?]⟩
    | none =>
      exfalso
      have hce : (Cst.Primary.name n).evaluate req es = .error (.cstError .nameError) := by
        obtain ⟨npath, nname⟩ := n
        simp only [Cst.Name.toVar?] at hvar
        cases hpath : npath with
        | nil => cases nname <;> simp_all [Cst.Primary.evaluate, Cst.Name.toVar?]
        | cons hd tl => simp [Cst.Primary.evaluate, hpath]
      have := hev _ hce
      simp [Error.isCstError] at this
  | .ref r =>
    unfold Cst.Primary.collectErrors at h
    have hev := (noCstError_ofResult _).mp h
    cases r with
    | uid path eid =>
      match eid with
      | .string s =>
        cases hs : CstCommon.unescape? s with
        | none =>
          exfalso
          have := hev (.cstError .stringError)
            (by simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString, hs])
          simp [Error.isCstError] at this
        | some s' =>
          cases hty : CstCommon.Name.toAName? path with
          | none =>
            exfalso
            have := hev (.cstError .unsupportedError)
              (by simp [Cst.Primary.evaluate, Cst.Str.toUnescapedString, hs, hty])
            simp [Error.isCstError] at this
          | some ty =>
            refine ⟨.expr (.lit (.entityUID ⟨ty, s'⟩)), .lit (.entityUID ⟨ty, s'⟩), ?_,
                    by simp [ExprOrSpecial.toExpr?]⟩
            simp [Cst.Primary.toExprOrSpecial?, Cst.Ref.toExprOrSpecial?, Cst.Name.toAName?, hty, hs]
    | ref path rinits =>
      exfalso
      have := hev (.cstError .unsupportedError) (by simp [Cst.Primary.evaluate])
      simp [Error.isCstError] at this
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [Cst.Primary.expr.sizeOf_spec] at *; omega)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem;
       simp only [Cst.Primary.eList.sizeOf_spec] at *; omega)
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; cases ‹Cst.RecInit›;
       simp only [Cst.Primary.rInits.sizeOf_spec, Cst.RecInit.mk.sizeOf_spec] at *; omega)

theorem Cst.Member.collectAccessors_complete
    (head : Option Value) (accs : List Cst.MemAccess) {req : Request} {es : Entities} :
    noCstError (Cst.Member.collectAccessors head accs req es).1 →
    ∃ accs_ast, accs.mapM Cst.MemAccess.toAstAccessor? = some accs_ast ∧
      (∀ cargs t, accs_ast ≠ AstAccessor.call cargs :: t) ∧
      ∀ he : Cedar.Spec.Expr, ∃ r, memberAuxB he accs_ast = some r := by
  intro h; sorry

theorem Cst.Member.collect_complete {e : Cst.Member} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h; sorry

theorem Cst.Unary.collect_complete {e : Cst.Unary} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  unfold Cst.Unary.collectErrors at h
  obtain ⟨hev, hitem⟩ := (noCstError_union _ _).mpr h
  obtain ⟨eos_i, ae_i, heos_i, hae_i⟩ := Cst.Member.collect_complete hitem
  match hop : e.op with
  | none =>
    exact ⟨eos_i, ae_i, by simp [Cst.Unary.toExprOrSpecial?, hop, heos_i], hae_i⟩
  | some (.nBang n) =>
    exact ⟨.expr (ae_i.bangN n.toNat), ae_i.bangN n.toNat,
           by simp [Cst.Unary.toExprOrSpecial?, hop, heos_i, hae_i],
           by simp [ExprOrSpecial.toExpr?]⟩
  | some (.nDash n) =>
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨eos_i, ae_i, by simp [Cst.Unary.toExprOrSpecial?, hop, heos_i], hae_i⟩
    · match hlit : CstCommon.Member.toLit? e.item with
      | some (.liNum x) =>
        -- Provable: an overflowing negative literal has its magnitude `x`
        -- overflow `Int64` too, so `e.item.collectErrors` carries
        -- `primaryOverflowError`; needs a `toLit?`↔`toExprOrSpecial?` bridge.
        sorry
      | some .liTrue | some .liFalse | some (.liStr _) | none =>
        refine ⟨.expr (ae_i.dashN n.toNat), ae_i.dashN n.toNat, ?_, by simp [ExprOrSpecial.toExpr?]⟩
        simp [Cst.Unary.toExprOrSpecial?, hop, hn0, hlit, heos_i, hae_i]
  | some .nOverBang =>
    exfalso
    have hce := (noCstError_ofResult _).mp hev
    have := hce (.cstError .unsupportedError) (by simp [Cst.Unary.evaluate, hop])
    simp [Error.isCstError] at this
  | some .nOverDash =>
    exfalso
    have hce := (noCstError_ofResult _).mp hev
    have := hce (.cstError .unsupportedError) (by simp [Cst.Unary.evaluate, hop])
    simp [Error.isCstError] at this
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf; omega)

theorem Cst.MultExpr.collect_complete {e : Cst.MultExpr} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  unfold Cst.MultExpr.collectErrors at h
  obtain ⟨hei, hMul⟩ := (noCstError_union _ _).mpr h
  obtain ⟨_, hinit⟩ := (noCstError_union _ _).mpr hei
  obtain ⟨eos_i, ae_i, heos_i, hae_i⟩ := Cst.Unary.collect_complete hinit
  match hext : e.extended with
  | [] =>
    refine ⟨eos_i, ae_i, ?_, hae_i⟩
    simp [Cst.MultExpr.toExprOrSpecial?, hext, heos_i]
  | hd :: tl =>
    have hinitA : e.initial.toAExpr? = some ae_i := by simp [Cst.Unary.toAExpr?, heos_i, hae_i]
    have hop : ∀ x ∈ e.extended, x.1 = Cst.MultOp.mTimes :=
      fun x hx => (collectMults_no_cst e.extended req es hMul x hx).1
    have htr : ∀ x ∈ e.extended, x.2.toAExpr?.isSome := by
      intro x hx
      obtain ⟨_, _, heosx, haex⟩ :=
        Cst.Unary.collect_complete (collectMults_no_cst e.extended req es hMul x hx).2
      simp [Cst.Unary.toAExpr?, heosx, haex]
    obtain ⟨result, hresult⟩ := multFoldExtended_complete e.extended ae_i hop htr
    refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp only [hext] at hresult
    simp [Cst.MultExpr.toExprOrSpecial?, hext, hinitA, hresult]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (cases e; simp only [Cst.MultExpr.mk.sizeOf_spec] at *)
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem;
       simp only [Prod.mk.sizeOf_spec] at *; omega)

theorem Cst.AddExpr.collect_complete {e : Cst.AddExpr} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  unfold Cst.AddExpr.collectErrors at h
  obtain ⟨hei, hAdd⟩ := (noCstError_union _ _).mpr h
  obtain ⟨_, hinit⟩ := (noCstError_union _ _).mpr hei
  obtain ⟨eos_i, ae_i, heos_i, hae_i⟩ := Cst.MultExpr.collect_complete hinit
  match hext : e.extended with
  | [] =>
    refine ⟨eos_i, ae_i, ?_, hae_i⟩
    simp [Cst.AddExpr.toExprOrSpecial?, hext, heos_i]
  | hd :: tl =>
    have hinitA : e.initial.toAExpr? = some ae_i := by simp [Cst.MultExpr.toAExpr?, heos_i, hae_i]
    have htr : ∀ x ∈ e.extended, x.2.toAExpr?.isSome := by
      intro x hx
      obtain ⟨_, _, heosx, haex⟩ :=
        Cst.MultExpr.collect_complete (collectAdds_no_cst e.extended req es hAdd x hx)
      simp [Cst.MultExpr.toAExpr?, heosx, haex]
    obtain ⟨result, hresult⟩ := addFoldExtended_complete e.extended ae_i htr
    refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp only [hext] at hresult
    simp [Cst.AddExpr.toExprOrSpecial?, hext, hinitA, hresult]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (cases e; simp only [Cst.AddExpr.mk.sizeOf_spec] at *)
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem;
       simp only [Prod.mk.sizeOf_spec] at *; omega)

theorem Cst.Relation.collect_complete {e : Cst.Relation} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  match e with
  | .rCommon initial extended =>
    unfold Cst.Relation.collectErrors at h
    obtain ⟨hev, herrs⟩ := (noCstError_union _ _).mpr h
    obtain ⟨hinit, hrels⟩ := (noCstError_union _ _).mpr herrs
    obtain ⟨eos_i, ae_i, heos_i, hae_i⟩ := Cst.AddExpr.collect_complete hinit
    match hext : extended with
    | [] =>
      exact ⟨eos_i, ae_i, by simp [Cst.Relation.toExprOrSpecial?, hext, heos_i], hae_i⟩
    | (op, y) :: rest =>
      match hrest : rest with
      | _ :: _ =>
        exfalso
        have := (noCstError_ofResult _).mp hev (.cstError .unsupportedError)
          (by simp [Cst.Relation.evaluate, hext, hrest])
        simp [Error.isCstError] at this
      | [] =>
        have hyA : y.toAExpr?.isSome := by
          obtain ⟨_, _, hyeos, hyae⟩ :=
            Cst.AddExpr.collect_complete
              (collectRels_no_cst _ req es hrels (op, y) List.mem_cons_self)
          simp [Cst.AddExpr.toAExpr?, hyeos, hyae]
        obtain ⟨yexpr, hyexpr⟩ := Option.isSome_iff_exists.mp hyA
        refine ⟨.expr (constructExprRel op ae_i yexpr), constructExprRel op ae_i yexpr, ?_,
                by simp [ExprOrSpecial.toExpr?]⟩
        simp [Cst.Relation.toExprOrSpecial?, hext, hrest, heos_i, hae_i, hyexpr]
  | .rHas target field =>
    unfold Cst.Relation.collectErrors at h
    obtain ⟨hev, herrs⟩ := (noCstError_union _ _).mpr h
    obtain ⟨htgt, hattr⟩ := (noCstError_union _ _).mpr herrs
    obtain ⟨teos, texpr, hteos, htexpr⟩ := Cst.AddExpr.collect_complete htgt
    have htgtA : target.toAExpr? = some texpr := by simp [Cst.AddExpr.toAExpr?, hteos, htexpr]
    have hfa : ∃ a as, field.toAttrs? = some (a :: as) := by
      cases hf : field.toAttrs? with
      | none => simp [hf, noCstError_singleton, Error.isCstError] at hattr
      | some l =>
        cases l with
        | nil => simp [hf, noCstError_singleton, Error.isCstError] at hattr
        | cons a as => exact ⟨a, as, rfl⟩
    obtain ⟨a, as, hfa⟩ := hfa
    obtain ⟨rhs, hrhs⟩ := Cedar.Thm.addExpr_toAttrs_toHasRhs hfa
    cases rhs with
    | inl fld =>
      exact ⟨.expr (.hasAttr texpr fld), .hasAttr texpr fld,
             by simp [Cst.Relation.toExprOrSpecial?, htgtA, hrhs], by simp [ExprOrSpecial.toExpr?]⟩
    | inr fs =>
      exact ⟨.expr (extendedHasAttr texpr fs), extendedHasAttr texpr fs,
             by simp [Cst.Relation.toExprOrSpecial?, htgtA, hrhs], by simp [ExprOrSpecial.toExpr?]⟩
  | .rLike target pattern =>
    unfold Cst.Relation.collectErrors at h
    obtain ⟨hev, herrs⟩ := (noCstError_union _ _).mpr h
    obtain ⟨htgt, hpat⟩ := (noCstError_union _ _).mpr herrs
    obtain ⟨teos, texpr, hteos, htexpr⟩ := Cst.AddExpr.collect_complete htgt
    have htgtA : target.toAExpr? = some texpr := by simp [Cst.AddExpr.toAExpr?, hteos, htexpr]
    cases hps : pattern.toPatternString? with
    | none => simp [hps, noCstError_singleton, Error.isCstError] at hpat
    | some s =>
      cases hcp : CstCommon.toPattern? s with
      | none => simp [hps, hcp, noCstError_singleton, Error.isCstError] at hpat
      | some mp =>
        have hpatT : pattern.toPattern? = some mp := by
          simp [Cst.AddExpr.toPattern?, Cedar.Thm.addExpr_toPatternString_toExprOrSpecial hps, hcp]
        exact ⟨.expr (.unaryApp (.like mp) texpr), .unaryApp (.like mp) texpr,
               by simp [Cst.Relation.toExprOrSpecial?, htgtA, hpatT], by simp [ExprOrSpecial.toExpr?]⟩
  | .rIsIn target ety inEntity =>
    unfold Cst.Relation.collectErrors at h
    obtain ⟨hev, herrs⟩ := (noCstError_union _ _).mpr h
    obtain ⟨hte, hInE⟩ := (noCstError_union _ _).mpr herrs
    obtain ⟨htgt, hety⟩ := (noCstError_union _ _).mpr hte
    obtain ⟨teos, texpr, hteos, htexpr⟩ := Cst.AddExpr.collect_complete htgt
    have htgtA : target.toAExpr? = some texpr := by simp [Cst.AddExpr.toAExpr?, hteos, htexpr]
    cases hety' : ety.toEntityType? with
    | none => simp [hety', noCstError_singleton, Error.isCstError] at hety
    | some etyName =>
      match hinE : inEntity with
      | none =>
        exact ⟨.expr (.unaryApp (.is etyName) texpr), .unaryApp (.is etyName) texpr,
               by simp [Cst.Relation.toExprOrSpecial?, htgtA, hety'], by simp [ExprOrSpecial.toExpr?]⟩
      | some ie =>
        cases hie : ie.toAExpr? with
        | none =>
          exfalso
          simp only [hie, Option.isNone_none, if_true] at hInE
          obtain ⟨_, hg⟩ := (noCstError_union _ _).mpr hInE
          rw [noCstError_singleton] at hg
          simp [Error.isCstError] at hg
        | some mi =>
          exact ⟨.expr (.and (.unaryApp (.is etyName) texpr) (.binaryApp .mem texpr mi)),
                 .and (.unaryApp (.is etyName) texpr) (.binaryApp .mem texpr mi),
                 by simp [Cst.Relation.toExprOrSpecial?, htgtA, hety', hie], by simp [ExprOrSpecial.toExpr?]⟩
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem;
       simp only [Prod.mk.sizeOf_spec] at *; omega))

theorem Cst.AndExpr.collect_complete {e : Cst.AndExpr} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  unfold Cst.AndExpr.collectErrors at h
  obtain ⟨hei, hRel⟩ := (noCstError_union _ _).mpr h
  obtain ⟨_, hinit⟩ := (noCstError_union _ _).mpr hei
  obtain ⟨eos_i, ae_i, heos_i, hae_i⟩ := Cst.Relation.collect_complete hinit
  match hext : e.extended with
  | [] =>
    refine ⟨eos_i, ae_i, ?_, hae_i⟩
    simp [Cst.AndExpr.toExprOrSpecial?, hext, heos_i]
  | hd :: tl =>
    have hinitA : e.initial.toAExpr? = some ae_i := by simp [Cst.Relation.toAExpr?, heos_i, hae_i]
    have htr : ∀ x ∈ e.extended, x.toAExpr?.isSome := by
      intro x hx
      obtain ⟨_, _, heosx, haex⟩ :=
        Cst.Relation.collect_complete (collectRelations_no_cst e.extended req es hRel x hx)
      simp [Cst.Relation.toAExpr?, heosx, haex]
    obtain ⟨result, hresult⟩ := andFoldExtended_complete e.extended ae_i htr
    refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp only [hext] at hresult
    simp [Cst.AndExpr.toExprOrSpecial?, hext, hinitA, hresult]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (cases e; simp only [Cst.AndExpr.mk.sizeOf_spec] at *)
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)

theorem Cst.OrExpr.collect_complete {e : Cst.OrExpr} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  unfold Cst.OrExpr.collectErrors at h
  obtain ⟨hei, hAnd⟩ := (noCstError_union _ _).mpr h
  obtain ⟨_, hinit⟩ := (noCstError_union _ _).mpr hei
  obtain ⟨eos_i, ae_i, heos_i, hae_i⟩ := Cst.AndExpr.collect_complete hinit
  match hext : e.extended with
  | [] =>
    refine ⟨eos_i, ae_i, ?_, hae_i⟩
    simp [Cst.OrExpr.toExprOrSpecial?, hext, heos_i]
  | hd :: tl =>
    have hinitA : e.initial.toAExpr? = some ae_i := by simp [Cst.AndExpr.toAExpr?, heos_i, hae_i]
    have htr : ∀ x ∈ e.extended, x.toAExpr?.isSome := by
      intro x hx
      obtain ⟨_, _, heosx, haex⟩ :=
        Cst.AndExpr.collect_complete (collectAndExprs_no_cst e.extended req es hAnd x hx)
      simp [Cst.AndExpr.toAExpr?, heosx, haex]
    obtain ⟨result, hresult⟩ := orFoldExtended_complete e.extended ae_i htr
    refine ⟨.expr result, result, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    simp only [hext] at hresult
    simp [Cst.OrExpr.toExprOrSpecial?, hext, hinitA, hresult]
termination_by sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals (cases e; simp only [Cst.OrExpr.mk.sizeOf_spec] at *)
  all_goals first
    | omega
    | (rename_i hmem; have := List.sizeOf_lt_of_mem hmem; omega)

theorem Cst.ExprData.collect_complete {e : Cst.ExprData} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  match e with
  | .edOr oe =>
    unfold Cst.ExprData.collectErrors at h
    obtain ⟨_, hoe⟩ := (noCstError_union _ _).mpr h
    unfold Cst.ExprData.toExprOrSpecial?
    exact Cst.OrExpr.collect_complete hoe
  | .edIf i t f =>
    unfold Cst.ExprData.collectErrors at h
    obtain ⟨_, herrs⟩ := (noCstError_union _ _).mpr h
    obtain ⟨hit, hf⟩ := (noCstError_union _ _).mpr herrs
    obtain ⟨hi, ht⟩ := (noCstError_union _ _).mpr hit
    obtain ⟨eos_i, ae_i, heos_i, hae_i⟩ := Cst.Expr.collect_complete hi
    obtain ⟨eos_t, ae_t, heos_t, hae_t⟩ := Cst.Expr.collect_complete ht
    obtain ⟨eos_f, ae_f, heos_f, hae_f⟩ := Cst.Expr.collect_complete hf
    refine ⟨.expr (.ite ae_i ae_t ae_f), .ite ae_i ae_t ae_f, ?_, by simp [ExprOrSpecial.toExpr?]⟩
    unfold Cst.ExprData.toExprOrSpecial?
    simp [Cst.Expr.toAExpr?, heos_i, hae_i, heos_t, hae_t, heos_f, hae_f]
termination_by sizeOf e
decreasing_by all_goals (simp_wf; try omega)

theorem Cst.ExprImpl.collect_complete {e : Cst.ExprImpl} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  unfold Cst.ExprImpl.collectErrors at h
  unfold Cst.ExprImpl.toExprOrSpecial?
  exact Cst.ExprData.collect_complete h
termination_by sizeOf e
decreasing_by all_goals (cases e; simp_wf)

theorem Cst.Expr.collect_complete {e : Cst.Expr} {req : Request} {es : Entities} :
    noCstError (e.collectErrors req es).1 →
    ∃ eos ae, e.toExprOrSpecial? = some eos ∧ eos.toExpr? = some ae := by
  intro h
  match e with
  | .expr ei =>
    unfold Cst.Expr.collectErrors at h
    unfold Cst.Expr.toExprOrSpecial?
    exact Cst.ExprImpl.collect_complete h
termination_by sizeOf e
decreasing_by all_goals simp_wf

end

end Cedar.Spec
