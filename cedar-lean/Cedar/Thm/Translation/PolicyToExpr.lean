import Cedar.Spec
import Cedar.Spec.Cst
import Cedar.Spec.CstSemantics
import Cedar.Spec.CstToAst
import Cedar.Thm.Translation.Aux
import Cedar.Thm.Data.List.Lemmas
import Cedar.Thm.Data.Set
import Cedar.Thm.Data.List.Canonical

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec

/-! ## Proof structure for `policy_to_expr_agrees`

Both translation paths are rearrangements of a left-folded AST conjunction over
a common leaf list `[principalScope, actionScope, resourceScope, conds…]`. The
proof factors into four layers:
  A. generic algebra of AST `.and` (path-independent),
  B. path 1 translation  (`Cst` `foldAnd` → `bigAnd`),
  C. path 2 normalization (`Policy.toExpr` → `bigAnd`),
  D. per-leaf semantic agreement.
The main theorem just composes them. All proofs are `sorry` for now. -/

/- ===== Layer A: algebra of AST conjunction ===== -/

/-- Left-nested AST conjunction; the common normal form for both paths. -/
def bigAnd (a : Expr) (rest : List Expr) : Expr :=
  rest.foldl (fun acc e => acc.and e) a

/-- Normal form of evaluating an AST `.and`. -/
theorem evaluate_and_eq (x y : Expr) (req : Request) (es : Entities) :
    evaluate (.and x y) req es =
    match (evaluate x req es).as Bool with
    | .error e => .error e
    | .ok false => .ok (.prim (.bool false))
    | .ok true => (evaluate y req es).as Bool := by
  simp only [evaluate]
  cases h : (evaluate x req es).as Bool with
  | error e => simp [bind, Except.bind]
  | ok b => cases b <;> simp [bind, Except.bind]

/-- Re-coercing a bool-wrapped result back through `.as Bool` is the identity. -/
theorem as_bool_map (r : Result Bool) :
    (Result.as Bool do let a ← r; pure (Value.prim (Prim.bool a))) = r := by
  cases r <;> simp [Result.as, Coe.coe, Value.asBool, bind, Except.bind, pure, Except.pure]

/-- `.and` is associative over the full evaluation `Result` (incl. error and
    short-circuit behavior). This is what makes left- vs right-nesting agree. -/
theorem evaluate_and_assoc (a b c : Expr) (req : Request) (es : Entities) :
    evaluate (.and (.and a b) c) req es = evaluate (.and a (.and b c)) req es := by
  rw [evaluate_and_eq (.and a b) c, evaluate_and_eq a b,
      evaluate_and_eq a (.and b c), evaluate_and_eq b c]
  cases ha : (evaluate a req es).as Bool with
  | error e => simp [Result.as]
  | ok ba =>
    cases ba with
    | false => simp [Result.as, Coe.coe, Value.asBool]
    | true =>
      cases hb : (evaluate b req es).as Bool with
      | error e => simp [Result.as, bind, Except.bind]
      | ok bb =>
        cases bb with
        | false => simp [Result.as, Coe.coe, Value.asBool, bind, Except.bind, pure, Except.pure]
        | true =>
          cases hc : (evaluate c req es).as Bool <;>
            simp [Result.as, Coe.coe, Value.asBool, bind, Except.bind, pure, Except.pure]

/-- `x` only ever evaluates to a bool or an error (true for every scope expr). -/
def Boolish (x : Expr) (req : Request) (es : Entities) : Prop :=
  ∀ v, evaluate x req es = .ok v → ∃ b : Bool, v = .prim (.bool b)

/-- Right identity `… ∧ true ≡ …` on boolish exprs (the empty-conditions case). -/
theorem evaluate_and_true (x : Expr) (req : Request) (es : Entities) :
    Boolish x req es →
    evaluate (.and x (.lit (.bool true))) req es = evaluate x req es := by
  intro h
  rw [evaluate_and_eq]
  cases hx : evaluate x req es with
  | error e => simp [Result.as]
  | ok v =>
    obtain ⟨b, rfl⟩ := h v hx
    cases b <;>
      simp [Result.as, Coe.coe, Value.asBool, Functor.map, Except.map, evaluate]

/-- Pointwise-equal leaves ⇒ equal conjunction evaluation. -/
theorem bigAnd_congr (a a' : Expr) (l l' : List Expr) (req : Request) (es : Entities) :
    evaluate a req es = evaluate a' req es →
    List.Forall₂ (fun e e' => evaluate e req es = evaluate e' req es) l l' →
    evaluate (bigAnd a l) req es = evaluate (bigAnd a' l') req es := by
  intro ha h
  induction h generalizing a a' with
  | nil => simpa [bigAnd] using ha
  | cons hr _ ih =>
    simp only [bigAnd, List.foldl_cons]
    apply ih
    rw [evaluate_and_eq, evaluate_and_eq, ha, hr]

/- ===== Layer B: path 1 translation (`foldAnd` → `bigAnd`) ===== -/

/-- `AndExpr.foldExtended` over lifted relations is exactly `bigAnd`. -/
theorem foldExtended_eq_bigAnd (acc : Expr) (l : List Cst.Expr) (aes : List Expr) :
    l.mapM Cst.Expr.toAExpr? = some aes →
    Cst.AndExpr.foldExtended acc (l.map Cst.Expr.toRelation) = some (bigAnd acc aes) := by
  induction l generalizing acc aes with
  | nil =>
    intro h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [Cst.AndExpr.foldExtended, bigAnd]
  | cons e es ih =>
    intro h
    simp [List.mapM_cons, Option.bind_eq_some_iff] at h
    obtain ⟨ahead, hhead, atl, htl, heq⟩ := h
    subst heq
    have hih := ih (acc.and ahead) atl htl
    simp only [List.map_cons, Cst.AndExpr.foldExtended, toRelation_toAExpr, hhead, bind,
      Option.bind, hih, bigAnd, List.foldl_cons]

/-- Translating a CST `foldAnd` yields the `bigAnd` of the translated leaves. -/
theorem foldAnd_toAExpr (l : List Cst.Expr) (as : List Expr) :
    l.mapM Cst.Expr.toAExpr? = some as →
    (Cst.Expr.foldAnd l).toAExpr? =
      some (match as with
            | []        => .lit (.bool true)
            | a :: rest => bigAnd a rest) := by
  intro h
  cases l with
  | nil =>
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    simp [Cst.Expr.foldAnd, Cst.Expr.tt, Cst.Primary.toMember, Cst.Member.toUnary,
      Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toRelation, Cst.Relation.toAndExpr,
      Cst.AndExpr.toOrExpr, Cst.OrExpr.toExpr, Cst.Expr.toAExpr?, Cst.Expr.toExprOrSpecial?,
      Cst.ExprImpl.toExprOrSpecial?, Cst.ExprData.toExprOrSpecial?, Cst.OrExpr.toExprOrSpecial?,
      Cst.AndExpr.toExprOrSpecial?, Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?,
      Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
      Cst.Primary.toExprOrSpecial?, Cst.Literal.toExprOrSpecial?, memberAux, ExprOrSpecial.toExpr?]
  | cons e tl =>
    cases tl with
    | nil =>
      cases hhead : e.toAExpr? with
      | none => simp [List.mapM_cons, hhead] at h
      | some ahead =>
        simp [List.mapM_cons, List.mapM_nil, hhead] at h
        subst h
        simp [Cst.Expr.foldAnd, hhead, bigAnd]
    | cons f es =>
      rw [List.mapM_cons] at h
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨ahead, hhead, atl, htl, heq⟩ := h
      subst heq
      have htl' : (f :: es).mapM Cst.Expr.toAExpr? = some atl := by
        simp [List.mapM_cons, Option.bind_eq_some_iff]; exact htl
      have hfold := foldExtended_eq_bigAnd ahead (f :: es) atl htl'
      simp only [List.map_cons] at hfold
      simp [Cst.Expr.foldAnd, Cst.AndExpr.toOrExpr, Cst.OrExpr.toExpr,
        Cst.Expr.toAExpr?, Cst.Expr.toExprOrSpecial?, Cst.ExprImpl.toExprOrSpecial?,
        Cst.ExprData.toExprOrSpecial?, Cst.OrExpr.toExprOrSpecial?, Cst.AndExpr.toExprOrSpecial?,
        toRelation_toAExpr, hhead, hfold, ExprOrSpecial.toExpr?]

/- ===== Layer C: path 2 normalization (`Policy.toExpr` → `bigAnd`) ===== -/

/-- Head-recursion for `Conditions.toExpr` (which is defined via a reverse-fold). -/
theorem conditions_toExpr_cons (c : Condition) (cs : Conditions) :
    Conditions.toExpr (c :: cs) =
    match cs with
    | [] => c.toExpr
    | _  => c.toExpr.and (Conditions.toExpr cs) := by
  cases hrev : cs.reverse with
  | nil =>
    have hcs : cs = [] := by have := congrArg List.reverse hrev; simpa using this
    subst hcs; simp [Conditions.toExpr]
  | cons e t =>
    obtain ⟨hd, tl, rfl⟩ : ∃ hd tl, cs = hd :: tl := by
      cases cs with
      | nil => simp at hrev
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    simp only [Conditions.toExpr, List.reverse_cons, hrev, List.cons_append,
      List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- Any AST `.and` only ever evaluates to a bool or an error. -/
theorem and_Boolish (x y : Expr) (req : Request) (es : Entities) :
    Boolish (Expr.and x y) req es := by
  intro v hv
  rw [evaluate_and_eq] at hv
  split at hv
  · simp at hv
  · exact ⟨false, by simp_all⟩
  · cases hy : (evaluate y req es).as Bool with
    | error e => rw [hy] at hv; simp [bind, Except.bind] at hv
    | ok a =>
      rw [hy] at hv
      simp [bind, Except.bind, pure, Except.pure] at hv
      exact ⟨a, hv.symm⟩

/-- Flatten a trailing `Conditions.toExpr` into the left-folded `bigAnd`. -/
theorem cond_flatten (acc : Expr) (cs : Conditions) (req : Request) (es : Entities)
    (hb : Boolish acc req es) :
    evaluate (acc.and (Conditions.toExpr cs)) req es =
    evaluate (bigAnd acc (cs.map Condition.toExpr)) req es := by
  induction cs generalizing acc with
  | nil =>
    simp only [Conditions.toExpr, List.reverse_nil, List.map_nil, bigAnd, List.foldl_nil]
    exact evaluate_and_true acc req es hb
  | cons c cs' ih =>
    cases cs' with
    | nil => rw [conditions_toExpr_cons]; simp [bigAnd]
    | cons d ds =>
      rw [conditions_toExpr_cons]
      dsimp only
      rw [← evaluate_and_assoc, ih (acc.and c.toExpr) (and_Boolish acc c.toExpr req es)]
      simp [bigAnd, List.map_cons]

/-- `Policy.toExpr` evaluates as `bigAnd` over its flattened leaves. Uses
    `evaluate_and_assoc` for the fixed nesting / condition flattening, and
    `evaluate_and_true` (with `Boolish` of the resource-scope leaf) to drop the
    trailing `true` when `condition = []`. -/
theorem evaluate_policy_toExpr (ap : Policy) (req : Request) (es : Entities) :
    evaluate ap.toExpr req es =
    evaluate (bigAnd ap.principalScope.toExpr
               (ap.actionScope.toExpr :: ap.resourceScope.toExpr ::
                ap.condition.map Condition.toExpr)) req es := by
  unfold Policy.toExpr
  rw [← evaluate_and_assoc]
  rw [← evaluate_and_assoc]
  rw [cond_flatten _ ap.condition req es (and_Boolish _ _ req es)]
  simp [bigAnd]

/- ===== Layer D: per-leaf agreement ===== -/

/-- Singleton-set membership ≡ bare-entity membership (action-scope `in uid`). -/
theorem evaluate_mem_singleton (v : Var) (uid : EntityUID) (req : Request) (es : Entities) :
    ∀ val, evaluate (.binaryApp .mem (.var v) (.set [.lit (.entityUID uid)])) req es = .ok val ↔
           evaluate (.binaryApp .mem (.var v) (.lit (.entityUID uid))) req es = .ok val := by
  have hels : (Set.make [Value.prim (Prim.entityUID uid)]).elts = [Value.prim (Prim.entityUID uid)] := by
    simp [Set.make, Set.elts, List.canonicalize_singleton]
  have key : ∀ val1 : Value,
      apply₂ .mem val1 (.set (Set.make [.prim (.entityUID uid)])) es
      = apply₂ .mem val1 (.prim (.entityUID uid)) es := by
    intro val1
    cases val1 with
    | prim p =>
      cases p with
      | entityUID a =>
        have huids : (Set.make [uid]).elts = [uid] := by
          simp [Set.make, Set.elts, List.canonicalize_singleton]
        simp only [apply₂, inₛ, Set.mapOrErr, hels, List.mapM_cons, List.mapM_nil,
          Value.asEntityUID, bind, Except.bind, pure, Except.pure, Set.any, huids, List.any,
          Bool.or_false]
      | _ => simp [apply₂]
    | _ => simp [apply₂]
  have heq : evaluate (.binaryApp .mem (.var v) (.set [.lit (.entityUID uid)])) req es =
             evaluate (.binaryApp .mem (.var v) (.lit (.entityUID uid))) req es := by
    simp only [evaluate, List.mapM₁_eq_mapM (fun e => evaluate e req es), List.mapM_cons,
      List.mapM_nil, bind, Except.bind, pure, Except.pure, key]
  intro val; rw [heq]

/-- `toEntityUID?` agrees with the AST translation on the produced literal. -/
theorem toEntityUID_toAExpr {e : Cst.Expr} {uid : EntityUID} :
    e.toEntityUID? = some uid → e.toAExpr? = some (.lit (.entityUID uid)) := by
  intro h
  simp [Cst.Expr.toEntityUID?, Option.bind_eq_some_iff] at h
  obtain ⟨erefs, herefs, hmatch⟩ := h
  cases erefs with
  | inl eref => simp only [Option.some.injEq] at hmatch; subst hmatch; exact expr_mem_toAExpr herefs
  | inr _ => simp at hmatch

/-- Shared core: the principal/resource leaf equals `Scope.toExpr scope v`,
    given the scope variable translates to `Expr.var v`. -/
theorem toPRScope_leaf {vd : Cst.VariableDef} {scope : Scope} {leaf : Expr} {v : Var}
    (hv : (vd.var.varToAddExpr).toExprOrSpecial? = some (ExprOrSpecial.var v))
    (hscope : vd.toPRScope? = some scope)
    (hleaf : vd.toExpr.toAExpr? = some leaf) :
    leaf = Scope.toExpr scope v := by
  have collapse : ∀ r : Cst.Relation,
      ({initial := r, extended := []} : Cst.AndExpr).toOrExpr.toExpr.toAExpr? = r.toAExpr? := by
    intro r
    simp [Cst.AndExpr.toOrExpr, Cst.OrExpr.toExpr, Cst.Expr.toAExpr?, Cst.Expr.toExprOrSpecial?,
      Cst.ExprImpl.toExprOrSpecial?, Cst.ExprData.toExprOrSpecial?, Cst.OrExpr.toExprOrSpecial?,
      Cst.AndExpr.toExprOrSpecial?, Cst.Relation.toAExpr?]
  obtain ⟨var, et, ineq⟩ := vd
  have hv2 : (var.varToAddExpr).toAExpr? = some (Expr.var v) := by
    simp [Cst.AddExpr.toAExpr?, hv, ExprOrSpecial.toExpr?]
  simp only [Cst.VariableDef.toExpr, Cst.VariableDef.toAndExpr] at hleaf
  match ineq, et, hscope with
  | none, none, hscope =>
    simp only [Cst.VariableDef.toPRScope?, Option.some.injEq] at hscope
    subst hscope
    rw [collapse] at hleaf
    simp [Cst.Relation.tt, Cst.Primary.toMember, Cst.Member.toUnary, Cst.Unary.toMultExpr,
      Cst.MultExpr.toAddExpr, Cst.AddExpr.toRelation, Cst.Relation.toAExpr?,
      Cst.Relation.toExprOrSpecial?, Cst.AddExpr.toExprOrSpecial?, Cst.MultExpr.toExprOrSpecial?,
      Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?, Cst.Primary.toExprOrSpecial?,
      Cst.Literal.toExprOrSpecial?, memberAux, ExprOrSpecial.toExpr?] at hleaf
    simp_all [Scope.toExpr]
  | none, some t, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨ety, hety, hsc⟩ := hscope
    subst hsc
    rw [collapse] at hleaf
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, hv2, hety,
      ExprOrSpecial.toExpr?, Option.bind_eq_some_iff] at hleaf
    simp_all [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType]
  | some (.rEq, e), none, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨uid, huid, hsc⟩ := hscope
    subst hsc
    rw [collapse] at hleaf
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, hv2, constructExprRel,
      toAddExpr_toAExpr, toEntityUID_toAExpr huid, ExprOrSpecial.toExpr?,
      Option.bind_eq_some_iff] at hleaf
    simp_all [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType]
  | some (.rIn, e), none, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨uid, huid, hsc⟩ := hscope
    subst hsc
    rw [collapse] at hleaf
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, hv2, constructExprRel,
      toAddExpr_toAExpr, toEntityUID_toAExpr huid, ExprOrSpecial.toExpr?,
      Option.bind_eq_some_iff] at hleaf
    simp_all [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType]
  | some (.rIn, e), some t, hscope =>
    simp [Cst.VariableDef.toPRScope?, Option.bind_eq_some_iff] at hscope
    obtain ⟨uid, huid, ety, hety, hsc⟩ := hscope
    subst hsc
    rw [collapse] at hleaf
    simp [Cst.Relation.toAExpr?, Cst.Relation.toExprOrSpecial?, hv, hv2, hety,
      toAddExpr_toAExpr, toEntityUID_toAExpr huid, ExprOrSpecial.toExpr?,
      Option.bind_eq_some_iff] at hleaf
    simp_all [Scope.toExpr, Var.eqEntityUID, Var.inEntityUID, Var.isEntityType]
  | some (.rEq, e), some t, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rLess, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rLessEq, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rGreater, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rGreaterEq, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope
  | some (.rNotEq, e), _, hscope => simp [Cst.VariableDef.toPRScope?] at hscope

/-- Principal-scope leaf agrees between the two paths. -/
theorem principal_leaf_agrees {vp : Cst.VariableDef} {ps : PrincipalScope} {leaf : Expr}
    (req : Request) (es : Entities) :
    vp.toPrincipalScope? = some ps →
    vp.toExpr.toAExpr? = some leaf →
    ∀ val, evaluate leaf req es = .ok val ↔ evaluate ps.toExpr req es = .ok val := by
  intro hps hleaf val
  simp only [Cst.VariableDef.toPrincipalScope?] at hps
  split at hps <;> [skip; simp at hps]
  rename_i hvar
  simp [Option.bind_eq_some_iff] at hps
  obtain ⟨scope, hscope, hps⟩ := hps
  subst hps
  have hv : (vp.var.varToAddExpr).toExprOrSpecial? = some (ExprOrSpecial.var .principal) := by
    rw [hvar]; simp [Cst.Ident.varToAddExpr, Cst.Primary.toMember, Cst.Member.toUnary,
      Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toExprOrSpecial?,
      Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
      Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?, memberAux]
  rw [toPRScope_leaf hv hscope hleaf]; exact Iff.rfl

/-- Resource-scope leaf agrees between the two paths. -/
theorem resource_leaf_agrees {vr : Cst.VariableDef} {rs : ResourceScope} {leaf : Expr}
    (req : Request) (es : Entities) :
    vr.toResourceScope? = some rs →
    vr.toExpr.toAExpr? = some leaf →
    ∀ val, evaluate leaf req es = .ok val ↔ evaluate rs.toExpr req es = .ok val := by
  intro hrs hleaf val
  simp only [Cst.VariableDef.toResourceScope?] at hrs
  split at hrs <;> [skip; simp at hrs]
  rename_i hvar
  simp [Option.bind_eq_some_iff] at hrs
  obtain ⟨scope, hscope, hrs⟩ := hrs
  subst hrs
  have hv : (vr.var.varToAddExpr).toExprOrSpecial? = some (ExprOrSpecial.var .resource) := by
    rw [hvar]; simp [Cst.Ident.varToAddExpr, Cst.Primary.toMember, Cst.Member.toUnary,
      Cst.Unary.toMultExpr, Cst.MultExpr.toAddExpr, Cst.AddExpr.toExprOrSpecial?,
      Cst.MultExpr.toExprOrSpecial?, Cst.Unary.toExprOrSpecial?, Cst.Member.toExprOrSpecial?,
      Cst.Primary.toExprOrSpecial?, Cst.Name.toVar?, memberAux]
  rw [toPRScope_leaf hv hscope hleaf]; exact Iff.rfl

/-- Action-scope leaf agrees between the two paths (uses `evaluate_mem_singleton`
    for the single-entity `in` case). -/
theorem action_leaf_agrees {va : Cst.VariableDef} {as : ActionScope} {leaf : Expr}
    (req : Request) (es : Entities) :
    va.toActionScope? = some as →
    va.toExpr.toAExpr? = some leaf →
    ∀ val, evaluate leaf req es = .ok val ↔ evaluate as.toExpr req es = .ok val := by
  sorry


/-- The two translation paths from a CST policy to an AST expression
    (`cp → CST Expr → AST Expr` and `cp → AST Policy → AST Expr`) are
    *semantically* equivalent: on every request/entities, the two resulting AST
    expressions evaluate to the same value (agreement on successful `.ok`
    results). Syntactic equality does not hold, since the paths build
    structurally different (but equivalent) expressions. -/
theorem policy_to_expr_agrees (cp : Cst.Policy) (ap : Policy)
  (ce : Cst.Expr) (ae : Expr) (req : Request) (es : Entities) :
  cp.toPolicy? = some ap →
  cp.toExpr = ce →
  ce.toAExpr? = some ae →
  ∀ val, evaluate ae req es = .ok val ↔ evaluate ap.toExpr req es = .ok val := by
  intro hap hce hae
  -- 1. Destructure `cp` and invert `toPolicy?`:
  --      `extractScope? vars = some (ps, as, rs)` ⇒ `vars = [vp, va, vr]`,
  --      `toConditions? conds = some apConds`,     `ap = ⟨_, eff, ps, as, rs, apConds⟩`.
  obtain ⟨⟨eff, vars, conds⟩⟩ := cp
  -- 2. Path 1: rewrite `ae` into `bigAnd` form.
  --      `hce : Cst.Expr.foldAnd (vars.map .toExpr ++ conds.map .toExpr) = ce`,
  --      then `foldAnd_toAExpr` (with `hae`) gives `ae = bigAnd PS' [AS', RS', wc…]`.
  -- 3. Path 2: `rw [evaluate_policy_toExpr]` ⇒ `bigAnd PS [AS, RS, dc…]`.
  -- 4. `apply bigAnd_congr`; discharge scope leaves with
  --      `principal_leaf_agrees` / `action_leaf_agrees` / `resource_leaf_agrees`,
  --      and condition leaves by `rfl` (`wcᵢ = dcᵢ`, same `toAExpr?` body).
  sorry
