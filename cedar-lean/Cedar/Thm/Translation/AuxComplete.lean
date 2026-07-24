import Cedar.Spec
import Cedar.Frontend.Cst
import Cedar.Frontend.Cst.Semantics
import Cedar.Frontend.Cst.ToAst
import Cedar.Thm.Translation.AuxSound
import Cedar.Thm.Data.List.Lemmas

/-!
Auxiliary lemmas for the CST→AST translation *completeness* proofs
(`Cedar/Thm/Translation/ExprComplete.lean`): if a CST expression evaluates
without error, then its translation succeeds.

These are the "list" and "record" shaped helpers, parameterised by a
per-element completeness hypothesis so they don't themselves recurse into the
expression grammar.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Frontend
open Cedar.Frontend.Cst hiding Expr ExprImpl ExprData OrExpr AndExpr AddExpr MultExpr Name Policy PolicyImpl Policies Ident Literal Primary Member MemAccess Unary Relation RelOp Cond VariableDef Ref RecInit Str

/-- If a list of CST expressions all evaluate (the `Except` `mapM` is `.ok`),
    and each translates whenever it evaluates, then the list translates. -/
theorem list_eval_complete {req : Request} {es : Entities} :
    ∀ (xs : List Cst.Expr) (vs : List Value),
      xs.mapM (fun x => x.evaluate req es) = .ok vs →
      (∀ x ∈ xs, ∀ v, x.evaluate req es = .ok v → ∃ ae, x.toAExpr? = some ae) →
      ∃ aes, xs.mapM (fun x => x.toAExpr?) = some aes := by
  intro xs
  induction xs with
  | nil => intro vs _ _; exact ⟨[], by simp⟩
  | cons hd tl ih =>
    intro vs hev hcomp
    simp only [List.mapM_cons, bind, Except.bind] at hev
    cases hhd : hd.evaluate req es with
    | error e => rw [hhd] at hev; simp at hev
    | ok vhd =>
      rw [hhd] at hev
      cases htl : tl.mapM (fun x => x.evaluate req es) with
      | error e => rw [htl] at hev; simp at hev
      | ok vtl =>
        obtain ⟨ae_hd, hae_hd⟩ := hcomp hd List.mem_cons_self vhd hhd
        obtain ⟨aes_tl, haes_tl⟩ :=
          ih vtl htl (fun x hx => hcomp x (List.mem_cons_of_mem _ hx))
        exact ⟨ae_hd :: aes_tl, by simp [List.mapM_cons, hae_hd, haes_tl]⟩

/-- If a record literal's key/value pairs all evaluate (the `Except` `mapM` is
    `.ok`), and each value translates whenever it evaluates, then the record
    translates (`rInitsToMap?` succeeds). Keys are handled by
    `Cst.Expr.toAttr?_consistent`. -/
theorem rInits_complete {req : Request} {es : Entities} :
    ∀ (r : List Cst.RecInit) (avs : List (Attr × Value)),
      r.mapM (fun ri =>
        match ri.attr.toAttr? with
        | none => Except.error (Error.cstError CstError.stringError)
        | some attr => do let val ← ri.value.evaluate req es; .ok (attr, val)) = .ok avs →
      (∀ ri ∈ r, ∀ v, ri.value.evaluate req es = .ok v → ∃ ae, ri.value.toAExpr? = some ae) →
      ∃ map, rInitsToMap? r = some map := by
  intro r
  induction r with
  | nil => intro avs _ _; exact ⟨[], by simp [rInitsToMap?]⟩
  | cons ri rs ih =>
    intro avs hev hcomp
    rw [List.mapM_ok_iff_forall₂] at hev
    cases hev with
    | cons hhd htl =>
      rename_i av_hd av_tl
      cases hkey : ri.attr.toAttr? with
      | none => simp [hkey] at hhd
      | some attr =>
        cases hvalv : ri.value.evaluate req es with
        | error e => simp [hkey, hvalv, bind, Except.bind] at hhd
        | ok vval =>
          have hkey_t := Cst.Expr.toAttr?_consistent ri.attr
          rw [hkey] at hkey_t
          replace hkey_t := hkey_t.symm
          rw [Option.bind_eq_some_iff] at hkey_t
          obtain ⟨eos, heos, hattr⟩ := hkey_t
          obtain ⟨vae, hvae⟩ := hcomp ri List.mem_cons_self vval hvalv
          have htl' : rs.mapM (fun ri =>
              match ri.attr.toAttr? with
              | none => Except.error (Error.cstError CstError.stringError)
              | some attr => do let val ← ri.value.evaluate req es; .ok (attr, val)) = .ok av_tl := by
            rw [List.mapM_ok_iff_forall₂]; exact htl
          obtain ⟨mtl, hmtl⟩ := ih av_tl htl' (fun x hx => hcomp x (List.mem_cons_of_mem _ hx))
          exact ⟨(attr, vae) :: mtl, by simp [rInitsToMap?, heos, hattr, hvae, hmtl]⟩

/-- `toUnreservedString?` succeeds only on an (unreserved) `.idIdent`. -/
private theorem toUnreservedString?_some {i : Cst.Ident} {s : String}
    (h : Cst.Ident.toUnreservedString? i = some s) : ∃ hk, i = .idIdent s hk := by
  cases i
  case idIdent s' hk' =>
    simp only [Cst.Ident.toUnreservedString?] at h
    split at h
    · injection h with h'; subst h'; exact ⟨hk', rfl⟩
    · exact absurd h (by simp)
  all_goals simp [Cst.Ident.toUnreservedString?] at h

/-- Prepending a field accessor reduces through `memberAuxB`'s attribute branch
    as long as the remaining accessors don't begin with a call. -/
private theorem memberAuxB_field_cons (id : Cst.Ident) (l : List AstAccessor) (he : Expr)
    (hnc : ∀ cargs t, l ≠ AstAccessor.call cargs :: t) :
    memberAuxB he (.field id :: l) = memberAuxB (.getAttr he (Cst.Ident.toString id)) l := by
  cases l with
  | nil => simp [memberAuxB]
  | cons a t =>
    cases a with
    | call cargs => exact absurd rfl (hnc cargs t)
    | field f => simp [memberAuxB]
    | index s => simp [memberAuxB]

/-- Core accessor-list completeness: if `Member.evalAccessors` succeeds on `accs`
    (and each call-argument translates when it evaluates), then `accs` translates
    via `toAstAccessor?`, the translation never begins with a call, and the
    resulting accessor list is accepted by `memberAuxB` for any head expression. -/
theorem evalAccessors_complete {req : Request} {es : Entities}
    (accs : List Cst.MemAccess) (head v : Value)
    (hev : Cst.Member.evalAccessors head accs req es = .ok v)
    (hcomp : ∀ ce : Cst.Expr, sizeOf ce < sizeOf accs →
      ∀ w, ce.evaluate req es = .ok w → ∃ ax, ce.toAExpr? = some ax) :
    ∃ accs_ast, accs.mapM Cst.MemAccess.toAstAccessor? = some accs_ast ∧
      (∀ cargs t, accs_ast ≠ AstAccessor.call cargs :: t) ∧
      ∀ he : Expr, ∃ r, memberAuxB he accs_ast = some r := by
  match accs, hev with
  | [], _ => exact ⟨[], by simp, by simp, fun he => ⟨he, rfl⟩⟩
  | .call _ :: _, hev => simp [Cst.Member.evalAccessors] at hev
  | .index ex :: rest, hev =>
    cases hex : Cst.Expr.toUnescapedStringLiteral? ex with
    | none => simp [Cst.Member.evalAccessors, hex] at hev
    | some attr =>
      simp only [Cst.Member.evalAccessors, hex] at hev
      cases hga : getAttr head attr es with
      | error e => simp [hga, bind, Except.bind] at hev
      | ok v' =>
        simp only [hga, bind, Except.bind] at hev
        obtain ⟨rest_ast, hrest_ast, _, hmemb⟩ := evalAccessors_complete rest v' v hev
          (fun ce hsz w hcw => hcomp ce (by simp only [List.cons.sizeOf_spec]; omega) w hcw)
        refine ⟨.index attr :: rest_ast, ?_, by simp, ?_⟩
        · simp [List.mapM_cons, Cst.MemAccess.toAstAccessor?, hex, hrest_ast]
        · intro he
          obtain ⟨r, hr⟩ := hmemb (Expr.getAttr he attr)
          exact ⟨r, by simp only [memberAuxB]; exact hr⟩
  | .field i :: .call args :: rest, hev =>
    cases hi : Cst.Ident.toUnreservedString? i with
    | none => simp [Cst.Member.evalAccessors, hi] at hev
    | some m =>
      obtain ⟨hm_kw, hii⟩ := toUnreservedString?_some hi; subst hii
      cases hop : Cst.String.toMethodOp? m with
      | none => simp [Cst.Member.evalAccessors, hi, hop] at hev
      | some op =>
        cases op with
        | inl bop =>
          cases args with
          | nil => simp [Cst.Member.evalAccessors, hi, hop] at hev
          | cons arg rest_args =>
            cases rest_args with
            | cons _ _ => simp [Cst.Member.evalAccessors, hi, hop] at hev
            | nil =>
              simp only [Cst.Member.evalAccessors, hi, hop] at hev
              cases harg : arg.evaluate req es with
              | error e => rw [harg] at hev; simp [bind, Except.bind] at hev
              | ok argVal =>
                rw [harg] at hev; simp only [bind, Except.bind] at hev
                cases hap : apply₂ bop head argVal es with
                | error e => rw [hap] at hev; simp at hev
                | ok v' =>
                  rw [hap] at hev
                  obtain ⟨a, ha⟩ := hcomp arg
                    (by simp only [List.cons.sizeOf_spec, Cst.MemAccess.call.sizeOf_spec,
                          List.nil.sizeOf_spec]; omega) argVal harg
                  obtain ⟨rest_ast, hrest_ast, _, hmemb⟩ := evalAccessors_complete rest v' v hev
                    (fun ce hsz w hcw => hcomp ce
                      (by simp only [List.cons.sizeOf_spec] at hsz ⊢; omega) w hcw)
                  refine ⟨.field (.idIdent m hm_kw) :: .call [a] :: rest_ast, ?_, by simp, ?_⟩
                  · rw [List.mapM_cons, List.mapM_cons]
                    simp [Cst.MemAccess.toAstAccessor?, hi, Cst.Expr.toAExprs?, ha, hrest_ast]
                  · intro he
                    obtain ⟨r, hr⟩ := hmemb (Expr.binaryApp bop he a)
                    refine ⟨r, ?_⟩
                    simp only [memberAuxB, Cst.Ident.toMeth?, hop, oneArg?]
                    exact hr
        | inr uop =>
          cases args with
          | cons _ _ => simp [Cst.Member.evalAccessors, hi, hop] at hev
          | nil =>
            simp only [Cst.Member.evalAccessors, hi, hop, List.isEmpty_nil, if_true] at hev
            cases hap : apply₁ uop head with
            | error e => rw [hap] at hev; simp [bind, Except.bind] at hev
            | ok v' =>
              rw [hap] at hev; simp only [bind, Except.bind] at hev
              obtain ⟨rest_ast, hrest_ast, _, hmemb⟩ := evalAccessors_complete rest v' v hev
                (fun ce hsz w hcw => hcomp ce
                  (by simp only [List.cons.sizeOf_spec] at hsz ⊢; omega) w hcw)
              refine ⟨.field (.idIdent m hm_kw) :: .call [] :: rest_ast, ?_, by simp, ?_⟩
              · rw [List.mapM_cons, List.mapM_cons]
                simp [Cst.MemAccess.toAstAccessor?, hi, Cst.Expr.toAExprs?, hrest_ast]
              · intro he
                obtain ⟨r, hr⟩ := hmemb (Expr.unaryApp uop he)
                refine ⟨r, ?_⟩
                simp only [memberAuxB, Cst.Ident.toMeth?, hop, List.isEmpty_nil, if_true]
                exact hr
  | .field i :: [], hev =>
    cases hi : Cst.Ident.toUnreservedString? i with
    | none => simp [Cst.Member.evalAccessors, hi] at hev
    | some attr =>
      obtain ⟨hm_kw, hii⟩ := toUnreservedString?_some hi; subst hii
      refine ⟨[.field (.idIdent attr hm_kw)], ?_, by simp, ?_⟩
      · simp [List.mapM_cons, Cst.MemAccess.toAstAccessor?, hi]
      · intro he
        exact ⟨Expr.getAttr he attr, by simp [memberAuxB, Cst.Ident.toString]⟩
  | .field i :: .field i2 :: rest, hev =>
    cases hi : Cst.Ident.toUnreservedString? i with
    | none => simp [Cst.Member.evalAccessors, hi] at hev
    | some attr =>
      obtain ⟨hm_kw, hii⟩ := toUnreservedString?_some hi; subst hii
      simp only [Cst.Member.evalAccessors, hi] at hev
      cases hga : getAttr head attr es with
      | error e => simp [hga, bind, Except.bind] at hev
      | ok v' =>
        simp only [hga, bind, Except.bind] at hev
        have hev' : Cst.Member.evalAccessors v' (.field i2 :: rest) req es = .ok v := hev
        obtain ⟨rest_ast, hrest_ast, hnc, hmemb⟩ :=
          evalAccessors_complete (.field i2 :: rest) v' v hev'
            (fun ce hsz w hcw => hcomp ce (by simp only [List.cons.sizeOf_spec] at hsz ⊢; omega) w hcw)
        refine ⟨.field (.idIdent attr hm_kw) :: rest_ast, ?_, by simp, ?_⟩
        · rw [List.mapM_cons]; simp [Cst.MemAccess.toAstAccessor?, hi, hrest_ast]
        · intro he
          obtain ⟨r, hr⟩ := hmemb (Expr.getAttr he attr)
          refine ⟨r, ?_⟩
          rw [memberAuxB_field_cons _ rest_ast he hnc]
          simpa [Cst.Ident.toString] using hr
  | .field i :: .index ex :: rest, hev =>
    cases hi : Cst.Ident.toUnreservedString? i with
    | none => simp [Cst.Member.evalAccessors, hi] at hev
    | some attr =>
      obtain ⟨hm_kw, hii⟩ := toUnreservedString?_some hi; subst hii
      have hstep : Cst.Member.evalAccessors head (.field (.idIdent attr hm_kw) :: .index ex :: rest) req es
                 = (do let hv ← getAttr head attr es;
                       Cst.Member.evalAccessors hv (.index ex :: rest) req es) := by
        simp [Cst.Member.evalAccessors, hi]
      rw [hstep] at hev
      cases hga : getAttr head attr es with
      | error e => rw [hga] at hev; simp [bind, Except.bind] at hev
      | ok v' =>
        rw [hga] at hev; simp only [bind, Except.bind] at hev
        obtain ⟨rest_ast, hrest_ast, hnc, hmemb⟩ :=
          evalAccessors_complete (.index ex :: rest) v' v hev
            (fun ce hsz w hcw => hcomp ce (by simp only [List.cons.sizeOf_spec] at hsz ⊢; omega) w hcw)
        refine ⟨.field (.idIdent attr hm_kw) :: rest_ast, ?_, by simp, ?_⟩
        · rw [List.mapM_cons]; simp [Cst.MemAccess.toAstAccessor?, hi, hrest_ast]
        · intro he
          obtain ⟨r, hr⟩ := hmemb (Expr.getAttr he attr)
          refine ⟨r, ?_⟩
          rw [memberAuxB_field_cons _ rest_ast he hnc]
          simpa [Cst.Ident.toString] using hr
termination_by sizeOf accs
decreasing_by
  all_goals simp_wf
  all_goals omega

/-- Fold completeness for `MultExpr`: if `foldOps` succeeds and every operand
    translates when it evaluates, then `foldExtended` succeeds (for any head). -/
theorem multExprFoldExtended_complete {req : Request} {es : Entities}
    (xs : List (Cst.MultOp × Cst.Unary)) (acc_v : Value) (acc_ast : Expr) (v : Value)
    (hfold : Cst.MultExpr.foldOps acc_v xs req es = .ok v)
    (hcomp : ∀ u : Cst.Unary, sizeOf u < sizeOf xs →
      ∀ w, u.evaluate req es = .ok w → ∃ ax, u.toAExpr? = some ax) :
    ∃ result, Cst.MultExpr.foldExtended acc_ast xs = some result := by
  match xs, hfold with
  | [], _ => exact ⟨acc_ast, by simp [Cst.MultExpr.foldExtended]⟩
  | (op, u) :: rest, hfold =>
    simp only [Cst.MultExpr.foldOps] at hfold
    cases hu : u.evaluate req es with
    | error e => rw [hu] at hfold; simp [bind, Except.bind] at hfold
    | ok uv =>
      rw [hu] at hfold
      cases op with
      | mTimes =>
        simp only [bind, Except.bind] at hfold
        cases hap : apply₂ .mul acc_v uv es with
        | error e => rw [hap] at hfold; simp at hfold
        | ok acc'' =>
          rw [hap] at hfold
          obtain ⟨aval, haval⟩ := hcomp u
            (by simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega) uv hu
          obtain ⟨result, hresult⟩ :=
            multExprFoldExtended_complete rest acc'' (.binaryApp .mul acc_ast aval) v hfold
              (fun u' hsz w hw => hcomp u'
                (by simp only [List.cons.sizeOf_spec]; omega) w hw)
          exact ⟨result, by simp [Cst.MultExpr.foldExtended, haval, hresult]⟩
      | mDivide => simp [bind, Except.bind] at hfold
      | mMod => simp [bind, Except.bind] at hfold
termination_by sizeOf xs

/-- Fold completeness for `AddExpr`: if `foldOps` succeeds and every operand
    translates when it evaluates, then `foldExtended` succeeds (for any head).
    Both `aPlus`/`aMinus` are accepted by the translator. -/
theorem addExprFoldExtended_complete {req : Request} {es : Entities}
    (xs : List (Cst.AddOp × Cst.MultExpr)) (acc_v : Value) (acc_ast : Expr) (v : Value)
    (hfold : Cst.AddExpr.foldOps acc_v xs req es = .ok v)
    (hcomp : ∀ m : Cst.MultExpr, sizeOf m < sizeOf xs →
      ∀ w, m.evaluate req es = .ok w → ∃ ax, m.toAExpr? = some ax) :
    ∃ result, Cst.AddExpr.foldExtended acc_ast xs = some result := by
  match xs, hfold with
  | [], _ => exact ⟨acc_ast, by simp [Cst.AddExpr.foldExtended]⟩
  | (op, m) :: rest, hfold =>
    simp only [Cst.AddExpr.foldOps] at hfold
    cases hm : m.evaluate req es with
    | error e => rw [hm] at hfold; simp at hfold
    | ok mv =>
      rw [hm] at hfold
      obtain ⟨aval, haval⟩ := hcomp m
        (by simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega) mv hm
      cases op with
      | aPlus =>
        simp only [bind, Except.bind] at hfold
        cases hap : apply₂ .add acc_v mv es with
        | error e => rw [hap] at hfold; simp at hfold
        | ok acc'' =>
          rw [hap] at hfold
          obtain ⟨result, hresult⟩ :=
            addExprFoldExtended_complete rest acc'' (.binaryApp .add acc_ast aval) v hfold
              (fun m' hsz w hw => hcomp m' (by simp only [List.cons.sizeOf_spec]; omega) w hw)
          exact ⟨result, by simp [Cst.AddExpr.foldExtended, haval, hresult]⟩
      | aMinus =>
        simp only [bind, Except.bind] at hfold
        cases hap : apply₂ .sub acc_v mv es with
        | error e => rw [hap] at hfold; simp at hfold
        | ok acc'' =>
          rw [hap] at hfold
          obtain ⟨result, hresult⟩ :=
            addExprFoldExtended_complete rest acc'' (.binaryApp .sub acc_ast aval) v hfold
              (fun m' hsz w hw => hcomp m' (by simp only [List.cons.sizeOf_spec]; omega) w hw)
          exact ⟨result, by simp [Cst.AddExpr.foldExtended, haval, hresult]⟩
termination_by sizeOf xs

/-- If every conjunct of an `AndExpr`'s extended list translates, `foldExtended`
    succeeds (for any head). Used in `AndExpr` completeness to discharge the
    translatability guard recorded by the strengthened evaluator. -/
theorem andExprFoldExtended_complete :
    ∀ (xs : List Cst.Relation), (xs.all (fun r => r.toAExpr?.isSome) = true) →
    ∀ (acc : Expr), ∃ result, Cst.AndExpr.foldExtended acc xs = some result := by
  intro xs
  induction xs with
  | nil => intro _ acc; exact ⟨acc, by simp [Cst.AndExpr.foldExtended]⟩
  | cons rel rest ih =>
    intro hall acc
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hrel, hrest⟩ := hall
    cases hrelE : rel.toAExpr? with
    | none => rw [hrelE] at hrel; simp at hrel
    | some aval =>
      obtain ⟨result, hresult⟩ := ih hrest (Cedar.Spec.Expr.and acc aval)
      exact ⟨result, by simp [Cst.AndExpr.foldExtended, hrelE, hresult]⟩

/-- If every disjunct of an `OrExpr`'s extended list translates, `foldExtended`
    succeeds (for any head). -/
theorem orExprFoldExtended_complete :
    ∀ (xs : List Cst.AndExpr), (xs.all (fun r => r.toAExpr?.isSome) = true) →
    ∀ (acc : Expr), ∃ result, Cst.OrExpr.foldExtended acc xs = some result := by
  intro xs
  induction xs with
  | nil => intro _ acc; exact ⟨acc, by simp [Cst.OrExpr.foldExtended]⟩
  | cons rel rest ih =>
    intro hall acc
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hrel, hrest⟩ := hall
    cases hrelE : rel.toAExpr? with
    | none => rw [hrelE] at hrel; simp at hrel
    | some aval =>
      obtain ⟨result, hresult⟩ := ih hrest (Cedar.Spec.Expr.or acc aval)
      exact ⟨result, by simp [Cst.OrExpr.foldExtended, hrelE, hresult]⟩

-- If a CST policy can be evaluated without error then scope extract will succeed
theorem extractScope_complete
  (cp : Cst.Policy) (req : Request) (es : Entities) :
  ¬ Cst.hasError cp req es →
  ∃ trip, match cp with
  | .policy p => extractScope? p.vars = some trip := by
  intro hne
  cases cp with
  | policy p =>
    cases h : extractScope? p.vars with
    | none =>
      exfalso
      apply hne
      have hpn : p.toPolicy? = none := by simp [Cst.PolicyImpl.toPolicy?, h]
      simp only [Cst.hasError, hpn, Option.isNone_none, if_true]
    | some trip => exact ⟨trip, h⟩

end Cedar.Thm
