import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/--
States that an `Environment` is well-formed
TODO: this is currently just a placeholder; move this to somewhere else
-/
def Environment.WellFormed (_env : Environment) : Prop := true
  -- env.ets.WellFormed ∧
  -- env.acts.WellFormed
  -- ∀ (ety : EntityType) (euid : EntityUID),
  --   env.ets.contains ety →
  --   env.acts.contains euid →
  --   euid.ty ≠ ety

/--
States that under sufficiently good conditions, the symbolic compiler
succeeds on a typed expression `ty` and produces a term `t` with the
corresponding type.
-/
def CompileWellTypedForExpr (ty : TypedExpr) (εnv : SymEnv) : Prop :=
  ∃ t : Term,
    compile ty.toExpr εnv = .ok t ∧
    t.typeOf = .option (TermType.ofType ty.typeOf)

def CompileWellTypedCondition (ty : TypedExpr) (env : Environment) (εnv : SymEnv) : Prop :=
  Environment.WellFormed env ∧
  εnv = SymEnv.ofEnv env ∧
  TypedExpr.WellTyped env ty ∧
  εnv.WellFormedFor ty.toExpr

/--
A lemma related to key lookup and map in a list of key-value pairs
-/
theorem list_key_find?_map
  [BEq α] [ReflBEq α]
  {l : List (α × β)}
  {k : α} {v : β}
  {f : α → β → γ}
  (h : List.find? (λ x => x.fst == k) l = some (k, v)) :
  List.find? (λ x => x.fst == k) (l.map λ (k, v) => (k, f k v)) = some (k, f k v)
:= by
  induction l
  case nil => simp at h
  case cons head tail ih =>
    simp at h
    cases h
    case _ h => simp [h]
    case _ h =>
      have ih := ih h.2
      simp only [List.map]
      simp only [List.find?]
      simp [ih]
      simp [h]

theorem insertCanonical_exists [LT β] [Cedar.Data.StrictLT β] [DecidableLT β]
  {f : α → β} {xs : List α} (x : α) :
  x ∈ List.insertCanonical f x xs
:= by
  induction xs
  case nil => simp [List.insertCanonical]
  case cons head tail ih =>
    simp [List.insertCanonical]
    split; any_goals simp
    split; any_goals simp
    apply Or.inr ih

theorem insertCanonical_new
  [LT β] [Cedar.Data.StrictLT β] [DecidableLT β] [DecidableEq β]
  {f : α → β} {xs : List α} {x : α} {y : α}
  (hexists : y ∈ xs)
  (hneq : f x ≠ f y) :
  y ∈ List.insertCanonical f x xs
:= by
  induction xs

  case nil => simp at hexists

  case cons hd tl ih =>
    simp [List.insertCanonical]
    split
    simp [hexists]
    split
    · simp at hexists
      cases hexists
      case _ hy => simp [hy]
      case _ hy => simp [ih hy]
    · simp at hexists
      cases hexists
      case _ hlt hgt hy =>
        simp [← hy] at hlt hgt
        have hltgt := Data.StrictLT.connected (f x) (f y) hneq
        cases hltgt <;> contradiction
      case _ hy => simp [hy]

/--
If the key exists in l, then it exists in `Data.Map.make l`
-/
theorem list_key_find?_append_to_map_make_find?
  -- [BEq α]
  [DecidableEq α] [LT α] [DecidableLT α]
  [Cedar.Data.StrictLT α]
  {a b : List (α × β)}
  {k : α} {v : β}
  (h : List.find? (λ x => x.fst == k) a = some (k, v)) :
  (Data.Map.make (a ++ b)).find? k = some v
:= by
  apply (Data.Map.in_list_iff_find?_some (Data.Map.make_wf (a ++ b))).mp
  simp [Data.Map.make, Data.Map.kvs]

  induction a

  case nil => simp at h
  case cons head tail ih =>
    simp [List.find?] at h
    split at h

    case _ heq =>
      simp at h
      simp [List.canonicalize, h]
      apply insertCanonical_exists

    case _ hneq =>
      have ih := ih h
      simp at hneq
      simp [List.canonicalize]

      apply insertCanonical_new
      assumption
      simp [hneq]

/--
A wrapper around compile_wf for convenience
-/
theorem wt_cond_implies_compile_wf
  {ty : TypedExpr} {env : Environment} {εnv : SymEnv} {t : Term} :
  CompileWellTypedCondition ty env εnv →
  compile ty.toExpr εnv = .ok t →
  t.WellFormed εnv.entities
:= by
  intros h hcomp; rcases h with ⟨_, _, _, hwf⟩
  have htwf := compile_wf hwf hcomp
  simp [htwf]

/--
Special case for literals
-/
theorem compile_well_typed_lit {p : Prim} {ty : CedarType} {env : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.lit p ty) env εnv →
  CompileWellTypedForExpr (.lit p ty) εnv
:= by
  intros h; rcases h with ⟨_, henv, hwt, hwf⟩
  simp [TypedExpr.typeOf, TypedExpr.toExpr, CompileWellTypedForExpr] at *

  unfold SymEnv.WellFormedFor at hwf
  rcases hwf with ⟨_, ⟨hrefs⟩⟩
  rcases hwt with ⟨_, ⟨⟨hwt⟩⟩⟩

  all_goals
    simp [compile, compilePrim, Factory.someOf]
    simp [Prim.ValidRef] at hrefs
    try simp [hrefs]
    simp [
      TermType.ofType,
      Term.typeOf,
      TermPrim.typeOf,
      BitVec.width,
    ]

/- Lemmas that TermType.ofType produces the same result w/ or w/o liftBoolTypes. -/
mutual
  private theorem ofQualifiedType_ignores_liftBool
    {ty : QualifiedType} :
    TermType.ofQualifiedType ty =
    TermType.ofQualifiedType ty.liftBoolTypes
  := by
    cases ty
    all_goals
      simp [
        TermType.ofQualifiedType,
        CedarType.liftBoolTypes,
        QualifiedType.liftBoolTypes,
      ]
      apply ofType_ignores_liftBool

  private theorem ofRecordType_ignores_liftBool:
    ∀ recs : List (Attr × QualifiedType),
    TermType.ofRecordType recs =
    TermType.ofRecordType (CedarType.liftBoolTypesRecord recs)
  | [] => by simp [TermType.ofRecordType, CedarType.liftBoolTypesRecord]
  | (_, ty) :: tail => by
    simp [TermType.ofRecordType, CedarType.liftBoolTypesRecord]
    constructor
    apply ofQualifiedType_ignores_liftBool
    apply ofRecordType_ignores_liftBool tail

  private theorem ofType_ignores_liftBool :
    ∀ ty : CedarType,
    TermType.ofType ty = TermType.ofType ty.liftBoolTypes
  | .bool _ => by simp [TermType.ofType, CedarType.liftBoolTypes]
  | .int => by simp [TermType.ofType, CedarType.liftBoolTypes]
  | .string => by simp [TermType.ofType, CedarType.liftBoolTypes]
  | .entity ety => by simp [TermType.ofType, CedarType.liftBoolTypes]
  | .ext xty => by simp [TermType.ofType, CedarType.liftBoolTypes]
  | .set ty => by
    simp [TermType.ofType, CedarType.liftBoolTypes]
    apply ofType_ignores_liftBool ty
  | .record rty => by
    simp [TermType.ofType, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
    apply ofRecordType_ignores_liftBool
end

theorem isCedarRecordType_implies_isRecordType
  {ty : TermType} :
  TermType.isCedarRecordType ty →
  TermType.isRecordType ty
:= by
  intros hty
  simp [
    TermType.isCedarRecordType,
    TermType.isRecordType,
    TermType.cedarType?,
  ] at *
  cases ty

  split at hty
  split

  any_goals simp
  any_goals contradiction
  all_goals simp [TermType.cedarType?] at *

  case prim _ h _ _ =>
    unfold TermType.cedarType? at *
    split at h
    any_goals simp at h
    any_goals contradiction

  case set ty =>
    cases e : ty.cedarType?
    all_goals rw [e] at hty
    all_goals simp at hty

/- Special case for variables -/
theorem compile_well_typed_var {v : Var} {ty : CedarType} {env : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.var v ty) env εnv →
  CompileWellTypedForExpr (.var v ty) εnv
:= by
  intros h; rcases h with ⟨_, henv, hwt, hwf⟩
  simp [TypedExpr.typeOf, TypedExpr.toExpr, CompileWellTypedForExpr] at *

  unfold SymEnv.WellFormedFor SymEnv.WellFormed SymRequest.WellFormed at hwf

  rcases hwf with ⟨⟨⟨_, hprincipal, _, haction, _, hresource, _, hcontext⟩, _⟩, _⟩
  case _ =>

  rcases hwt with _ | hwt
  cases hwt

  all_goals
    simp [compile, compileVar, Factory.someOf] at *

  case var.context =>
    simp [
      TermType.ofType,
      Term.typeOf,
      CedarType.liftBoolTypes,
      RecordType.liftBoolTypes,
    ]
    simp [
      hprincipal, haction, hresource,
    ] at *

    rw [isCedarRecordType_implies_isRecordType]
    rotate_left; assumption

    simp [TermType.ofType, Term.typeOf]
    simp [henv, SymEnv.ofEnv, SymRequest.ofRequestType, TermType.ofType, TermPrim.typeOf, Term.typeOf]
    apply ofRecordType_ignores_liftBool

  all_goals
    simp [
      hprincipal, haction, hresource, hcontext,
    ] at *
    simp [TermType.ofType, Term.typeOf]
    simp [henv, SymEnv.ofEnv, SymRequest.ofRequestType, TermType.ofType, TermPrim.typeOf, Term.typeOf]

theorem wf_typeOf_ite {g t₁ t₂ : Term} {ty : TermType} {entities : SymEntities}
  (hwf_g : g.WellFormed entities)
  (hwf_t1 : t₁.WellFormed entities)
  (hwf_t2 : t₂.WellFormed entities)
  (hbool_g : g.typeOf = TermType.bool)
  (htyeq1 : t₁.typeOf = ty)
  (htyeq2 : t₂.typeOf = ty) :
  (Factory.ite g t₁ t₂).typeOf = ty
:= by
  have h1 : t₁.typeOf = t₂.typeOf := by simp [htyeq1, htyeq2]
  have h := wf_ite hwf_g hwf_t1 hwf_t2 hbool_g h1
  rw [h.right]; assumption

theorem wf_typeOf_not {t : Term} {ty : TermType} {entities : SymEntities}
  (hwf : t.WellFormed entities)
  (hbool_t : t.typeOf = ty)
  (hty : ty = .bool) :
  (Factory.not t).typeOf = ty
:= by
  have h1 : t.typeOf = .bool := by simp [hbool_t, hty]
  have h := wf_not hwf h1
  rw [h.right]; simp [hty]

theorem wf_typeOf_eq {t₁ t₂ : Term} {entities : SymEntities}
  (h1 : t₁.WellFormed entities)
  (h2 : t₂.WellFormed entities)
  (htyeq : t₁.typeOf = t₂.typeOf) :
  (Factory.eq t₁ t₂).typeOf = .bool
:= by
  have h := wf_eq h1 h2 htyeq
  rw [h.right]

theorem wf_typeOf_or {t₁ t₂ : Term} {entities : SymEntities}
  (hwf_t1 : t₁.WellFormed entities)
  (hwf_t2 : t₂.WellFormed entities)
  (hbool_t1 : t₁.typeOf = TermType.bool)
  (hbool_t2 : t₂.typeOf = TermType.bool) :
  (Factory.or t₁ t₂).typeOf = TermType.bool
:= (wf_or hwf_t1 hwf_t2 hbool_t1 hbool_t2).right

/--
CompileWellTypedCondition decomposes for ite
-/
theorem eliminate_wt_cond_ite
  {cond : TypedExpr} {thenExpr : TypedExpr} {elseExpr : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.ite cond thenExpr elseExpr ty) env εnv) :
  CompileWellTypedCondition cond env εnv ∧
  CompileWellTypedCondition thenExpr env εnv ∧
  CompileWellTypedCondition elseExpr env εnv
:= by
  have ⟨hwf_env, henv, hwt, hwf⟩ := h
  constructor; rotate_left; constructor
  all_goals
    constructor
    any_goals assumption

    constructor
    · cases hwt; assumption
    · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
      rcases hwf with ⟨_, hrefs⟩
      constructor;
      · cases hwt; assumption
      · constructor
        · assumption
        · cases hrefs;
          any_goals assumption

theorem compile_well_typed_ite
  {a : TypedExpr} {b : TypedExpr} {c : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (iha : CompileWellTypedForExpr a εnv)
  (ihb : CompileWellTypedForExpr b εnv)
  (ihc : CompileWellTypedForExpr c εnv)
  (hcond_ite : CompileWellTypedCondition (.ite a b c ty) env εnv) :
  CompileWellTypedForExpr (.ite a b c ty) εnv
:= by
  have ⟨hcond_a, hcond_b, hcond_c⟩ := eliminate_wt_cond_ite hcond_ite
  have ⟨hwf_env, henv, hwt_ite, hwf_ite⟩ := hcond_ite

  have ⟨tcomp_a, ⟨hcomp_a, hty_comp_a⟩⟩ := iha
  have ⟨tcomp_b, ⟨hcomp_b, hty_comp_b⟩⟩ := ihb
  have ⟨tcomp_c, ⟨hcomp_c, hty_comp_c⟩⟩ := ihc

  have hwf_comp_a := wt_cond_implies_compile_wf hcond_a hcomp_a
  have hwf_comp_b := wt_cond_implies_compile_wf hcond_b hcomp_b
  have hwf_comp_c := wt_cond_implies_compile_wf hcond_c hcomp_c

  have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
  have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b
  have ⟨hwf_get_comp_c, hty_get_comp_c⟩ := wf_option_get hwf_comp_c hty_comp_c

  -- Infer types from well-typedness of (.ite a b c ty)
  cases hwt_ite;
  case ite _ hbool_a _ _ heqty =>

  simp [
    CompileWellTypedForExpr,
    TypedExpr.toExpr,
    compile,
    compileIf,
    hcomp_a, hty_comp_a,
    hcomp_b, hty_comp_b,
    hcomp_c, hty_comp_c,
    hbool_a, heqty,
  ]

  -- Case analysis on simplification
  split
  · simp [← heqty, hty_comp_b]
    unfold TypedExpr.typeOf
    simp

  · simp [heqty, hty_comp_c]
    unfold TypedExpr.typeOf
    simp

  · simp
    apply typeOf_ifSome_option
    apply wf_typeOf_ite
      hwf_get_comp_a
      hwf_comp_b
      hwf_comp_c
    · simp [hty_get_comp_a, hbool_a, TermType.ofType]
    · simp [heqty, hty_comp_b]
      unfold TypedExpr.typeOf
      simp
    · simp [heqty, hty_comp_c]
      unfold TypedExpr.typeOf
      simp

  · simp; contradiction

/--
CompileWellTypedCondition decomposes for `or` or `and`
-/
theorem eliminate_wt_cond_or_and
  {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  {cons : TypedExpr → TypedExpr → CedarType → TypedExpr}
  (h : CompileWellTypedCondition (cons a b ty) env εnv)
  (hcons : cons = .or ∨ cons = .and) :
  CompileWellTypedCondition a env εnv ∧
  CompileWellTypedCondition b env εnv
:= by
  cases hcons
  all_goals
    -- Same proof for both cases
    case _ hcons =>
    simp [hcons] at *
    have ⟨hwf_env, henv, hwt, hwf⟩ := h
    constructor
    all_goals
      constructor
      any_goals assumption

      constructor
      · cases hwt; assumption
      · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
        rcases hwf with ⟨_, hrefs⟩
        constructor;
        · cases hwt; assumption
        · constructor
          · assumption
          · cases hrefs;
            any_goals assumption

/--
Special case for `or` and `and`
-/
theorem compile_well_typed_or_and
  {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (iha : CompileWellTypedForExpr a εnv)
  (ihb : CompileWellTypedForExpr b εnv) :

  (CompileWellTypedCondition (.or a b ty) env εnv →
    CompileWellTypedForExpr (.or a b ty) εnv) ∧

  (CompileWellTypedCondition (.and a b ty) env εnv →
    CompileWellTypedForExpr (.and a b ty) εnv)
:= by
  constructor
  all_goals
  intros hcond

  -- Some facts needed later
  have ⟨hwf_env, henv, hwt, hwf⟩ := hcond
  have ⟨hcond_a, hcond_b⟩ := eliminate_wt_cond_or_and hcond ?_
  any_goals simp

  have ⟨tcomp_a, ⟨hcomp_a, hty_comp_a⟩⟩ := iha
  have ⟨tcomp_b, ⟨hcomp_b, hty_comp_b⟩⟩ := ihb

  have hwf_comp_a := wt_cond_implies_compile_wf hcond_a hcomp_a
  have hwf_comp_b := wt_cond_implies_compile_wf hcond_b hcomp_b

  have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
  have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b

  -- By well-typedness, a and b must be booleans
  -- So we substitute that fact and simplify
  cases hwt; case _ _ hbool_a _ hbool_b =>
  simp [hbool_a, hbool_b] at *; clear hbool_a hbool_b
  simp [TypedExpr.typeOf, TermType.ofType] at *

  simp [
    CompileWellTypedForExpr,
    TypedExpr.toExpr,
    compile,
    compileAnd,
    compileOr,
    hcomp_a, hty_comp_a, hcomp_b, hty_comp_b,
  ]
  split
  · apply Exists.intro; constructor; rfl
    simp [Term.typeOf, TermPrim.typeOf, TermType.ofType, TypedExpr.typeOf]
  · apply Exists.intro; constructor; rfl
    apply typeOf_ifSome_option
    apply wf_typeOf_ite
    any_goals assumption
    constructor
    apply wf_bool
    simp [TermType.ofType, Term.typeOf, TermPrim.typeOf, Factory.someOf, TypedExpr.typeOf]
  · contradiction

/--
CompileWellTypedCondition decomposes for unaryApp
-/
theorem eliminate_wt_cond_unaryApp
  {op : UnaryOp} {expr : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.unaryApp op expr ty) env εnv) :
  CompileWellTypedCondition expr env εnv
:= by
  have ⟨hwf_env, henv, hwt, hwf⟩ := h
  constructor; any_goals assumption
  constructor
  · cases hwt; assumption
  · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
    rcases hwf with ⟨_, hrefs⟩
    constructor;
    · cases hwt; assumption
    · constructor
      · assumption
      · cases hrefs;
        any_goals assumption

theorem compile_well_typed_unaryApp
  {op : UnaryOp} {expr : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (ihexpr : CompileWellTypedForExpr expr εnv)
  (hcond_unary : CompileWellTypedCondition (.unaryApp op expr ty) env εnv) :
  CompileWellTypedForExpr (.unaryApp op expr ty) εnv
:= by
  have hcond_expr := eliminate_wt_cond_unaryApp hcond_unary
  have ⟨hwf_env, henv, hwt, hwf⟩ := hcond_unary
  have ⟨compile_expr, hcomp_expr, hty_comp_expr⟩ := ihexpr

  have hwf_comp_expr := wt_cond_implies_compile_wf hcond_expr hcomp_expr
  have ⟨hwf_get_comp_expr, hty_get_comp_expr⟩ := wf_option_get hwf_comp_expr hty_comp_expr

  -- Case analysis on the operator
  cases hwt
  case unaryApp _ hopwt =>
  cases hopwt

  -- Some simplification on all goals
  all_goals simp [
    CompileWellTypedForExpr,
    hcomp_expr,
    hty_get_comp_expr,
    TypedExpr.toExpr,
    compile,
    compileApp₁,
    Term.typeOf,
  ]

  case not hty_expr =>
    simp [hty_expr, TermType.ofType] at hty_comp_expr
    simp [hty_expr, TermType.ofType, Factory.someOf]
    rw [typeOf_ifSome_option]
    simp [TypedExpr.typeOf, TermType.ofType, Term.typeOf]

    apply wf_typeOf_not
    any_goals assumption
    any_goals simp

    simp [hty_get_comp_expr, hty_expr, TermType.ofType, Term.typeOf]

  case neg hty_expr =>
    simp [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp [hty_expr, TermType.ofType, Factory.someOf]
    rw [typeOf_ifSome_option]
    simp [TypedExpr.typeOf, TermType.ofType, Term.typeOf, Factory.ifFalse, Factory.noneOf, Factory.someOf]

    have ⟨hwf_bvnego_get_expr, hty_bvnego_get_expr⟩ := wf_bvnego hwf_get_comp_expr hty_get_comp_expr
    have ⟨hwf_bvneg_get_expr, hty_bvneg_get_expr⟩ := wf_bvneg hwf_get_comp_expr hty_get_comp_expr

    apply wf_typeOf_ite
    any_goals assumption
    any_goals simp [TermType.ofType, Term.typeOf, TermPrim.typeOf, Factory.someOf]
    · constructor
      simp [*]
      constructor
    · constructor; assumption
    · simp [*]
    · simp [*]

  case is hty_expr =>
    simp [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp [hty_expr, TermType.ofType, Factory.someOf]
    rw [typeOf_ifSome_option]
    simp [
      TypedExpr.typeOf,
      TermType.ofType,
      Term.typeOf,
      Factory.ifFalse,
      Factory.noneOf,
      Factory.someOf,
      TermPrim.typeOf,
    ]

  case isEmpty elem_ty hty_expr =>
    simp [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp [hty_expr, TermType.ofType, Factory.someOf]
    rw [typeOf_ifSome_option]
    simp [
      TypedExpr.typeOf,
      TermType.ofType,
      Term.typeOf,
      Factory.ifFalse,
      Factory.noneOf,
      Factory.someOf,
      TermPrim.typeOf,
      Factory.set.isEmpty,
    ]

    split
    any_goals simp [Term.typeOf, TermPrim.typeOf]
    simp [hty_get_comp_expr]
    apply wf_typeOf_eq
    any_goals assumption
    any_goals simp [Term.typeOf, hty_get_comp_expr]

    -- Prove that the empty set term is well-formed
    · constructor
      · intros; contradiction
      · intros; contradiction
      · have h : TermType.WellFormed εnv.entities (.set (TermType.ofType elem_ty)) := by
          simp [←hty_get_comp_expr]
          apply typeOf_wf_term_is_wf
          assumption
        cases h; assumption
      · constructor

  case like _ hty_expr =>
    simp [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp [hty_expr, TermType.ofType, Factory.someOf]
    rw [typeOf_ifSome_option]
    simp [
      TypedExpr.typeOf,
      TermType.ofType,
      Term.typeOf,
      Factory.ifFalse,
      Factory.noneOf,
      Factory.someOf,
      TermPrim.typeOf,
      Factory.set.isEmpty,
    ]
    exact (wf_string_like (εs := εnv.entities)
      hwf_get_comp_expr
      hty_get_comp_expr).right

/--
CompileWellTypedCondition decomposes for binaryApp
TODO: merge this with other eliminate_wt_cond_*
-/
theorem eliminate_wt_cond_binaryApp
  {op : BinaryOp} {a : TypedExpr} {b : TypedExpr} {ty : CedarType} {env : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.binaryApp op a b ty) env εnv →
  CompileWellTypedCondition a env εnv ∧
  CompileWellTypedCondition b env εnv
:= by
  intros h; rcases h with ⟨hwf_env, henv, hwt, hwf⟩
  constructor
  all_goals
    constructor
    any_goals assumption

    constructor
    · cases hwt; assumption
    · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
      rcases hwf with ⟨_, hrefs⟩
      constructor;
      · cases hwt; assumption
      · constructor
        · assumption
        · cases hrefs;
          any_goals assumption

/--
If some entity exists in `env`, then it must
also exists in `SymEnv.ofEnv env` with the corresponding `SymEntityData`
-/
theorem ofEnv_lookup_entity
  {env : Environment} {εnv : SymEnv} {ety : EntityType} {entry : EntitySchemaEntry}
  (henv : εnv = SymEnv.ofEnv env)
  (hfound : Data.Map.find? env.ets ety = some entry) :
  Data.Map.find? εnv.entities ety = some (SymEntityData.ofEntityType ety entry)
:= by
  simp [henv, Data.Map.find?, SymEnv.ofEnv, SymEntities.ofSchema, Data.Map.toList]
  simp [Data.Map.find?] at hfound

  -- Simplify hfound
  split at hfound
  any_goals contradiction
  case _ _ _ hfound2 =>
  simp at hfound; simp [hfound] at *;
  have hfound := hfound2; clear hfound2

  have h := List.find?_some hfound
  simp at h
  simp [h] at hfound; clear h

  apply list_key_find?_append_to_map_make_find?
  apply list_key_find?_map
  assumption

/--
Lemma that if a concrete `env : Environment` has tags for
a particular entity type, when `SymEnv.ofEnv env` must also
have tags for it
-/
theorem SymEnv_of_preserves_tags
  {env : Environment} {ety : EntityType} {ty : CedarType}
  (h : env.ets.tags? ety = some (some ty)) :
  ∃ τags : SymTags,
    (SymEnv.ofEnv env).entities.tags ety = τags ∧
    τags.vals.outType = TermType.ofType ty
:= by
  simp [EntitySchema.tags?] at h
  have ⟨found_entry, ⟨hfound, hty_entry⟩⟩ := h

  -- The corresponding entity exists in `εnv`
  have hety_exists :
    Data.Map.find? (SymEnv.ofEnv env).entities ety
    = some (SymEntityData.ofEntityType ety found_entry)
  := by
    apply ofEnv_lookup_entity ?_ hfound
    rfl

  simp [
    hety_exists,
    SymEntities.tags,
    SymEntityData.ofEntityType,
    SymEntityData.ofStandardEntityType,
    SymEntityData.ofEnumEntityType,
  ]
  split <;> simp
  case h_1 std_entry =>
    simp [EntitySchemaEntry.tags?] at hty_entry
    simp [hty_entry, SymEntityData.ofStandardEntityType.symTags, UnaryFunction.outType]
  case h_2 enum_entry => contradiction

/--
Similar to compileApp₂_wf_types, but for compile
-/
theorem compile_binaryApp_wf_types
  {op : BinaryOp} {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {t : Term} {tcomp_a : Term} {tcomp_b : Term}
  {εnv : SymEnv}
  (hwf_ent : εnv.entities.WellFormed)
  (hok_a : compile a.toExpr εnv = Except.ok tcomp_a)
  (hok_b : compile b.toExpr εnv = Except.ok tcomp_b)
  (hwf_get_comp_a : Term.WellFormed εnv.entities (Factory.option.get tcomp_a))
  (hwf_get_comp_b : Term.WellFormed εnv.entities (Factory.option.get tcomp_b))
  (hok : compile (TypedExpr.toExpr (.binaryApp op a b ty)) εnv = .ok t) :

  match op with
    | .add | .sub | .mul => t.typeOf = .option (.bitvec 64)
    | .getTag            =>
      ∃ ety τs,
        (Factory.option.get tcomp_a).typeOf = .entity ety ∧
        εnv.entities.tags ety = some (some τs) ∧
        t.typeOf = τs.vals.outType.option
    | _                  => t.typeOf = .option .bool
:= by
  simp [compile, TypedExpr.toExpr, hok_a, hok_b] at hok
  simp_do_let
    (compileApp₂ op
      (Factory.option.get tcomp_a)
      (Factory.option.get tcomp_b)
      εnv.entities)
    at hok
  simp at hok
  case ok tcomp_app hcomp_app =>

  have h := (compileApp₂_wf_types
    hwf_ent
    hwf_get_comp_a
    hwf_get_comp_b
    hcomp_app
  ).right

  -- tcomp_app and t should have the same type
  have heqty :
    t.typeOf = tcomp_app.typeOf
  := by
    simp [← hok]
    cases op
    any_goals
      simp at h
      simp [h]
      apply typeOf_ifSome_option
      apply typeOf_ifSome_option
      assumption

    -- Special case for getTag
    case getTag =>
      simp at h
      have ⟨_, _, _, _, h⟩ := h
      simp [h]
      apply typeOf_ifSome_option
      apply typeOf_ifSome_option
      assumption

  cases op
  any_goals
    simp at h
    simp [h, heqty]

theorem compile_well_typed_binaryApp
  {op : BinaryOp} {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (iha : CompileWellTypedForExpr a εnv)
  (ihb : CompileWellTypedForExpr b εnv)
  (hcond_binary : CompileWellTypedCondition (.binaryApp op a b ty) env εnv) :
  CompileWellTypedForExpr (.binaryApp op a b ty) εnv
:= by
  -- Some facts needed later
  have ⟨hcond_a, hcond_b⟩ := eliminate_wt_cond_binaryApp hcond_binary
  have ⟨_, henv, hwt_binary, ⟨hwf_εnv, hrefs_binary⟩⟩ := hcond_binary

  have ⟨hwf_req, hwf_ent⟩ := hwf_εnv

  have ⟨tcomp_a, ⟨hcomp_a, hty_comp_a⟩⟩ := iha
  have ⟨tcomp_b, ⟨hcomp_b, hty_comp_b⟩⟩ := ihb

  have hwf_comp_a := wt_cond_implies_compile_wf hcond_a hcomp_a
  have hwf_comp_b := wt_cond_implies_compile_wf hcond_b hcomp_b

  have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
  have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b

  -- For each operator, reduce the goal to simply proving
  -- that compilation succeeds
  have reduce_to_compile_ok
    (hok : ∃ t : Term,
      compile (TypedExpr.toExpr (.binaryApp op a b ty)) εnv = .ok t) :
    CompileWellTypedForExpr (.binaryApp op a b ty) εnv
  := by
    have ⟨t, hok⟩ := hok
    have htypes := compile_binaryApp_wf_types
      hwf_ent hcomp_a hcomp_b hwf_get_comp_a hwf_get_comp_b hok

    cases hwt_binary
    case binaryApp _ hopwt =>
    cases hopwt

    all_goals simp [
      CompileWellTypedForExpr,
      hcomp_a,
      hty_get_comp_a,
      hcomp_b,
      hty_get_comp_b,
      TypedExpr.toExpr,
      Term.typeOf,
      TermType.ofType,
      TypedExpr.typeOf,
    ]

    any_goals
      simp [TypedExpr.toExpr] at hok
      simp at htypes
      simp [hok, htypes]

    -- Special case for geTag
    case getTag _ ety tags htag hty_a hty_b _ _ =>
      have ⟨ety2, hty_get_comp_a2, τs, hτag, hτag_ty⟩ := htypes
      rw [← ofType_ignores_liftBool]

      have ⟨τs2, hτag2, hτag_ty2⟩ := SymEnv_of_preserves_tags htag

      have heq_ety : ety = ety2 := by
        simp [hty_get_comp_a, hty_a, TermType.ofType] at hty_get_comp_a2
        assumption

      have hτs : τs = τs2 := by
        simp [← henv, heq_ety, hτag] at hτag2
        assumption

      simp [← hτag_ty2, hτag_ty, hτs]

  -- Reduce to proving that compilation succeeds
  apply reduce_to_compile_ok
  cases hwt_binary
  case binaryApp _ hopwt =>
  cases hopwt

  -- Apply some common definitions
  all_goals
    unfold compile TypedExpr.toExpr
    simp [hcomp_a, hcomp_b]
    simp [compileApp₂, hty_get_comp_a, hty_get_comp_b]

  -- Most cases in `BinaryOp.WellTyped`
  -- have the form <case> (a.typeOf = ...) (b.typeOf = ...)
  -- which can be resolved by some simplification
  any_goals try case _ hty_a hty_b =>
    simp [hty_a, hty_b, TermType.ofType]

  case eq_entity hty_a hty_b =>
    simp [
      hty_a, hty_b,
      TermType.ofType,
      reducibleEq,
      TermType.isPrimType,
      TypedExpr.toExpr,
    ]
    split <;> simp

  case eq_lit p1 p2 pty1 pty2 hprim1 hprim2 =>
    -- Prove that both types would are primitive types
    cases hprim1; case lit hprim1 =>
    cases hprim2; case lit hprim2 =>
    have hprim1 : TermType.isPrimType (TermType.ofType pty1) := by
      cases hprim1; all_goals simp [TermType.ofType, TermType.isPrimType]
    have hprim2 : TermType.isPrimType (TermType.ofType pty2) := by
      cases hprim2; all_goals simp [TermType.ofType, TermType.isPrimType]
    simp [
      hprim1, hprim2,
      TypedExpr.toExpr,
      TypedExpr.typeOf,
      reducibleEq,
    ]
    split <;> simp

  case eq _ heqty =>
    simp [heqty, compileApp₂, TermType.ofType, reducibleEq]

  case hasTag ety hty_a hty_b =>
    simp [
      henv,
      hty_a, hty_b,
      hty_get_comp_a, hty_get_comp_b,
      compileHasTag,
      TermType.ofType,
    ]

    -- Show that `ety` is a valid entity type
    -- from the fact that `tcomp_a` is well-formed
    -- (so its (entity) type is well-formed)
    simp [hty_a, TermType.ofType] at hty_comp_a
    have hwf_ty_a := typeOf_wf_term_is_wf hwf_comp_a
    simp [hty_comp_a] at hwf_ty_a

    cases hwf_ty_a; case option_wf hwf_ty_a =>
    cases hwf_ty_a; case entity_wf hwf_ty_a =>
    simp [SymEntities.isValidEntityType] at hwf_ty_a

    have ⟨_, hety_exists⟩ :=
      Cedar.Data.Map.contains_iff_some_find?.mp hwf_ty_a

    simp [SymEntities.tags, ← henv, hety_exists]
    split
    any_goals contradiction
    all_goals simp

  case getTag _ _ htag hty_a hty_b =>
    have ⟨_, hτag, _⟩ := SymEnv_of_preserves_tags htag
    simp [← henv] at hτag
    simp [hty_a, hty_b, hτag, compileGetTag, TermType.ofType]

/--
If some attribute exists in a record type,
then it should still exist after applying `TermType.ofRecordType`
-/
theorem ofRecordType_lookup
  {rty : RecordType} {attr : Attr} {qty : Qualified CedarType} {ty : CedarType}
  (hattr_exists : Data.Map.find? rty attr = some qty)
  (hattr_ty : qty.getType = ty) :
  ∃ attr_ty : TermType,
    (Data.Map.mk (TermType.ofRecordType rty.1)).find? attr = some attr_ty ∧
    match attr_ty with
    | .option attr_ty' => TermType.ofType ty = attr_ty' ∧ ¬qty.isRequired
    | _ => TermType.ofType ty = attr_ty ∧ qty.isRequired
:= by
  cases rty
  case mk rty_1 =>
  induction rty_1
  case nil =>
    simp [Data.Map.find?, List.find?] at hattr_exists

  case cons head tail ih =>
    rcases head with ⟨k, v⟩
    simp [TermType.ofRecordType, Data.Map.find?, List.find?]
    simp [Data.Map.find?, List.find?] at hattr_exists ih

    cases e : k == attr
    simp [e] at *

    case false => apply ih hattr_exists
    case true =>
      simp [e] at hattr_exists
      simp [hattr_exists, TermType.ofQualifiedType]
      cases qty

      case optional =>
        simp [TermType.ofQualifiedType, Qualified.isRequired]
        simp [Qualified.getType] at hattr_ty
        simp [hattr_ty]

      case required =>
        simp [TermType.ofQualifiedType, Qualified.isRequired]
        simp [Qualified.getType] at hattr_ty
        simp [hattr_ty]

        -- TermType.ofType never produces an option type
        unfold TermType.ofType
        split
        case h_1 hof_type =>
          split at hof_type
          all_goals contradiction
        simp

-- Given that
--   env.ets.attrs? ety = some a
--   a.liftBoolTypes = rty
-- Show that
--   (SymEnv.ofEnv env).entities.attrs ety = .some attrs
--   UnaryFunction.WellFormed εnv.entities attrs
--   attrs.argType = CedarType.entity ety
--   attrs.outType = .record (Data.Map.mk (TermType.ofRecordType rty.1))

/--
`SymEnv` being well-formed implies that any
attribute function is well-formed
-/
theorem env_wf_implies_attrs_wf
  {εnv : SymEnv} {ety : EntityType} {attrs : UnaryFunction}
  (hwf : εnv.WellFormed)
  (hattrs_exists : εnv.entities.attrs ety = .some attrs) :
  UnaryFunction.WellFormed εnv.entities attrs ∧
  attrs.argType = .entity ety ∧
  attrs.outType.isCedarRecordType
:= by
  have ⟨_, _, hwf_entities⟩ := hwf
  simp [SymEntities.attrs] at hattrs_exists
  simp_do_let (Data.Map.find? εnv.entities ety) at hattrs_exists
  contradiction

  case some d hety_exists =>
    have ⟨h1, h2, h3, _⟩ := hwf_entities ety d hety_exists
    simp at hattrs_exists
    simp [hattrs_exists] at h1 h2 h3
    simp [h1, h2, h3]

/--
Show that `SymEnv.ofEnv env` preserves the result of attribute lookup
-/
theorem ofEnv_entity_attr_lookup
  {env : Environment} {εnv : SymEnv}
  {rty : RecordType} {ety : EntityType}
  (henv : εnv = SymEnv.ofEnv env)
  (hattrs_exists : env.ets.attrs? ety = some rty)
  (hwf : εnv.WellFormed) :
  ∃ attrs : UnaryFunction,
    εnv.entities.attrs ety = .some attrs ∧
    UnaryFunction.WellFormed εnv.entities attrs ∧
    attrs.argType = .entity ety ∧
    attrs.outType = .record (Data.Map.mk (TermType.ofRecordType rty.1))
:= by
  simp [EntitySchema.attrs?, Data.Map.find?] at hattrs_exists

  split at hattrs_exists
  all_goals simp at hattrs_exists
  case h_1 found_ety found_entry hfound =>

  -- The corresponding entity exists in `εnv`
  have hety_exists :
    Data.Map.find? εnv.entities ety
    = some (SymEntityData.ofEntityType ety found_entry)
  := by
    apply ofEnv_lookup_entity henv
    simp [Data.Map.find?, hfound]

  have ⟨attrs, hattrs_exists2⟩ :
    ∃ attrs : UnaryFunction, εnv.entities.attrs ety = .some attrs
  := by
    simp [SymEntities.attrs, hety_exists]

  have ⟨hwf_attrs, hty_arg_attrs⟩ := env_wf_implies_attrs_wf hwf hattrs_exists2

  apply Exists.intro attrs
  constructor

  -- Entity type exists in `εnv.entities`
  · assumption

  -- Some well-formedness and well-typedness conditions
  · simp [hwf_attrs, hty_arg_attrs]

    -- TODO: show that the `attrs.outType` is `TermType.ofRecordType rty.1`
    simp [
      SymEntities.attrs,
      hety_exists,
      SymEntityData.ofEntityType,
      SymEntityData.ofStandardEntityType,
      SymEntityData.ofEnumEntityType,
      SymEntityData.ofStandardEntityType.attrsUUF,
      SymEntityData.emptyAttrs,
    ] at hattrs_exists2
    split at hattrs_exists2 <;> simp at hattrs_exists2

    -- Standard entity types
    · simp [← hattrs_exists2, UnaryFunction.outType, TermType.ofType]
      simp [EntitySchemaEntry.attrs] at hattrs_exists
      simp [hattrs_exists]

    -- Enum entity types
    · simp [← hattrs_exists2, UnaryFunction.outType, TermType.ofType]
      simp [EntitySchemaEntry.attrs] at hattrs_exists
      simp [← hattrs_exists, TermType.ofRecordType, Data.Map.empty]

/--
CompileWellTypedCondition decomposes for getAttr
-/
theorem eliminate_wt_cond_getAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.getAttr expr attr ty) env εnv) :
  CompileWellTypedCondition expr env εnv
:= by
  have ⟨hwf_env, henv, hwt, hwf⟩ := h
  constructor; any_goals assumption
  constructor
  · cases hwt; any_goals assumption
  · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
    rcases hwf with ⟨_, hrefs⟩
    constructor;
    · cases hwt; any_goals assumption
    · constructor
      · assumption
      · cases hrefs;
        any_goals assumption

theorem compile_well_typed_getAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (ihexpr : CompileWellTypedForExpr expr εnv)
  (hcond : CompileWellTypedCondition (.getAttr expr attr ty) env εnv) :
  CompileWellTypedForExpr (.getAttr expr attr ty) εnv
:= by
  have hcond_expr := eliminate_wt_cond_getAttr hcond
  have ⟨_, henv, hwt, hwf_εnv, hrefs⟩ := hcond
  have ⟨compile_expr, hcomp_expr, hty_comp_expr⟩ := ihexpr

  have hwf_comp_expr := wt_cond_implies_compile_wf hcond_expr hcomp_expr
  have ⟨hwf_get_comp_expr, hty_get_comp_expr⟩ := wf_option_get hwf_comp_expr hty_comp_expr

  cases hwt

  case getAttr_entity ety rty hent_attrs_exists hwt_expr hty_expr henv_attr_lookup =>
    simp [
      CompileWellTypedForExpr,
      compile,
      compileGetAttr,
      compileAttrsOf,
      TypedExpr.toExpr,
      TermType.ofType,
      hcomp_expr,
      hty_get_comp_expr,
      hty_comp_expr,
      hty_expr,
    ]

    simp at hent_attrs_exists
    have ⟨rty2, hrty2, hrty_rty2⟩ := hent_attrs_exists

    simp at henv_attr_lookup
    have ⟨attr_ty, henv_attr_lookup, hty_env_attr⟩ := henv_attr_lookup

    -- Show some facts about `εnv` from the hypotheses in `getAttr_entity`
    have ⟨
      attrs, _, attr_ty,
      hattrs_exists, hwf_attrs, hattr_input,
      hattr_isrec, hattr_exists, hattr_ty_eq,
    ⟩ :
      ∃ (attrs : UnaryFunction)
        (rty : Data.Map Attr TermType)
        (attr_ty : TermType),

        -- Entity type has attrs
        εnv.entities.attrs ety = .some attrs ∧

        -- The symbolic attrs is "well-formed"
        UnaryFunction.WellFormed εnv.entities attrs ∧
        (Factory.option.get compile_expr).typeOf = attrs.argType ∧
        (Factory.app attrs (Factory.option.get compile_expr)).typeOf = .record rty ∧

        rty.find? attr = some attr_ty ∧

        -- Result type matches attr_ty
        match attr_ty with
        | .option attr_ty' => TermType.ofType ty = attr_ty'
        | _ => TermType.ofType ty = attr_ty
    := by
      have ⟨_, h1, h2, h3, h4⟩ := ofEnv_entity_attr_lookup henv hrty2 hwf_εnv

      simp [hty_expr, TermType.ofType] at hty_get_comp_expr
      simp [h1, h2, h3, h4, hty_get_comp_expr]

      apply Exists.intro (Data.Map.mk (TermType.ofRecordType rty2.1))
      constructor

      -- Types of symbolic attrs are correct
      · simp [← h4]
        apply (wf_app (εs := εnv.entities) hwf_get_comp_expr ?_ ?_).right
        simp [hty_get_comp_expr, h3]
        apply h2

      -- (hattr_exists : Data.Map.find? rty attr = some qty)
      -- (hattr_ty : qty.getType = ty) :
      have ⟨_, h1, h2⟩ := ofRecordType_lookup henv_attr_lookup hty_env_attr

      -- Finally, show that TermType is agnostic to `rty2` and `rty2.liftBoolTypes`
      have hlift := ofRecordType_ignores_liftBool rty2.1
      simp [RecordType.liftBoolTypes] at hrty_rty2
      simp [← hrty_rty2] at hlift
      simp [← hrty_rty2, ← hlift] at h1
      simp [h1]
      split at h2 <;> simp [h2]

    simp [hattrs_exists, hattr_isrec, hattr_exists]
    split
    any_goals contradiction

    -- When the field is optional
    case h_1 _ _ h =>
      simp at h; simp [h] at hattr_ty_eq
      simp [TypedExpr.typeOf]
      apply typeOf_ifSome_option
      rw [(wf_record_get (εs := εnv.entities) ?_ hattr_isrec hattr_exists).right]
      · simp [hattr_ty_eq]; assumption
      · apply (wf_app hwf_get_comp_expr hattr_input hwf_attrs).left

    -- When the field is not optional
    case h_2 _ _ h =>
      simp at h; simp [h] at hattr_ty_eq
      simp [TypedExpr.typeOf, Factory.someOf]
      apply typeOf_ifSome_option
      simp [Term.typeOf]
      rw [(wf_record_get (εs := εnv.entities) ?_ hattr_isrec hattr_exists).right]
      · simp [hattr_ty_eq]; assumption
      · apply (wf_app hwf_get_comp_expr hattr_input hwf_attrs).left

  case getAttr_record rty _ hty_expr henv_attr_lookup =>
    simp [hty_expr, TermType.ofType] at hty_get_comp_expr
    simp [
      CompileWellTypedForExpr,
      compile,
      compileGetAttr,
      compileAttrsOf,
      TypedExpr.toExpr,
      TermType.ofType,
      hcomp_expr,
      hty_get_comp_expr,
      hty_comp_expr,
      hty_expr,
    ]

    -- Some some facts about record attr lookup
    -- from hypotheses in `getAttr_record` and `ofRecordType_lookup`
    have ⟨attr_ty, hattr_exists, hattr_ty_eq⟩ :
      ∃ attr_ty : TermType,
        (Data.Map.mk (TermType.ofRecordType rty.1)).find? attr = some attr_ty ∧
        -- Result type matches attr_ty
        match attr_ty with
        | .option attr_ty' => TermType.ofType ty = attr_ty'
        | _ => TermType.ofType ty = attr_ty
    := by
      simp at henv_attr_lookup
      have ⟨field_ty, field_exists, hfield_ty⟩ := henv_attr_lookup
      have ⟨attr_ty, h1, h2⟩ := ofRecordType_lookup field_exists hfield_ty
      simp [h1]; split
      all_goals simp at h2; simp [h2]

    simp [hattr_exists]
    split
    any_goals contradiction

    -- Optional field
    case h_1 _ h =>
      simp [TypedExpr.typeOf]
      apply typeOf_ifSome_option
      rw [(wf_record_get (εs := εnv.entities)
        hwf_get_comp_expr
        hty_get_comp_expr hattr_exists).right]
      simp at h
      simp [h] at hattr_ty_eq
      simp [h, hattr_ty_eq]

    -- Required field
    case h_2 _ h =>
      simp [TypedExpr.typeOf, Factory.someOf]
      apply typeOf_ifSome_option
      simp [Term.typeOf]
      rw [(wf_record_get (εs := εnv.entities)
        hwf_get_comp_expr
        hty_get_comp_expr hattr_exists).right]
      simp at h
      simp [h] at hattr_ty_eq
      simp [h, hattr_ty_eq]

/--
CompileWellTypedCondition decomposes for hasAttr
-/
theorem eliminate_wt_cond_hasAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.hasAttr expr attr ty) env εnv) :
  CompileWellTypedCondition expr env εnv
:= by
  have ⟨hwf_env, henv, hwt, hwf⟩ := h
  constructor; any_goals assumption
  constructor
  · cases hwt; any_goals assumption
  · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
    rcases hwf with ⟨_, hrefs⟩
    constructor;
    · cases hwt; any_goals assumption
    · constructor
      · assumption
      · cases hrefs;
        any_goals assumption

theorem compile_well_typed_hasAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (ihexpr : CompileWellTypedForExpr expr εnv)
  (hcond : CompileWellTypedCondition (.hasAttr expr attr ty) env εnv) :
  CompileWellTypedForExpr (.hasAttr expr attr ty) εnv
:= by
  have hcond_expr := eliminate_wt_cond_hasAttr hcond
  have ⟨_, henv, hwt, hwf_εnv, hrefs⟩ := hcond
  have ⟨compile_expr, hcomp_expr, hty_comp_expr⟩ := ihexpr

  have hwf_comp_expr := wt_cond_implies_compile_wf hcond_expr hcomp_expr
  have ⟨hwf_get_comp_expr, hty_get_comp_expr⟩ := wf_option_get hwf_comp_expr hty_comp_expr

  cases hwt

  case hasAttr_entity ety hwt_expr hty_expr =>
     -- Show that `ety` is a valid entity type
    -- from the fact that `tcomp_a` is well-formed
    -- (so its (entity) type is well-formed)
    simp [hty_expr, TermType.ofType] at hty_comp_expr
    have hwf_ty_expr := typeOf_wf_term_is_wf hwf_comp_expr
    simp [hty_comp_expr] at hwf_ty_expr

    cases hwf_ty_expr; case option_wf hwf_ty_expr =>
    cases hwf_ty_expr; case entity_wf hwf_ty_expr =>
    simp [SymEntities.isValidEntityType] at hwf_ty_expr

    have ⟨sym_ety_data, hety_exists⟩ :=
      Cedar.Data.Map.contains_iff_some_find?.mp hwf_ty_expr

    simp [
      CompileWellTypedForExpr,
      compile,
      compileHasAttr,
      compileAttrsOf,
      TypedExpr.toExpr,
      TermType.ofType,
      SymEntities.attrs,
      hcomp_expr,
      hty_get_comp_expr,
      hty_comp_expr,
      hty_expr,
      hety_exists,
    ]

    have hattrs_exists :
      εnv.entities.attrs ety = .some sym_ety_data.attrs
    := by
      simp [SymEntities.attrs, hety_exists]

    have ⟨
      hwf_attrs,
      hty_attrs_arg,
      hty_attrs_out,
    ⟩ := env_wf_implies_attrs_wf hwf_εnv hattrs_exists

    have ⟨rty, hty_attrs_out⟩ :
      ∃ rty : Data.Map Attr TermType,
        sym_ety_data.attrs.outType = .record rty
    := by
      have hty_attrs_out := isCedarRecordType_implies_isRecordType hty_attrs_out
      simp [TermType.isRecordType] at hty_attrs_out
      cases e : sym_ety_data.attrs.outType
      all_goals simp [e] at hty_attrs_out
      simp [e]

    have hty_app_attrs :
      (Factory.app sym_ety_data.attrs (Factory.option.get compile_expr)).typeOf
      = .record rty
    := by
      simp [← hty_attrs_out]
      apply (wf_app (εs := εnv.entities) hwf_get_comp_expr ?_ ?_).right

      simp [hty_expr] at hty_get_comp_expr
      simp [hty_get_comp_expr]
      simp [hty_attrs_arg, TermType.ofType]
      exact hwf_attrs

    simp [hty_app_attrs]
    split <;> simp

    -- Optional field
    case _ hattr_exists =>
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        Factory.isSome,
      ]

      apply (wf_not (εs := εnv.entities) ?_ ?_).right

      apply (wf_isNone (εs := εnv.entities) ?_).left
      rotate_left
      apply (wf_isNone (εs := εnv.entities) ?_).right

      all_goals
        apply (wf_record_get ?_ hty_app_attrs hattr_exists).left
        apply (wf_app ?_ ?_ ?_).left
        exact hwf_get_comp_expr
        simp [hty_get_comp_expr, hty_expr, TermType.ofType, hty_attrs_arg]
        exact hwf_attrs

    -- Required field
    case _ =>
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        Factory.isSome, TermPrim.typeOf,
      ]

    -- Attribute does not exist
    case _ =>
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        Factory.isSome, TermPrim.typeOf,
      ]

  case hasAttr_record rty hwt_expr hty_expr =>
    simp [
      CompileWellTypedForExpr,
      compile,
      compileHasAttr,
      compileAttrsOf,
      TypedExpr.toExpr,
      TermType.ofType,
      SymEntities.attrs,
      hcomp_expr,
      hty_get_comp_expr,
      hty_comp_expr,
      hty_expr,
    ]

    simp [hty_expr, TermType.ofType] at hty_get_comp_expr

    split <;> simp

    -- Optional attribute
    case _ hattr_exists =>
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        Factory.isSome,
      ]

      apply (wf_not (εs := εnv.entities) ?_ ?_).right

      apply (wf_isNone (εs := εnv.entities) ?_).left
      rotate_left
      apply (wf_isNone (εs := εnv.entities) ?_).right
      all_goals
        apply (wf_record_get hwf_get_comp_expr hty_get_comp_expr hattr_exists).left

    -- Required attribute
    case _ hattr_exists =>
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        Factory.isSome, TermPrim.typeOf,
      ]

    -- Attribute does not exist
    case _ =>
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        Factory.isSome, TermPrim.typeOf,
      ]

/--
CompileWellTypedCondition decomposes for set
-/
theorem eliminate_wt_cond_set
  {xs : List TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.set xs ty) env εnv)
  (x : TypedExpr)
  (hx : x ∈ xs) :
  CompileWellTypedCondition x env εnv
:= by
  have ⟨hwf_env, henv, hwt, hwf⟩ := h
  constructor; any_goals assumption
  constructor
  · cases hwt; any_goals assumption
  · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
    rcases hwf with ⟨_, hrefs⟩
    constructor;
    · cases hwt with
      | set h1 =>
        apply h1; assumption
    · constructor
      · assumption
      · cases hrefs with
        | set_valid h =>
          apply h
          simp [List.map₁]
          apply Exists.intro x
          simp [hx]

theorem compile_well_typed_set
  {xs : List TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (ihxs : ∀ x, x ∈ xs → CompileWellTypedForExpr x εnv)
  (hcond : CompileWellTypedCondition (.set xs ty) env εnv) :
  CompileWellTypedForExpr (.set xs ty) εnv
:= by
  have hcond_xs := eliminate_wt_cond_set hcond
  have ⟨_, henv, hwt, hwf_εnv, hrefs⟩ := hcond

  simp [
    CompileWellTypedForExpr,
    TypedExpr.toExpr,
    compile,
    compileSet,
    List.map₁,
    List.mapM₁,
  ]

  -- Prove that mapM over `compile` succeeds
  have ⟨tcomp_xs, hcomp_xs⟩ :
    ∃ tcomp_xs,
    List.mapM (fun x => compile x.val εnv) (List.map TypedExpr.toExpr xs).attach
    = Except.ok tcomp_xs
  := by
    apply List.all_ok_implies_mapM_ok
    simp
    intros x hx
    have ⟨_, h, _⟩ := ihxs x hx
    simp [h]
  simp [hcomp_xs]

  -- Get some info from well-typedness
  cases hwt with
  | set hwt_xs hty_sx hnon_empty =>
  case _ ty =>

  simp at hnon_empty

  have htcomp_xs_non_empty :
    tcomp_xs ≠ []
  := by
    intros hcontra
    simp [hcontra] at hcomp_xs
    have hxs_empty := List.mapM_implies_nil hcomp_xs
    simp at hxs_empty
    exact hnon_empty hxs_empty

  -- Prove that each compiled result has the correct type
  have hty_comp_xs :
    ∀ y ∈ tcomp_xs,
      y.typeOf = (TermType.ofType ty).option ∧
      Term.WellFormed εnv.entities y
  := by
    intros y hy
    have ⟨⟨x', hx⟩, _, hcomp_x⟩ := List.mapM_ok_implies_all_from_ok hcomp_xs y hy
    simp at hx
    have ⟨x, hx, hx_to_x'⟩ := hx
    have ⟨_, hcomp_x2, hty_comp_x⟩ := ihxs x hx

    simp at hcomp_x
    simp [← hx_to_x', hcomp_x2] at hcomp_x
    simp [← hcomp_x, hty_comp_x]
    simp [hty_sx x hx]

    apply (compile_wf ?_ hcomp_x2).left
    exact (hcond_xs x hx).2.2.2

  -- Prove that Option.get of each compiled result has the correct type
  have hty_get_comp_xs :
    ∀ y ∈ List.map Factory.option.get tcomp_xs,
      y.typeOf = TermType.ofType ty ∧
      Term.WellFormed εnv.entities y
  := by
    intros y hy
    simp at hy
    have ⟨y', hy', hy_to_y'⟩ := hy

    have ⟨hty_y', hwf_y'⟩ := hty_comp_xs y' hy'
    simp [← hy_to_y']
    constructor
    · exact (wf_option_get hwf_y' hty_y').right
    · exact (wf_option_get hwf_y' hty_y').left

  cases tcomp_xs with
  | nil => contradiction
  | cons tcomp_xs_hd tcomp_xs_tl =>
    simp
    split
    case _ hopt =>
      have h1 :
        ∀ (a : Term), a ∈ tcomp_xs_tl → a.typeOf = (TermType.ofType ty).option
      := by
        intros a ha
        apply (hty_comp_xs a ?_).left
        simp [ha]

      have h2 :
        tcomp_xs_hd.typeOf = (TermType.ofType ty).option
      := by
        apply (hty_comp_xs tcomp_xs_hd ?_).left
        simp

      simp [hopt] at h2
      simp [hopt, h2]
      split
      any_goals contradiction
      simp

      -- Finally, resolve some typing constraints
      apply (wf_ifAllSome (εs := εnv.entities) ?_ ?_ ?_).right

      intros g hg
      apply (hty_comp_xs g hg).right

      · constructor
        apply (wf_setOf ?_ ?_ ?_).left

        . intros t ht; apply (hty_get_comp_xs t ht).right
        · intros t ht; apply (hty_get_comp_xs t ht).left
        · have h := hty_get_comp_xs (Factory.option.get tcomp_xs_hd)
          simp at h
          simp [← h.left]
          apply typeOf_wf_term_is_wf
          apply h.right

      · simp [Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf]
        apply (wf_setOf (εs := εnv.entities) ?_ ?_ ?_).right

        . intros t ht; apply (hty_get_comp_xs t ht).right
        . intros t ht; apply (hty_get_comp_xs t ht).left
        · have h := hty_get_comp_xs (Factory.option.get tcomp_xs_hd)
          simp at h
          simp [← h.left]
          apply typeOf_wf_term_is_wf
          apply h.right

    case _ hnot_opt =>
      have hty_comp_xs_hd := hty_comp_xs tcomp_xs_hd
      simp at hty_comp_xs_hd
      simp [hty_comp_xs_hd] at hnot_opt

/--
Compiling a well-typed expression should produce a term of the corresponding TermType.
-/
theorem compile_well_typed {env : Environment} {εnv : SymEnv} {ty : TypedExpr} :
  CompileWellTypedCondition ty env εnv →
  CompileWellTypedForExpr ty εnv
:= by
  intros h
  cases ty
  case lit => exact compile_well_typed_lit h
  case var => exact compile_well_typed_var h
  case ite =>
    have ⟨h1, h2, h3⟩ := eliminate_wt_cond_ite h
    apply compile_well_typed_ite
    any_goals apply compile_well_typed
    any_goals assumption

  case and =>
    have ⟨ha, hb⟩ := eliminate_wt_cond_or_and h ?_
    apply (compile_well_typed_or_and ?_ ?_).right
    any_goals apply compile_well_typed
    any_goals assumption
    any_goals simp

  case or =>
    have ⟨ha, hb⟩ := eliminate_wt_cond_or_and h ?_
    apply (compile_well_typed_or_and ?_ ?_).left
    any_goals apply compile_well_typed
    any_goals assumption
    any_goals simp

  case unaryApp =>
    have hcond := eliminate_wt_cond_unaryApp h
    apply compile_well_typed_unaryApp
    any_goals apply compile_well_typed
    all_goals assumption

  case binaryApp =>
    have ⟨ha, hb⟩ := eliminate_wt_cond_binaryApp h
    apply compile_well_typed_binaryApp
    any_goals apply compile_well_typed
    any_goals assumption

  case getAttr =>
    have hcond := eliminate_wt_cond_getAttr h
    apply compile_well_typed_getAttr
    any_goals apply compile_well_typed
    all_goals assumption

  case hasAttr =>
    have hcond := eliminate_wt_cond_hasAttr h
    apply compile_well_typed_hasAttr
    any_goals apply compile_well_typed
    all_goals assumption

  case set =>
    have hcond := eliminate_wt_cond_set h
    apply compile_well_typed_set
    · intros x hx
      apply compile_well_typed (hcond x hx)
    assumption

  case record =>
    sorry

  case call =>
    sorry

-- theorem compile_well_typed_expr_never_fails {ty : TypedExpr} {env : Environment} {εnv : SymEnv} :
--   εnv = SymEnv.ofEnv env →
--   TypedExpr.WellTyped env ty →
--   εnv.WellFormedFor ty.toExpr →
--   Except.isOk (compile ty.toExpr εnv)
-- := by
--   sorry

end Cedar.Thm
