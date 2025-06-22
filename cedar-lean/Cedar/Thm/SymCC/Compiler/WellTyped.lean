import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

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
  εnv = SymEnv.ofEnv env ∧
  TypedExpr.WellTyped env ty ∧
  εnv.WellFormedFor ty.toExpr

/--
A wrapper around compile_wf for convenience
-/
theorem wt_cond_implies_compile_wf
  {ty : TypedExpr} {env : Environment} {εnv : SymEnv} {t : Term} :
  CompileWellTypedCondition ty env εnv →
  compile ty.toExpr εnv = .ok t →
  t.WellFormed εnv.entities
:= by
  intros h hcomp; rcases h with ⟨henv, hwt, hwf⟩
  have htwf := compile_wf hwf hcomp
  simp [htwf]

/--
Special case for literals
-/
theorem compile_well_typed_lit {p : Prim} {ty : CedarType} {env : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.lit p ty) env εnv →
  CompileWellTypedForExpr (.lit p ty) εnv
:= by
  intros h; rcases h with ⟨henv, hwt, hwf⟩
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
  intros h; rcases h with ⟨henv, hwt, hwf⟩
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

theorem compile_well_typed_ite
  {cond : TypedExpr} {thenExpr : TypedExpr} {elseExpr : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}:
  CompileWellTypedCondition (.ite cond thenExpr elseExpr ty) env εnv →
  CompileWellTypedForExpr (.ite cond thenExpr elseExpr ty) εnv
:= by
  intros h; rcases h with ⟨henv, hwt, hwf⟩
  simp [TypedExpr.typeOf, TypedExpr.toExpr, CompileWellTypedForExpr] at *
  sorry

/--
CompileWellTypedCondition decomposes for and
-/
theorem eliminate_wt_cond_and {a : TypedExpr} {b : TypedExpr} {ty : CedarType} {env : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.and a b ty) env εnv →
  CompileWellTypedCondition a env εnv ∧
  CompileWellTypedCondition b env εnv
:= by
  intros h; rcases h with ⟨henv, hwt, hwf⟩
  constructor
  all_goals
    constructor
    any_goals assumption

    constructor
    · cases hwt; assumption
    · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
      rcases hwf with ⟨_, hrefs⟩
      constructor; assumption
      cases hrefs; assumption

theorem compile_well_typed_and
  {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (iha: CompileWellTypedForExpr a εnv)
  (ihb : CompileWellTypedForExpr b εnv)
  (hcond_and : CompileWellTypedCondition (.and a b ty) env εnv) :
  CompileWellTypedForExpr (.and a b ty) εnv
:= by
  -- Some facts needed later
  have ⟨hcond_a, hcond_b⟩ := eliminate_wt_cond_and hcond_and
  have ⟨henv, hwt_and, hwf_and⟩ := hcond_and

  have ⟨tcomp_a, ⟨hcomp_a, hty_comp_a⟩⟩ := iha
  have ⟨tcomp_b, ⟨hcomp_b, hty_comp_b⟩⟩ := ihb

  have hwf_comp_a := wt_cond_implies_compile_wf hcond_a hcomp_a
  have hwf_comp_b := wt_cond_implies_compile_wf hcond_b hcomp_b

  have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
  have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b

  -- By well-typedness, a and b must be booleans
  -- So we substitute that fact and simplify
  cases hwt_and; case and _ hbool_a _ hbool_b =>
  simp [hbool_a, hbool_b] at *; clear hbool_a hbool_b
  simp [TypedExpr.typeOf, TermType.ofType] at *

  simp [
    CompileWellTypedForExpr,
    TypedExpr.toExpr,
    compile,
    compileAnd,
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
  {op : UnaryOp} {expr : TypedExpr} {ty : CedarType} {env : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.unaryApp op expr ty) env εnv →
  CompileWellTypedCondition expr env εnv
:= by
  intros h; rcases h with ⟨henv, hwt, hwf⟩
  constructor; any_goals assumption
  constructor
  · cases hwt; assumption
  · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
    rcases hwf with ⟨_, hrefs⟩
    constructor; assumption
    cases hrefs; assumption

theorem compile_well_typed_unaryApp
  {op : UnaryOp} {expr : TypedExpr} {ty : CedarType}
  {env : Environment} {εnv : SymEnv}
  (ihexpr : CompileWellTypedForExpr expr εnv)
  (hcond_unary : CompileWellTypedCondition (.unaryApp op expr ty) env εnv) :
  CompileWellTypedForExpr (.unaryApp op expr ty) εnv
:= by
  have hcond_expr := eliminate_wt_cond_unaryApp hcond_unary
  have ⟨henv, hwt, hwf⟩ := hcond_unary
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

  case like => sorry

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
  intros h; rcases h with ⟨henv, hwt, hwf⟩
  constructor
  all_goals
    constructor
    any_goals assumption

    constructor
    · cases hwt; assumption
    · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
      rcases hwf with ⟨_, hrefs⟩
      constructor; assumption
      cases hrefs; assumption

set_option maxHeartbeats 300000

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
  have ⟨_, ⟨h1, h2⟩⟩ := h

  -- have _ := Cedar.Data.Map.in_list_iff_find?_some.mpr

  -- apply Cedar.Data.Map.in_list_iff_find?_some at h1

  simp [
    SymEnv.ofEnv,
    SymEntities.ofSchema,
    SymEntities.tags,
    Cedar.Data.Map.find?,
  ]
  sorry

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
  have ⟨henv, hwt_binary, ⟨hwf_env, hrefs_binary⟩⟩ := hcond_binary

  have ⟨hwf_req, hwf_ent⟩ := hwf_env

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
    -- hasTag succeeds as long as `ety` is valid
    -- so we just need that fact

    -- have ⟨τag, htag⟩ := SymEnv_of_preserves_tags htag
    simp [
      henv,
      hty_a, hty_b,
      hty_get_comp_a, hty_get_comp_b,
      compileHasTag,
      TermType.ofType,
    ]
    -- unfold SymEntities.ValidRefsFor at hrefs_binary
    -- simp [TypedExpr.toExpr] at hrefs_binary

    -- cases hrefs_binary
    -- case binaryApp_valid hrefs_a _ =>

    -- TODO: need to somehow deduce
    --       from `a.typeOf = CedarType.entity ety✝`
    --       that ety is a good entity
    -- apply hres_ty
    sorry

  case getTag _ _ htag hty_a hty_b =>
    have ⟨_, hτag, _⟩ := SymEnv_of_preserves_tags htag
    simp [← henv] at hτag
    simp [hty_a, hty_b, hτag, compileGetTag, TermType.ofType]

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
  case ite => exact compile_well_typed_ite h
  case and =>
    have ⟨ha, hb⟩ := eliminate_wt_cond_and h
    apply compile_well_typed_and
    any_goals apply compile_well_typed
    all_goals assumption

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

  all_goals sorry

-- theorem compile_well_typed_expr_never_fails {ty : TypedExpr} {env : Environment} {εnv : SymEnv} :
--   εnv = SymEnv.ofEnv env →
--   TypedExpr.WellTyped env ty →
--   εnv.WellFormedFor ty.toExpr →
--   Except.isOk (compile ty.toExpr εnv)
-- := by
--   intros
--   sorry

end Cedar.Thm
