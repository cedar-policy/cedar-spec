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
def CompileWellTypedResult (ty : TypedExpr) (εnv : SymEnv) : Prop :=
  ∃ t : Term,
    compile ty.toExpr εnv = .ok t ∧
    t.typeOf = .option (TermType.ofType ty.typeOf)

def CompileWellTyped (ty : TypedExpr) (env : Environment) (εnv : SymEnv) : Prop :=
  εnv = SymEnv.ofEnv env →
  TypedExpr.WellTyped env ty →
  εnv.WellFormedFor ty.toExpr →
  CompileWellTypedResult ty εnv

/--
Special case for literals
-/
theorem compile_well_typed_lit {p : Prim} {ty : CedarType} {env : Environment} {εnv : SymEnv} :
  CompileWellTyped (.lit p ty) env εnv
:= by
  intros henv hwt hwf
  simp [TypedExpr.typeOf, TypedExpr.toExpr, CompileWellTypedResult] at *

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
  CompileWellTyped (.var v ty) env εnv
:= by
  intros henv hwt hwf
  simp [TypedExpr.typeOf, TypedExpr.toExpr, CompileWellTypedResult] at *

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

mutual
  theorem compile_well_typed_ite
    {cond : TypedExpr} {thenExpr : TypedExpr} {elseExpr : TypedExpr} {ty : CedarType}
    {env : Environment} {εnv : SymEnv}:
    CompileWellTyped (.ite cond thenExpr elseExpr ty) env εnv
  := by
    intros henv hwt hwf
    simp [TypedExpr.typeOf, TypedExpr.toExpr] at *
    sorry

  theorem compile_well_typed_and
    {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
    {env : Environment} {εnv : SymEnv} :
    CompileWellTypedResult a εnv →
    CompileWellTypedResult b εnv →
    CompileWellTyped (.and a b ty) env εnv
  := by
    intros ha hb henv hwt hwf
    simp [CompileWellTypedResult] at *

    let ⟨t_a, ⟨hcomp_a, hty_a⟩⟩ := ha
    let ⟨t_b, ⟨hcomp_b, hty_b⟩⟩ := hb

    -- By well-typedness, a and b must be booleans
    cases hwt
    case and _ hbool_a _ hbool_b =>

    simp [compile, compileAnd, TypedExpr.typeOf, TypedExpr.toExpr] at *
    simp [
      hcomp_a, hcomp_b, hty_a, hty_b, hbool_a, hbool_b,
      TermType.ofType, Term.typeOf,
    ]

    split
    · simp [Term.typeOf, TermPrim.typeOf]
    · simp
      rw [typeOf_ifSome_option]
      rw [typeOf_ite]
      rw [typeOf_option_get]
      simp [hty_a, hbool_a, TermType.ofType]
      simp [hty_b, hbool_b, TermType.ofType]
      simp [Factory.someOf, TermType.ofType, Term.typeOf, TermPrim.typeOf]

    · contradiction

  /--
  Compiling a well-typed expression should produce a term of the corresponding TermType.
  -/
  theorem compile_well_typed {env : Environment} {εnv : SymEnv} {ty : TypedExpr} :
    CompileWellTyped ty env εnv
  := by
    cases ty
    case lit => exact compile_well_typed_lit
    case var => exact compile_well_typed_var
    case ite => exact compile_well_typed_ite
    case and =>
      intros henv hwt hwf
      apply compile_well_typed_and
      any_goals assumption

      -- Prove IH
      all_goals
        apply compile_well_typed
        any_goals assumption
        cases hwt
        any_goals assumption
        simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor] at *
        rcases hwf with ⟨hwf, hrefs⟩
        simp [Expr.ValidRefs, TypedExpr.toExpr] at hrefs
        constructor; assumption
        cases hrefs; assumption

    all_goals sorry
  -- termination_by (sizeOf ty)
end

  -- intros henv hwt hwf hcomp

  -- unfold
  --   SymEnv.WellFormedFor
  --   SymEntities.ValidRefsFor
  --   SymEnv.WellFormed
  --   SymRequest.WellFormed at hwf

  -- rcases hwf with ⟨⟨hreqwf, henvwf⟩, hrefs⟩
  -- rcases hreqwf with ⟨
  --   hreqwf₁,
  --   hreqwf₂,
  --   hreqwf₃,
  --   hreqwf₄,
  --   hreqwf₅,
  --   hreqwf₆,
  --   hreqwf₇,
  --   hreqwf₈
  -- ⟩

  -- cases e : ty
  -- all_goals
  --   rw [e] at hcomp hwt hrefs
  --   unfold TypedExpr.toExpr at hrefs
  --   unfold compile TypedExpr.toExpr at hcomp
  --   simp at *
  --   -- unfold Factory.someOf Term.typeOf TermPrim.typeOf TypedExpr.typeOf TermType.ofType at *
  --   -- cases hwt

  -- case lit p =>
  --   unfold compilePrim at hcomp
  --   cases hwt
  --   cases p

  --   case entity =>
  --     cases hrefs
  --     case lit_valid hrefs =>
  --       unfold Prim.ValidRef at hrefs
  --       unfold Factory.someOf at hcomp
  --       simp at *
  --       rw [hrefs] at hcomp
  --       simp at *
  --       rw [←hcomp]
  --       unfold Term.typeOf TermPrim.typeOf at *
  --       simp

  --   -- Other cases can be resolved by rewriting
  --   any_goals
  --     simp at *
  --     rw [←hcomp]
  --     unfold Term.typeOf TermPrim.typeOf BitVec.width at *
  --     simp

  -- case var v =>
  --   cases v
  --   all_goals
  --     unfold compileVar at hcomp
  --     simp at *

  --   case principal =>

  --     sorry

  --   all_goals sorry

  -- all_goals sorry

  -- | lit p =>
  --   sorry
  -- | _ => sorry

  -- let x := ty.toExpr
  -- have h₄ : compile x εnv = .ok t := h₄
  -- match x with
  -- | .lit (.bool b) =>
  --   -- unfold TypedExpr.typeOf
  --   -- unfold compile compilePrim Factory.someOf at h₄
  --   -- simp at h₄
  --   -- unfold Term.typeOf TermPrim.typeOf
  --   -- rw [←h₄]
  --   -- simp
  --   -- unfold Term.typeOf TermPrim.typeOf
  --   -- simp
  --   cases h₂ with
  --   | lit p => sorry
  --   | var v =>
  --     cases v with
  --     | principal => sorry
  --     | _ => sorry
  --   | _ => sorry
  -- | _ => sorry

theorem compile_well_typed_expr_never_fails {ty : TypedExpr} {env : Environment} {εnv : SymEnv} :
  εnv = SymEnv.ofEnv env →
  TypedExpr.WellTyped env ty →
  εnv.WellFormedFor ty.toExpr →
  Except.isOk (compile ty.toExpr εnv)
:= by
  intros
  sorry

end Cedar.Thm
