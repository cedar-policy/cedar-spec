import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

def CompileWellTyped (ty : TypedExpr) (env : Environment) (εnv : SymEnv) (t : Term) : Prop :=
  εnv = SymEnv.ofEnv env →
  TypedExpr.WellTyped env ty →
  εnv.WellFormedFor ty.toExpr →
  compile ty.toExpr εnv = .ok t →
  t.typeOf = .option (TermType.ofType ty.typeOf)

/--
Special case for literals
-/
theorem compile_well_typed_lit {p : Prim} {ty : CedarType} {env : Environment} {εnv : SymEnv} {t : Term} :
  CompileWellTyped (.lit p ty) env εnv t
:= by
  intros henv hwt hwf hcomp
  simp [TypedExpr.typeOf, TypedExpr.toExpr] at *

  unfold SymEnv.WellFormedFor at hwf
  rcases hwf with ⟨_, ⟨hrefs⟩⟩
  rcases hwt with ⟨_, ⟨⟨hwt⟩⟩⟩

  all_goals
    simp [Prim.ValidRef] at hrefs
    simp [compile, compilePrim, Factory.someOf] at hcomp
    try simp [hrefs] at hcomp
    simp [
      ← hcomp,
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

theorem compile_well_typed_var {v : Var} {ty : CedarType} {env : Environment} {εnv : SymEnv} {t : Term} :
  CompileWellTyped (.var v ty) env εnv t
:= by
  intros henv hwt hwf hcomp
  simp [TypedExpr.typeOf, TypedExpr.toExpr] at *

  unfold SymEnv.WellFormedFor SymEnv.WellFormed SymRequest.WellFormed at hwf

  rcases hwf with ⟨⟨⟨_, hprincipal, _, haction, _, hresource, _, hcontext⟩, _⟩, _⟩
  case _ =>

  rcases hwt with _ | hwt
  cases hwt

  all_goals
    simp [compile, compileVar, Factory.someOf] at *
    simp [
      hprincipal, haction, hresource, hcontext,
    ] at *

  case var.context =>
    simp [
      henv,
      SymEnv.ofEnv, SymRequest.ofRequestType,
      TermType.ofType, TermPrim.typeOf,
      Term.typeOf, TermType.isRecordType,
    ] at hcomp
    simp [
      ← hcomp,
      TermType.ofType,
      Term.typeOf, CedarType.liftBoolTypes,
      RecordType.liftBoolTypes,
    ]
    apply ofRecordType_ignores_liftBool

  all_goals
    simp [← hcomp, TermType.ofType, Term.typeOf]
    simp [henv, SymEnv.ofEnv, SymRequest.ofRequestType, TermType.ofType, TermPrim.typeOf, Term.typeOf]

mutual
  theorem compile_well_typed_ite
    {cond : TypedExpr} {thenExpr : TypedExpr} {elseExpr : TypedExpr} {ty : CedarType}
    {env : Environment} {εnv : SymEnv} {t : Term} :
    CompileWellTyped (.ite cond thenExpr elseExpr ty) env εnv t
  := by
    intros henv hwt hwf hcomp
    simp [TypedExpr.typeOf, TypedExpr.toExpr] at *
    sorry

  theorem compile_well_typed_and
    {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
    {env : Environment} {εnv : SymEnv} {t : Term} :
    CompileWellTyped (.and a b ty) env εnv t
  := by
    intros henv hwt hwf hcomp
    simp [TypedExpr.typeOf, TypedExpr.toExpr, compile, compileAnd] at *

    -- By well-typedness, ty must be a boolean type
    cases hwt
    case and _ haty _ hbty =>

    cases e : compile a.toExpr εnv
    all_goals simp [e] at hcomp
    case ok compile_a =>

    split at hcomp
    case h_1 =>
      simp at hcomp
      simp [←hcomp, Term.typeOf, TermPrim.typeOf, TermType.ofType]

    case h_2 ht1ty =>
      cases e : compile b.toExpr εnv
      all_goals simp [e] at hcomp
      case ok compile_b =>
      split at hcomp
      · simp at hcomp
        simp [←hcomp]

        rw [typeOf_ifSome_option]
        rw [typeOf_ite]
        rw [typeOf_option_get]
        rw [ht1ty]
        simp [TermType.ofType]; assumption
        simp [Factory.someOf, TermType.ofType, Term.typeOf, TermPrim.typeOf]

      · contradiction
    · contradiction

  /--
  Compiling a well-typed expression should produce a term of the corresponding TermType.
  -/
  theorem compile_well_typed {env : Environment} {εnv : SymEnv} {t : Term} {ty : TypedExpr} :
    CompileWellTyped ty env εnv t
  -- | .lit _ _ => by exact compile_well_typed_lit
  -- | .var _ _ => by exact compile_well_typed_var
  -- | .ite _ _ _ _ => by exact compile_well_typed_ite
  -- | .and _ _ _ => by exact compile_well_typed_and
  -- | _ => sorry
  -- termination_by (sizeOf ty)
  := by
    cases ty
    case lit => exact compile_well_typed_lit
    case var => exact compile_well_typed_var
    case ite => exact compile_well_typed_ite
    case and => exact compile_well_typed_and

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
