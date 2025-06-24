import Cedar.Thm.Validation.WellTyped.Definition
import Cedar.Thm.SymCC.Compiler.Invert
import Cedar.Thm.SymCC.Compiler.WF

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/--
States the symbolic compiler succeeds on a typed expression `tx` and
produces a term `t` with the corresponding type.
-/
def CompileWellTypedForExpr (tx : TypedExpr) (εnv : SymEnv) : Prop :=
  ∃ t : Term,
    compile tx.toExpr εnv = .ok t ∧
    t.typeOf = .option (TermType.ofType tx.typeOf)

/--
States that an `Environment` is well-formed.

TODO: this is currently just a placeholder, in case we need more
assumptions about the input `Environment`.
-/
def Environment.WellFormed (_ : Environment) : Prop := true

/--
A sufficient condition for `CompileWellTypedForExpr` to hold.
-/
def CompileWellTypedCondition (tx : TypedExpr) (Γ : Environment) (εnv : SymEnv) : Prop :=
  Environment.WellFormed Γ ∧
  εnv = SymEnv.ofEnv Γ ∧
  TypedExpr.WellTyped Γ tx ∧
  εnv.WellFormedFor tx.toExpr

/--
A wrapper around compile_wf for convenience
-/
theorem wt_cond_implies_compile_wf
  {tx : TypedExpr} {Γ : Environment} {εnv : SymEnv} {t : Term} :
  CompileWellTypedCondition tx Γ εnv →
  compile tx.toExpr εnv = .ok t →
  t.WellFormed εnv.entities
:= by
  intros h hcomp; rcases h with ⟨_, _, _, hwf⟩
  have htwf := compile_wf hwf hcomp
  simp [htwf]

/--
Special case for literals
-/
theorem compile_well_typed_lit {p : Prim} {tx : CedarType} {Γ : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.lit p tx) Γ εnv →
  CompileWellTypedForExpr (.lit p tx) εnv
:= by
  intros h; rcases h with ⟨_, hεnv, hwt, hwf⟩
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
    {qty : QualifiedType} :
    TermType.ofQualifiedType qty =
    TermType.ofQualifiedType qty.liftBoolTypes
  := by
    cases qty
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
  | _ :: tail => by
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
theorem compile_well_typed_var {v : Var} {ty : CedarType} {Γ : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.var v ty) Γ εnv →
  CompileWellTypedForExpr (.var v ty) εnv
:= by
  intros h; rcases h with ⟨_, hεnv, hwt, hwf⟩
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
    simp [hεnv, SymEnv.ofEnv, SymRequest.ofRequestType, TermType.ofType, TermPrim.typeOf, Term.typeOf]
    apply ofRecordType_ignores_liftBool

  all_goals
    simp [
      hprincipal, haction, hresource, hcontext,
    ] at *
    simp [TermType.ofType, Term.typeOf]
    simp [hεnv, SymEnv.ofEnv, SymRequest.ofRequestType, TermType.ofType, TermPrim.typeOf, Term.typeOf]

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
  {Γ : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.ite cond thenExpr elseExpr ty) Γ εnv) :
  CompileWellTypedCondition cond Γ εnv ∧
  CompileWellTypedCondition thenExpr Γ εnv ∧
  CompileWellTypedCondition elseExpr Γ εnv
:= by
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
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
  {Γ : Environment} {εnv : SymEnv}
  (iha : CompileWellTypedForExpr a εnv)
  (ihb : CompileWellTypedForExpr b εnv)
  (ihc : CompileWellTypedForExpr c εnv)
  (hcond_ite : CompileWellTypedCondition (.ite a b c ty) Γ εnv) :
  CompileWellTypedForExpr (.ite a b c ty) εnv
:= by
  have ⟨hcond_a, hcond_b, hcond_c⟩ := eliminate_wt_cond_ite hcond_ite
  have ⟨hwf_env, hεnv, hwt_ite, hwf_ite⟩ := hcond_ite

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
  {Γ : Environment} {εnv : SymEnv}
  {cons : TypedExpr → TypedExpr → CedarType → TypedExpr}
  (h : CompileWellTypedCondition (cons a b ty) Γ εnv)
  (hcons : cons = .or ∨ cons = .and) :
  CompileWellTypedCondition a Γ εnv ∧
  CompileWellTypedCondition b Γ εnv
:= by
  cases hcons
  all_goals
    -- Same proof for both cases
    case _ hcons =>
    simp [hcons] at *
    have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
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
  {Γ : Environment} {εnv : SymEnv}
  (iha : CompileWellTypedForExpr a εnv)
  (ihb : CompileWellTypedForExpr b εnv) :

  (CompileWellTypedCondition (.or a b ty) Γ εnv →
    CompileWellTypedForExpr (.or a b ty) εnv) ∧

  (CompileWellTypedCondition (.and a b ty) Γ εnv →
    CompileWellTypedForExpr (.and a b ty) εnv)
:= by
  constructor
  all_goals
  intros hcond

  -- Some facts needed later
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := hcond
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
  {Γ : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.unaryApp op expr ty) Γ εnv) :
  CompileWellTypedCondition expr Γ εnv
:= by
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
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
  {Γ : Environment} {εnv : SymEnv}
  (ihexpr : CompileWellTypedForExpr expr εnv)
  (hcond_unary : CompileWellTypedCondition (.unaryApp op expr ty) Γ εnv) :
  CompileWellTypedForExpr (.unaryApp op expr ty) εnv
:= by
  have hcond_expr := eliminate_wt_cond_unaryApp hcond_unary
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := hcond_unary
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
  {op : BinaryOp} {a : TypedExpr} {b : TypedExpr} {ty : CedarType} {Γ : Environment} {εnv : SymEnv} :
  CompileWellTypedCondition (.binaryApp op a b ty) Γ εnv →
  CompileWellTypedCondition a Γ εnv ∧
  CompileWellTypedCondition b Γ εnv
:= by
  intros h; rcases h with ⟨hwf_env, hεnv, hwt, hwf⟩
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
If some entity exists in `Γ`, then it must
also exists in `SymEnv.ofEnv Γ` with the corresponding `SymEntityData`
-/
theorem ofEnv_lookup_entity
  {Γ : Environment} {εnv : SymEnv} {ety : EntityType} {entry : EntitySchemaEntry}
  (hεnv : εnv = SymEnv.ofEnv Γ)
  (hfound : Data.Map.find? Γ.ets ety = some entry) :
  Data.Map.find? εnv.entities ety = some (SymEntityData.ofEntityType ety entry)
:= by
  simp [hεnv, Data.Map.find?, SymEnv.ofEnv, SymEntities.ofSchema, Data.Map.toList]
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

  apply Data.Map.find?_implies_make_find?
  apply List.find?_implies_append_find?
  apply List.find?_implies_find?_fst_map
  assumption

/--
Lemma that if a concrete `Γ : Environment` has tags for
a particular entity type, when `SymEnv.ofEnv Γ` must also
have tags for it
-/
theorem SymEnv_of_preserves_tags
  {Γ : Environment} {ety : EntityType} {ty : CedarType}
  (h : Γ.ets.tags? ety = some (some ty)) :
  ∃ τags : SymTags,
    (SymEnv.ofEnv Γ).entities.tags ety = τags ∧
    τags.vals.outType = TermType.ofType ty
:= by
  simp [EntitySchema.tags?] at h
  have ⟨found_entry, ⟨hfound, hty_entry⟩⟩ := h

  -- The corresponding entity exists in `εnv`
  have hety_exists :
    Data.Map.find? (SymEnv.ofEnv Γ).entities ety
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
  {Γ : Environment} {εnv : SymEnv}
  (iha : CompileWellTypedForExpr a εnv)
  (ihb : CompileWellTypedForExpr b εnv)
  (hcond_binary : CompileWellTypedCondition (.binaryApp op a b ty) Γ εnv) :
  CompileWellTypedForExpr (.binaryApp op a b ty) εnv
:= by
  -- Some facts needed later
  have ⟨hcond_a, hcond_b⟩ := eliminate_wt_cond_binaryApp hcond_binary
  have ⟨_, hεnv, hwt_binary, ⟨hwf_εnv, hrefs_binary⟩⟩ := hcond_binary

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
        simp [← hεnv, heq_ety, hτag] at hτag2
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
      hεnv,
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

    simp [SymEntities.tags, ← hεnv, hety_exists]
    split
    any_goals contradiction
    all_goals simp

  case getTag _ _ htag hty_a hty_b =>
    have ⟨_, hτag, _⟩ := SymEnv_of_preserves_tags htag
    simp [← hεnv] at hτag
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
--   Γ.ets.attrs? ety = some a
--   a.liftBoolTypes = rty
-- Show that
--   (SymEnv.ofEnv Γ).entities.attrs ety = .some attrs
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
Show that `SymEnv.ofEnv Γ` preserves the result of attribute lookup
-/
theorem ofEnv_entity_attr_lookup
  {Γ : Environment} {εnv : SymEnv}
  {rty : RecordType} {ety : EntityType}
  (hεnv : εnv = SymEnv.ofEnv Γ)
  (hattrs_exists : Γ.ets.attrs? ety = some rty)
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
    apply ofEnv_lookup_entity hεnv
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
  {Γ : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.getAttr expr attr ty) Γ εnv) :
  CompileWellTypedCondition expr Γ εnv
:= by
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
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
  {Γ : Environment} {εnv : SymEnv}
  (ihexpr : CompileWellTypedForExpr expr εnv)
  (hcond : CompileWellTypedCondition (.getAttr expr attr ty) Γ εnv) :
  CompileWellTypedForExpr (.getAttr expr attr ty) εnv
:= by
  have hcond_expr := eliminate_wt_cond_getAttr hcond
  have ⟨_, hεnv, hwt, hwf_εnv, hrefs⟩ := hcond
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
      have ⟨_, h1, h2, h3, h4⟩ := ofEnv_entity_attr_lookup hεnv hrty2 hwf_εnv

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
  {Γ : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.hasAttr expr attr ty) Γ εnv) :
  CompileWellTypedCondition expr Γ εnv
:= by
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
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
  {Γ : Environment} {εnv : SymEnv}
  (ihexpr : CompileWellTypedForExpr expr εnv)
  (hcond : CompileWellTypedCondition (.hasAttr expr attr ty) Γ εnv) :
  CompileWellTypedForExpr (.hasAttr expr attr ty) εnv
:= by
  have hcond_expr := eliminate_wt_cond_hasAttr hcond
  have ⟨_, _, hwt, hwf_εnv, hrefs⟩ := hcond
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
  {Γ : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.set xs ty) Γ εnv)
  (x : TypedExpr)
  (hx : x ∈ xs) :
  CompileWellTypedCondition x Γ εnv
:= by
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
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
  {Γ : Environment} {εnv : SymEnv}
  (ihxs : ∀ x, x ∈ xs → CompileWellTypedForExpr x εnv)
  (hcond : CompileWellTypedCondition (.set xs ty) Γ εnv) :
  CompileWellTypedForExpr (.set xs ty) εnv
:= by
  have hcond_xs := eliminate_wt_cond_set hcond
  have ⟨_, hεnv, hwt, hwf_εnv, hrefs⟩ := hcond

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
CompileWellTypedCondition decomposes for record
-/
theorem eliminate_wt_cond_record
  {xs : List (Attr × TypedExpr)} {ty : CedarType}
  {Γ : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.record xs ty) Γ εnv)
  (a : Attr) (x : TypedExpr)
  (hx : (a, x) ∈ xs) :
  CompileWellTypedCondition x Γ εnv
:= by
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
  -- constructor; rotate_left
  -- · have e : x = (a, x).snd := by rfl
  --   rw [e]
  --   apply List.sizeOf_snd_lt_sizeOf_list
  --   exact hx
  constructor; any_goals assumption
  constructor
  · cases hwt; any_goals assumption
  · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
    rcases hwf with ⟨_, hrefs⟩
    constructor;
    · cases hwt with
      | record h1 =>
        apply h1; assumption
    · constructor
      · assumption
      · cases hrefs with
        | record_valid h =>
          simp at h
          apply h a x.toExpr a x
          simp [List.attach₂, hx]
          any_goals rfl
          have e : x = (a, x).snd := by rfl
          rw [e]
          apply List.sizeOf_snd_lt_sizeOf_list
          exact hx

/--
Defines when each pair of values in two list of key-value pairs
satisfies a relation `p`, and each pair of keys is equal
-/
inductive MapListValueRelation {α β κ} (p : α → β → Prop) : List (κ × α) → List (κ × β) → Prop
  | nil : MapListValueRelation p [] []
  | cons {k₁ k₂ : κ} {x : α} {y : β} {xs : List (κ × α)} {ys : List (κ × β)} :
    p x y →
    k₁ = k₂ →
    MapListValueRelation p xs ys →
    MapListValueRelation p ((k₁, x) :: xs) ((k₂, y) :: ys)

/--
`List.insertCanonical` preserves `MapListValueRelation`
-/
theorem insertCanonical_preseves_MapListValueRelation
  [LT κ] [DecidableLT κ] [Data.StrictLT κ]
  {p : α → β → Prop}
  {k : κ} {x : α} {y : β}
  {xs : List (κ × α)} {ys : List (κ × β)}
  (hp : p x y)
  (h : MapListValueRelation p xs ys) :
  MapListValueRelation p
    (List.insertCanonical Prod.fst (k, x) xs)
    (List.insertCanonical Prod.fst (k, y) ys)
:= by
  induction h with
  | nil =>
    simp [List.insertCanonical]
    constructor; assumption; simp
    constructor
  | cons px2 pkeq ptail ih =>
    simp [List.insertCanonical, pkeq]
    split
    · constructor; assumption; simp
      constructor; assumption; simp
      assumption
    split
    · constructor; assumption; simp
      exact ih
    constructor; assumption; simp
    assumption

/--
`List.canonicalize` preserves `MapListValueRelation`
-/
theorem canonicalize_preseves_MapListValueRelation
  [LT κ] [DecidableLT κ] [Data.StrictLT κ]
  {p : α → β → Prop}
  {xs : List (κ × α)} {ys : List (κ × β)}
  (h : MapListValueRelation p xs ys) :
  MapListValueRelation p
    (List.canonicalize Prod.fst xs)
    (List.canonicalize Prod.fst ys)
:= by
  -- unfold List.canonicalize

  induction h with
  | nil =>
    simp [List.canonicalize]
    constructor

  | cons hp hkeq hxs ih =>
    case _ k1 k2 x y xs ys =>
    simp [List.canonicalize, ← hkeq]
    unfold List.insertCanonical
    simp
    split
    case _ h =>
      simp [h] at ih
      split
      · constructor
        assumption
        simp
        constructor

      case _ _ _ _ hcons =>
      simp [hcons] at ih
      contradiction

    case _ cxshd cxstl hxs =>
      simp [hxs] at ih
      cases e : (List.canonicalize Prod.fst ys)
      simp [e] at ih
      contradiction

      case _ cyshd cystl =>
      simp [e] at ih
      cases ih with
      | cons phd hkeq2 htail =>
        simp [hxs, hkeq2]
        split
        · repeat
            constructor
            assumption
            simp
          assumption

        split
        case _ =>
          constructor; assumption; simp
          apply insertCanonical_preseves_MapListValueRelation
          assumption
          assumption

        constructor; assumption; simp
        assumption

/--
If `p x y` implies `f x = g y`,
then `MapListValueRelation p xs ys` implies
`List.map (Prod.map id f) xs = List.map (Prod.map id g) ys`
-/
theorem MapListValueRelation.implies_map_eq_if_p_implies_eq
  {p : α → β → Prop}
  {f : α → γ} {g : β → γ}
  {xs : List (κ × α)} {ys : List (κ × β)}
  (hr : MapListValueRelation p xs ys)
  (heq : ∀ x y, p x y → f x = g y) :
  List.map (λ x => (x.fst, f x.snd)) xs
  = List.map (λ x => (x.fst, g x.snd)) ys
:= by
  induction hr with
  | nil => simp [List.map]
  | cons hp hkeq hr2 ih =>
    case _ x y xs ys =>
    simp [List.map]
    simp [hkeq, heq x y hp]
    exact ih

/--
A technical lemma required to simplify record compilation
-/
theorem MapListValueRelation.from_map_mapM
  {f : α → SymCC.Result β}
  {g : α → α'}
  {h : β → β'}
  {p : β' → α' → Prop}
  {xs : List (κ × α)} {ys : List (κ × β)}
  (hmapM : List.mapM (λ (k, x) => do (k, ← f x)) xs = Except.ok ys)
  (hp : ∀ κ x y, (κ, x) ∈ xs → f x = Except.ok y → p (h y) (g x)) :
  MapListValueRelation p
    (List.map (fun x => (x.fst, h x.snd)) ys)
    (List.map (fun x => (x.fst, g x.snd)) xs)
:= by
  induction xs generalizing ys with
  | nil =>
    simp [pure, Except.pure] at hmapM
    simp [hmapM]
    constructor

  | cons xhd xtl ih =>
    cases ys with
    | nil =>
      -- Not possible
      simp at hmapM
      simp_do_let (f xhd.snd) at hmapM
      simp [Functor.map, Except.map] at hmapM
      split at hmapM; contradiction
      simp at hmapM

    | cons yhd ytl =>
      simp
      have hall_ok := List.mapM_ok_implies_all_ok hmapM
      simp at hall_ok

      -- Show that xhd.fst = yhd.fst
      simp at hmapM
      simp_do_let (f xhd.snd) at hmapM
      simp [Functor.map, Except.map] at hmapM
      split at hmapM; contradiction
      simp at hmapM
      have heqk : xhd.fst = yhd.fst := by simp [← hmapM.left]

      constructor

      have hp := hp yhd.fst xhd.snd
      simp [← heqk] at hp
      apply hp

      simp [*]
      simp [← hmapM.left]
      simp [heqk]

      apply ih
      · simp [← hmapM.right]
        assumption

      · intros k x y hx hf_x
        apply hp k x y
        simp [hx]
        assumption

theorem compile_well_typed_record
  {xs : List (Attr × TypedExpr)} {ty : CedarType}
  {Γ : Environment} {εnv : SymEnv}
  (ihxs : ∀ a x, (a, x) ∈ xs → CompileWellTypedForExpr x εnv)
  (hcond : CompileWellTypedCondition (.record xs ty) Γ εnv) :
  CompileWellTypedForExpr (.record xs ty) εnv
:= by
  have hcond_xs := eliminate_wt_cond_record hcond
  have ⟨_, hεnv, hwt, hwf_εnv, hrefs⟩ := hcond

  simp [
    CompileWellTypedForExpr,
    TypedExpr.toExpr,
    compile,
    compileRecord,
    List.mapM₂,
  ]

  -- Compilation of all fields succeeds (the simplified version)
  have ⟨tcomp_xs, hcomp_xs_simp⟩ :
    ∃ ats : List (Attr × Term),
      List.mapM
        (fun x => do
          let __do_lift ← compile x.snd.toExpr εnv
          Except.ok (x.fst, __do_lift))
        xs = Except.ok ats
  := by
    apply List.all_ok_implies_mapM_ok
    intros p hx
    have ⟨k, x⟩ := p
    have ⟨_, hcomp_x, _⟩ := ihxs k x hx
    simp [hcomp_x]

  -- Compilation of all fields succeeds (the exact version)
  have hcomp_xs :
    List.mapM
      (fun x => do
        let __do_lift ← compile x.1.snd εnv
        Except.ok (x.1.fst, __do_lift))
      (List.map (fun x => (x.1.fst, x.1.snd.toExpr)) xs.attach₂).attach₂
    = Except.ok tcomp_xs
  := by
    simp [List.attach₂]

    -- TODO: maybe simplify this a bit
    have e {p : Attr × Expr → Prop} :
      (fun x : { x : Attr × Expr // p x } => do
        let __do_lift ← compile x.val.snd εnv
        Except.ok (x.val.fst, __do_lift))
      =
      (fun x : { x : Attr × Expr // p x } => (
        fun x : Attr × Expr => do
        let __do_lift ← compile x.snd εnv
        Except.ok (x.fst, __do_lift)
      ) x.val)
    := rfl
    rw [e]

    simp [List.mapM_pmap_subtype (
      fun x : Attr × Expr => do
      let __do_lift ← compile x.snd εnv
      Except.ok (x.fst, __do_lift)
    ) ?_ ?_]
    simp [List.map_pmap]
    simp [List.mapM_map]
    simp [hcomp_xs_simp]

  -- Extract some info from well-typedness
  cases hwt with
  | record _ hrty =>
  case _ rty _ =>

  -- `rty` is a well-formed map
  have hwf_rty :
    rty.WellFormed
  := by
    simp [Data.Map.WellFormed, hrty]
    apply Eq.symm
    apply Data.Map.make_of_make_is_id

  -- `tcomp_xs` and `xs` have some association
  have hassoc_comp_xs :
    MapListValueRelation
      (λ t ty =>
        t.typeOf = TermType.ofQualifiedType ty)
      (List.map (fun x => (x.fst, Factory.option.get x.snd)) tcomp_xs)
      (List.map (fun x => (x.fst, Qualified.required x.snd.typeOf)) xs)
  := by
    apply MapListValueRelation.from_map_mapM
      (f := fun x => compile x.toExpr εnv)
      (g := fun x : TypedExpr => Qualified.required x.typeOf)
      hcomp_xs_simp

    intros k x tcomp_x hx hcomp_x
    simp [TermType.ofQualifiedType]
    have ⟨_, hcomp_x2, hty_comp_x⟩ := ihxs k x hx
    simp [hcomp_x] at hcomp_x2
    simp [← hcomp_x2] at hty_comp_x

    have hcond_x := hcond_xs k x hx
    have ⟨_, h⟩ := wf_option_get (wt_cond_implies_compile_wf hcond_x hcomp_x) hty_comp_x
    exact h

  -- Each compiled term (and Option.get of it) is well-formed
  have hwf_comp_xs :
    ∀ (y : Term), y ∈ List.map Prod.snd tcomp_xs →
    Term.WellFormed εnv.entities y ∧
    Term.WellFormed εnv.entities (Factory.option.get y)
  := by
    simp
    intros y k hy
    have ⟨⟨k2, x⟩, hx, hcomp_x⟩ := List.mapM_ok_implies_all_from_ok hcomp_xs_simp (k, y) hy
    simp at hcomp_x
    simp_do_let (compile x.toExpr εnv) at hcomp_x
    case ok hk_to_k2 hcomp_x2 =>
    simp at hcomp_x
    simp [hcomp_x] at hcomp_x2
    simp [hcomp_x] at hx

    have ⟨hwf_comp_x, ⟨ty, hty_comp_x⟩⟩ := compile_wf ((hcond_xs k x hx).2.2.2) hcomp_x2
    simp [hwf_comp_x]
    apply (wf_option_get hwf_comp_x hty_comp_x).left

  -- Prove some typing obligations
  simp [hcomp_xs, Factory.someOf]
  apply (wf_ifAllSome (εs := εnv.entities) ?_ ?_ ?_).right
  · intros g hg
    exact (hwf_comp_xs g hg).left

  · constructor
    apply wf_recordOf
    simp
    intros k y k2 y2 hy hk_to_k2 hopt_y
    simp [← hopt_y]
    simp at hwf_comp_xs
    exact (hwf_comp_xs y2 k2 hy).right

  · simp [
      Term.typeOf,
      Factory.recordOf,
      TypedExpr.typeOf,
      TermType.ofType,
      Data.Map.make,
    ]

    -- Rephrase `TermType.ofRecordType` with `List.map`
    have e (rty : List (Attr × QualifiedType)) :
      TermType.ofRecordType rty
      = rty.map λ (a, qty) => (a, TermType.ofQualifiedType qty)
    := by
      induction rty with
      | nil => simp [TermType.ofRecordType]
      | cons => simp [TermType.ofRecordType]; assumption
    simp [e rty.1]

    simp [hrty, Data.Map.make]

    simp [List.attach₃]
    simp [List.map_pmap]
    have hassoc_canon := canonicalize_preseves_MapListValueRelation hassoc_comp_xs
    apply hassoc_canon.implies_map_eq_if_p_implies_eq
    simp

/--
CompileWellTypedCondition decomposes for call
-/
theorem eliminate_wt_cond_call
  {xfn : ExtFun} {xs : List TypedExpr} {ty : CedarType}
  {Γ : Environment} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.call xfn xs ty) Γ εnv)
  (x : TypedExpr)
  (hx : x ∈ xs) :
  CompileWellTypedCondition x Γ εnv
:= by
  have ⟨hwf_env, hεnv, hwt, hwf⟩ := h
  constructor; any_goals assumption
  constructor
  · cases hwt; any_goals assumption
  · simp [SymEnv.WellFormedFor, SymEntities.ValidRefsFor, TypedExpr.toExpr] at *
    rcases hwf with ⟨_, hrefs⟩
    constructor;
    · cases hwt with
      | call h1 =>
        apply h1; assumption
    · constructor
      · assumption
      · cases hrefs with
        | call_valid h =>
          apply h
          simp [List.map₁]
          apply Exists.intro x
          simp [hx]

theorem compile_well_typed_call
  {xfn : ExtFun} {xs : List TypedExpr} {ty : CedarType}
  {Γ : Environment} {εnv : SymEnv}
  (ihxs : ∀ x, x ∈ xs → CompileWellTypedForExpr x εnv)
  (hcond : CompileWellTypedCondition (.call xfn xs ty) Γ εnv) :
  CompileWellTypedForExpr (.call xfn xs ty) εnv
:= by
  have hcond_xs := eliminate_wt_cond_call hcond
  have ⟨_, hεnv, hwt, hwf_εnv, hrefs⟩ := hcond
  simp [
    CompileWellTypedForExpr,
    TypedExpr.toExpr,
    compile,
    List.map₁,
    List.mapM₁,
  ]

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

  simp [compileCall]

  -- Get some info from well-typedness
  cases hwt with
  | call _ hwt_xfn =>
  cases hwt_xfn

  -- Compiled with compileCall₀
  case
    decimal _ _ hparse _ |
    ip _ _ hparse _ |
    datetime _ _ hparse _ |
    duration _ _ hparse _
  =>
    simp [Functor.map, Option.map] at hcomp_xs
    simp [bind, Except.bind] at hcomp_xs
    split at hcomp_xs
    contradiction

    case _ tcomp_x1 hcomp_x1 =>
    simp [Except.map, pure, Except.pure] at hcomp_xs

    simp [TypedExpr.toExpr, compile, compilePrim, Factory.someOf] at hcomp_x1
    simp [
      ← hcomp_xs, compileCall₀, ← hcomp_x1, ← hparse,
      Factory.someOf,
      Term.typeOf,
      TermPrim.typeOf,
      TermType.ofType,
      TypedExpr.typeOf,
    ]

  -- Compiled with compileCall₁
  case
    isIpv4 x1 hty_x1 _ |
    isIpv6 x1 hty_x1 _ |
    isLoopback x1 hty_x1 _ |
    isMulticast x1 hty_x1 _ |
    toTime x1 hty_x1 _ |
    toMilliseconds x1 hty_x1 _ |
    toSeconds x1 hty_x1 _ |
    toMinutes x1 hty_x1 _ |
    toHours x1 hty_x1 _ |
    toDays x1 hty_x1 _ |
    toDate x1 hty_x1 _
  =>
    have ⟨tcomp_x1, hcomp_x1, hty_comp_x1⟩ := ihxs x1 ?_
    have ⟨hwf_comp_x1, _⟩ := compile_wf ((hcond_xs x1 ?_).2.2.2) hcomp_x1

    have hcomp_xs : tcomp_xs = [tcomp_x1]
    := by
      simp [
        Functor.map, Option.map, Except.map,
        bind, Except.bind,
        pure, Except.pure,
      ] at hcomp_xs
      simp [hcomp_x1] at hcomp_xs
      simp [hcomp_xs]

    simp [
      hcomp_xs,
      ← hcomp_x1,
      hty_comp_x1,
      hty_x1,
      compileCall₁,
      compileCallWithError₁,
      Factory.someOf,
      Term.typeOf,
      TermType.ofType,
    ]
    simp [TypedExpr.typeOf, TermType.ofType]
    apply typeOf_ifSome_option
    try simp [Term.typeOf]

    first
      | apply (wf_ipaddr_isIpv6 (εs := εnv.entities) ?_).right
      | apply (wf_ipaddr_isIpv4 (εs := εnv.entities) ?_).right
      | apply (wf_ipaddr_isLoopback (εs := εnv.entities) ?_).right
      | apply (wf_ipaddr_isMulticast (εs := εnv.entities) ?_).right
      | apply (wf_datetime_toTime (εs := εnv.entities) ?_).right
      | apply (wf_duration_toMilliseconds (εs := εnv.entities) ?_).right
      | apply (wf_duration_toSeconds (εs := εnv.entities) ?_).right
      | apply (wf_duration_toMinutes (εs := εnv.entities) ?_).right
      | apply (wf_duration_toHours (εs := εnv.entities) ?_).right
      | apply (wf_duration_toDays (εs := εnv.entities) ?_).right
      | apply (wf_datetime_toDate (εs := εnv.entities) ?_).right

    apply wf_option_get
    assumption

    simp [hty_comp_x1, hty_x1, TermType.ofType]
    simp; simp

  -- Compiled with compileCall₂
  case
    lessThan x1 x2 hty_x1 hty_x2 _ |
    lessThanOrEqual x1 x2 hty_x1 hty_x2 _ |
    greaterThan x1 x2 hty_x1 hty_x2 _ |
    greaterThanOrEqual x1 x2 hty_x1 hty_x2 _ |
    isInRange x1 x2 hty_x1 hty_x2 _ |
    offset x1 x2 hty_x1 hty_x2 _ |
    durationSince x1 x2 hty_x1 hty_x2 _
  =>
    have ⟨tcomp_x1, hcomp_x1, hty_comp_x1⟩ := ihxs x1 ?_
    have ⟨hwf_comp_x1, _⟩ := compile_wf ((hcond_xs x1 ?_).2.2.2) hcomp_x1
    have ⟨tcomp_x2, hcomp_x2, hty_comp_x2⟩ := ihxs x2 ?_
    have ⟨hwf_comp_x2, _⟩ := compile_wf ((hcond_xs x2 ?_).2.2.2) hcomp_x2
    any_goals simp

    have hcomp_xs : tcomp_xs = [tcomp_x1, tcomp_x2]
    := by
      simp [
        Functor.map, Option.map, Except.map,
        bind, Except.bind,
        pure, Except.pure,
      ] at hcomp_xs
      simp [hcomp_x1, hcomp_x2] at hcomp_xs
      simp [hcomp_xs]

    simp [
      hcomp_xs,
      ← hcomp_x1, ← hcomp_x2,
      hty_comp_x1, hty_comp_x2,
      hty_x1, hty_x2,
      compileCall₂,
      compileCallWithError₂,
      Factory.someOf,
      Term.typeOf,
      TermType.ofType,
    ]
    simp [TypedExpr.typeOf, TermType.ofType]
    apply typeOf_ifSome_option
    apply typeOf_ifSome_option

    try simp [Term.typeOf]
    first
      | apply (wf_decimal_lessThan (εs := εnv.entities) ?_ ?_).right
      | apply (wf_decimal_lessThanOrEqual (εs := εnv.entities) ?_ ?_).right
      | apply (wf_decimal_greaterThan (εs := εnv.entities) ?_ ?_).right
      | apply (wf_decimal_greaterThanOrEqual (εs := εnv.entities) ?_ ?_).right
      | apply (wf_ipaddr_isInRange (εs := εnv.entities) ?_ ?_).right
      | apply (wf_datetime_offset (εs := εnv.entities) ?_ ?_).right
      | apply (wf_datetime_durationSince (εs := εnv.entities) ?_ ?_).right

    all_goals
      apply wf_option_get
      assumption
      simp [hty_comp_x1, hty_comp_x2, hty_x1, hty_x2, TermType.ofType]

/--
Compiling a well-typed expression should produce a term of the corresponding TermType.
-/
theorem compile_well_typed {Γ : Environment} {εnv : SymEnv} {tx : TypedExpr} :
  CompileWellTypedCondition tx Γ εnv →
  CompileWellTypedForExpr tx εnv
:= by
  intros h
  cases tx
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
    have hcond := eliminate_wt_cond_record h
    apply compile_well_typed_record
    · intros a x hx
      apply compile_well_typed (hcond a x hx)
    assumption

  case call =>
    have hcond := eliminate_wt_cond_call h
    apply compile_well_typed_call
    · intros x hx
      apply compile_well_typed (hcond x hx)
    assumption

  decreasing_by
    repeat case _ =>
      simp [*]; omega

    -- Set
    · simp [*]
      have h := List.sizeOf_lt_of_mem hx
      omega

    -- Record
    · simp [*]
      have h := List.sizeOf_snd_lt_sizeOf_list hx
      simp at h
      omega

    -- Call
    · simp [*]
      have h := List.sizeOf_lt_of_mem hx
      omega

end Cedar.Thm
