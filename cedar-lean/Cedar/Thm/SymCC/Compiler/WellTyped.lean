import Cedar.Thm.WellTyped.Expr.Definition
import Cedar.Thm.WellTyped.Residual.Definition
import Cedar.Thm.SymCC.Compiler.WF
import Cedar.Thm.SymCC.Env.ofEnv
import Cedar.Thm.SymCC.Env.WF
import Cedar.Thm.SymCC.Term.ofType

/-!
This file contains theorems saying that `compile` succeeds
with the correct term type on well-typed expressions.
-/

namespace Cedar.Thm

open Cedar.Spec
open Cedar.Thm
open Cedar.Validation
open SymCC

/--
States the symbolic compiler succeeds on a typed expression `tx` and
produces a term `t` with the corresponding type.
-/
def CompileWellTyped (tx : TypedExpr) (εnv : SymEnv) : Prop :=
  ∃ t : Term,
    compile tx.toExpr εnv = .ok t ∧
    t.typeOf = .option (TermType.ofType tx.typeOf)

/--
A sufficient condition for `CompileWellTyped` to hold.
-/
def CompileWellTypedCondition (tx : TypedExpr) (Γ : TypeEnv) (εnv : SymEnv) : Prop :=
  εnv = SymEnv.ofEnv Γ ∧
  TypedExpr.WellTyped Γ tx ∧
  εnv.WellFormedFor tx.toExpr

/--
A stronger version of `CompileWellTyped` that
also includes well-formedness of the term
-/
def CompileWellTypedAndWF (tx : TypedExpr) (εnv : SymEnv) : Prop :=
  ∃ t : Term,
    compile tx.toExpr εnv = .ok t ∧
    t.typeOf = .option (TermType.ofType tx.typeOf) ∧
    t.WellFormed εnv.entities

/--
Strengthen `CompileWellTyped` to `CompileWellTypedAndWF`
-/
private theorem CompileWellTyped.add_wf
  {tx : TypedExpr} {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTyped tx εnv)
  (hcond : CompileWellTypedCondition tx Γ εnv) :
  CompileWellTypedAndWF tx εnv
:= by
  have ⟨_, hcomp, hty_comp⟩ := h
  have ⟨_, _, hwf⟩ := hcond
  simp only [CompileWellTyped] at h
  simp [CompileWellTypedAndWF, hcomp, hty_comp, compile_wf hwf hcomp]

/--
A wrapper around compile_wf for convenience
-/
private theorem wt_cond_implies_compile_wf
  {tx : TypedExpr} {Γ : TypeEnv} {εnv : SymEnv} {t : Term}
  (h : CompileWellTypedCondition tx Γ εnv)
  (hcomp : compile tx.toExpr εnv = .ok t) :
  t.WellFormed εnv.entities
:= by
  have ⟨_, _, hwf⟩ := h
  simp [compile_wf hwf hcomp]

/--
If some attribute exists in a record type,
then it should still exist after applying `TermType.ofRecordType`
-/
theorem ofRecordType_preserves_attr
  {rty : RecordType} {attr : Attr} {qty : Qualified CedarType} {ty : CedarType}
  (hattr_exists : Data.Map.find? rty attr = some qty)
  (hattr_ty : qty.getType = ty) :
  ∃ attr_ty : TermType,
    (Data.Map.mk (TermType.ofRecordType rty.1)).find? attr = some attr_ty ∧
    match attr_ty with
    | .option attr_ty' => TermType.ofType ty = attr_ty' ∧ ¬qty.isRequired
    | _ => TermType.ofType ty = attr_ty ∧ qty.isRequired
:= by
  cases rty with | mk rty_1 =>
  induction rty_1
  case nil =>
    simp [Data.Map.find?, List.find?] at hattr_exists
  case cons head tail ih =>
    have ⟨k, v⟩ := head
    simp only [Data.Map.find?, TermType.ofRecordType, List.find?, Bool.not_eq_true]
    simp only [Data.Map.find?, List.find?, Bool.not_eq_true] at hattr_exists ih
    cases e : k == attr
    case false =>
      simp only [e] at ⊢ hattr_exists
      apply ih hattr_exists
    case true =>
      simp only [e, Option.some.injEq] at hattr_exists
      simp only [hattr_exists, Option.some.injEq, exists_eq_left']
      cases qty with
      | optional =>
        simp only [TermType.ofQualifiedType, Qualified.isRequired, and_true]
        simp only [Qualified.getType] at hattr_ty
        simp [hattr_ty]
      | required =>
        simp only [
          TermType.ofQualifiedType, Qualified.isRequired,
          Bool.true_eq_false, and_false, and_true,
        ]
        simp only [Qualified.getType] at hattr_ty
        simp only [hattr_ty]
        -- TermType.ofType never produces an option type
        unfold TermType.ofType
        split
        case h_1 hof_type =>
          split at hof_type
          all_goals contradiction
        simp

/- Lemmas saying that TermType.ofType produces the same result w/ or w/o liftBoolTypes. -/
mutual
  private theorem ofQualifiedType_eq_ofQualifiedType_liftBool
    {qty : QualifiedType} :
    TermType.ofQualifiedType qty =
    TermType.ofQualifiedType qty.liftBoolTypes
  := by
    cases qty
    all_goals
      simp only [
        TermType.ofQualifiedType,
        QualifiedType.liftBoolTypes,
        TermType.option.injEq,
      ]
      apply ofType_eq_ofType_liftBool

  private theorem ofRecordType_eq_ofRecordType_liftBool
    (recs : List (Attr × QualifiedType)) :
    TermType.ofRecordType recs =
    TermType.ofRecordType (CedarType.liftBoolTypesRecord recs)
  := by
    cases recs with
    | nil => simp [TermType.ofRecordType, CedarType.liftBoolTypesRecord]
    | cons _ tail =>
      simp only [
        TermType.ofRecordType,
        CedarType.liftBoolTypesRecord,
        List.cons.injEq,
        Prod.mk.injEq,
        true_and,
      ]
      constructor
      apply ofQualifiedType_eq_ofQualifiedType_liftBool
      apply ofRecordType_eq_ofRecordType_liftBool tail

  private theorem ofType_eq_ofType_liftBool
    (ty : CedarType) :
    TermType.ofType ty = TermType.ofType ty.liftBoolTypes
  := by
    cases ty with
    | bool _ => simp [TermType.ofType, CedarType.liftBoolTypes]
    | int => simp [TermType.ofType, CedarType.liftBoolTypes]
    | string => simp [TermType.ofType, CedarType.liftBoolTypes]
    | entity ety => simp [TermType.ofType, CedarType.liftBoolTypes]
    | ext xty => simp [TermType.ofType, CedarType.liftBoolTypes]
    | set ty =>
      simp [TermType.ofType, CedarType.liftBoolTypes]
      apply ofType_eq_ofType_liftBool ty
    | record rty =>
      simp [TermType.ofType, CedarType.liftBoolTypes, RecordType.liftBoolTypes]
      apply ofRecordType_eq_ofRecordType_liftBool
end

theorem isCedarRecordType_implies_isRecordType
  {ty : TermType}
  (hty : TermType.isCedarRecordType ty) :
  TermType.isRecordType ty
:= by
  have ⟨rty, hrty⟩ := isCedarRecordType_implies_term_record_type hty
  simp [hrty, TermType.isRecordType]

/--
A variant of `wf_ite` to simplify things in this proof
-/
private theorem wf_typeOf_ite {g t₁ t₂ : Term} {ty : TermType} {entities : SymEntities}
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

/--
CompileWellTypedCondition decomposes for ite
-/
private theorem CompileWellTypedCondition.eliminate_ite
  {cond : TypedExpr} {thenExpr : TypedExpr} {elseExpr : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.ite cond thenExpr elseExpr ty) Γ εnv) :
  CompileWellTypedCondition cond Γ εnv ∧
  CompileWellTypedCondition thenExpr Γ εnv ∧
  CompileWellTypedCondition elseExpr Γ εnv
:= by
  have ⟨_, hwt, ⟨_, hrefs⟩⟩ := h
  simp [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt
  cases hrefs
  all_goals repeat
    constructor
    try any_goals assumption

/--
CompileWellTypedCondition decomposes for `or` or `and`
-/
private theorem CompileWellTypedCondition.eliminate_or_and
  {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
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
    have ⟨_, hwt, ⟨_, hrefs⟩⟩ := h
    simp [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
    cases hwt
    cases hrefs
    all_goals repeat
      constructor
      try any_goals assumption

/--
CompileWellTypedCondition decomposes for unaryApp
-/
private theorem CompileWellTypedCondition.eliminate_unaryApp
  {op : UnaryOp} {expr : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.unaryApp op expr ty) Γ εnv) :
  CompileWellTypedCondition expr Γ εnv
:= by
  have ⟨_, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt
  cases hrefs
  all_goals repeat
    constructor
    try any_goals assumption

/--
CompileWellTypedCondition decomposes for binaryApp
-/
private theorem CompileWellTypedCondition.eliminate_binaryApp
  {op : BinaryOp} {a : TypedExpr} {b : TypedExpr} {ty : CedarType} {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.binaryApp op a b ty) Γ εnv) :
  CompileWellTypedCondition a Γ εnv ∧
  CompileWellTypedCondition b Γ εnv
:= by
  have ⟨_, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt
  cases hrefs
  all_goals repeat
    constructor
    try any_goals assumption

/--
CompileWellTypedCondition decomposes for getAttr
-/
private theorem CompileWellTypedCondition.eliminate_getAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.getAttr expr attr ty) Γ εnv) :
  CompileWellTypedCondition expr Γ εnv
:= by
  have ⟨hεnv, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt
  all_goals
    cases hrefs
    all_goals repeat
      constructor
      any_goals assumption

/--
CompileWellTypedCondition decomposes for hasAttr
-/
private theorem CompileWellTypedCondition.eliminate_hasAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.hasAttr expr attr ty) Γ εnv) :
  CompileWellTypedCondition expr Γ εnv
:= by
  have ⟨hεnv, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt
  all_goals
    cases hrefs
    all_goals repeat
      constructor
      any_goals assumption

/--
CompileWellTypedCondition decomposes for set
-/
private theorem CompileWellTypedCondition.eliminate_set
  {xs : List TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.set xs ty) Γ εnv)
  (x : TypedExpr)
  (hx : x ∈ xs) :
  CompileWellTypedCondition x Γ εnv
:= by
  have ⟨hεnv, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt with | set hwt =>
  cases hrefs with | set_valid hrefs =>
  constructor
  · any_goals assumption
  · constructor;
    · apply hwt; assumption
    · constructor
      · assumption
      · apply hrefs
        simp only [List.map₁, List.map_subtype, List.unattach_attach, List.mem_map]
        apply Exists.intro x
        simp [hx]

/--
CompileWellTypedCondition decomposes for record
-/
private theorem CompileWellTypedCondition.eliminate_record
  {xs : List (Attr × TypedExpr)} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.record xs ty) Γ εnv)
  (a : Attr) (x : TypedExpr)
  (hx : (a, x) ∈ xs) :
  CompileWellTypedCondition x Γ εnv
:= by
  have ⟨hεnv, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt with | record hwt =>
  cases hrefs with | record_valid hrefs =>
  constructor
  · exact hεnv
  · apply And.intro (hwt a x hx)
    constructor
    · assumption
    · simp only [List.map₂_eq_map_snd TypedExpr.toExpr, List.mem_map, Prod.exists,
        forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq] at hrefs
      exact hrefs a x.toExpr a x (by simp [hx]) rfl rfl

/--
CompileWellTypedCondition decomposes for call
-/
private theorem CompileWellTypedCondition.eliminate_call
  {xfn : ExtFun} {xs : List TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.call xfn xs ty) Γ εnv)
  (x : TypedExpr)
  (hx : x ∈ xs) :
  CompileWellTypedCondition x Γ εnv
:= by
  have ⟨hεnv, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [SymEntities.ValidRefsFor, TypedExpr.toExpr] at hrefs
  cases hwt with | call hwt =>
  cases hrefs with | call_valid hrefs =>
  constructor
  · any_goals assumption
  · constructor;
    · apply hwt; assumption
    · constructor
      · assumption
      · apply hrefs
        simp only [List.map₁, List.map_subtype, List.unattach_attach, List.mem_map]
        apply Exists.intro x
        simp [hx]

theorem compile_well_typed_lit {p : Prim} {tx : CedarType} {Γ : TypeEnv} {εnv : SymEnv}
  (h : CompileWellTypedCondition (.lit p tx) Γ εnv) :
  CompileWellTyped (.lit p tx) εnv
:= by
  have ⟨hεnv, hwt, ⟨_, hrefs⟩⟩ := h
  simp only [TypedExpr.toExpr] at hrefs
  cases hrefs with | lit_valid hrefs =>
  cases hwt with | lit hwt_prim =>
  simp only [
    compile, compilePrim, Factory.someOf,
    CompileWellTyped, TypedExpr.toExpr,
    TypedExpr.typeOf,
  ]
  cases hwt_prim with
  | bool | int | string =>
    simp [
      TermType.ofType,
      Term.typeOf,
      TermPrim.typeOf,
      BitVec.width,
    ]
  | entityUID =>
    simp only [Prim.ValidRef] at hrefs
    simp [
      hrefs,
      TermType.ofType,
      Term.typeOf,
      TermPrim.typeOf,
    ]

theorem compile_well_typed_var {v : Var} {ty : CedarType} {Γ : TypeEnv} {εnv : SymEnv}
  (hcond : CompileWellTypedCondition (.var v ty) Γ εnv) :
  CompileWellTyped (.var v ty) εnv
:= by
  have ⟨hεnv, hwt, hwf⟩ := hcond
  have ⟨⟨⟨_, hprincipal, _, haction, _, hresource, _, hcontext⟩, _⟩, _⟩ := hwf
  cases hwt with | var hwt =>
  cases hwt
  all_goals simp only [
    hεnv,
    CompileWellTyped,
    TypedExpr.toExpr,
    SymEnv.ofEnv,
    SymRequest.ofRequestType,
    TermType.ofType,
    compile,
    compileVar,
    Term.typeOf,
    Factory.someOf,
    TypedExpr.typeOf,
  ] at ⊢ hprincipal hresource hcontext
  case principal =>
    simp only [hprincipal, ↓reduceIte, Except.ok.injEq, exists_eq_left', Term.typeOf]
  case action =>
    simp only [TermType.isEntityType, TermPrim.typeOf, ↓reduceIte, Except.ok.injEq, exists_eq_left', Term.typeOf]
  case resource =>
    simp only [hresource, ↓reduceIte, Except.ok.injEq, exists_eq_left', Term.typeOf]
  case context =>
    rw [isCedarRecordType_implies_isRecordType]
    simp only [
      ↓reduceIte, Except.ok.injEq,
      CedarType.liftBoolTypes,
      RecordType.liftBoolTypes,
      TermType.ofType, exists_eq_left',
      Term.typeOf, TermType.option.injEq,
      TermType.record.injEq,
      Data.Map.mk.injEq,
    ]
    apply ofRecordType_eq_ofRecordType_liftBool
    apply hcontext

theorem compile_well_typed_ite
  {a : TypedExpr} {b : TypedExpr} {c : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (iha : CompileWellTypedAndWF a εnv)
  (ihb : CompileWellTypedAndWF b εnv)
  (ihc : CompileWellTypedAndWF c εnv)
  (hcond_ite : CompileWellTypedCondition (.ite a b c ty) Γ εnv) :
  CompileWellTyped (.ite a b c ty) εnv
:= by
  have ⟨hεnv, hwt_ite, hwf_ite⟩ := hcond_ite
  have ⟨tcomp_a, hcomp_a, hty_comp_a, hwf_comp_a⟩ := iha
  have ⟨tcomp_b, hcomp_b, hty_comp_b, hwf_comp_b⟩ := ihb
  have ⟨tcomp_c, hcomp_c, hty_comp_c, hwf_comp_c⟩ := ihc
  have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
  have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b
  have ⟨hwf_get_comp_c, hty_get_comp_c⟩ := wf_option_get hwf_comp_c hty_comp_c
  -- Infer types from well-typedness of (.ite a b c ty)
  cases hwt_ite with | ite _ _ _ hbool_a heqty =>
  simp only [
    CompileWellTyped, heqty,
    TypedExpr.toExpr, compile,
    hcomp_a, compileIf, hcomp_b,
    hcomp_c, Except.bind_ok,
    hty_comp_c, hty_comp_b,
    ↓reduceIte, hty_comp_a, hbool_a,
  ]
  -- Case analysis on simplification
  split
  · simp [← heqty, hty_comp_b]
    unfold TypedExpr.typeOf
    simp
  · simp [hty_comp_c]
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
    · simp [hty_comp_c]
      unfold TypedExpr.typeOf
      simp
  · simp; contradiction

/--
Combined case for `or` and `and`
-/
theorem compile_well_typed_or_and
  {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (iha : CompileWellTypedAndWF a εnv)
  (ihb : CompileWellTypedAndWF b εnv) :
  (CompileWellTypedCondition (.or a b ty) Γ εnv →
    CompileWellTyped (.or a b ty) εnv) ∧
  (CompileWellTypedCondition (.and a b ty) Γ εnv →
    CompileWellTyped (.and a b ty) εnv)
:= by
  constructor
  all_goals
    intros hcond
    have ⟨hεnv, hwt, hwf⟩ := hcond
    have ⟨tcomp_a, hcomp_a, hty_comp_a, hwf_comp_a⟩ := iha
    have ⟨tcomp_b, hcomp_b, hty_comp_b, hwf_comp_b⟩ := ihb
    have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
    have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b
    -- By well-typedness, a and b must be booleans
    -- So we substitute that fact and simplify
    cases hwt; case _ _ hbool_a _ hbool_b =>
    simp only [hbool_a, hbool_b] at *; clear hbool_a hbool_b
    simp only [TermType.ofType] at *
    simp only [
      hcomp_a, hcomp_b,
      hty_comp_b, hty_comp_a,
      CompileWellTyped,
      TypedExpr.toExpr,
      compile,
      compileOr, compileAnd,
      Except.bind_ok, ↓reduceIte,
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
      simp [
        TermType.ofType,
        Term.typeOf,
        TermPrim.typeOf,
        Factory.someOf,
        TypedExpr.typeOf,
      ]
    · contradiction

theorem compile_well_typed_unaryApp
  {op : UnaryOp} {expr : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (ihexpr : CompileWellTypedAndWF expr εnv)
  (hcond : CompileWellTypedCondition (.unaryApp op expr ty) Γ εnv) :
  CompileWellTyped (.unaryApp op expr ty) εnv
:= by
  have ⟨hεnv, hwt, hwf⟩ := hcond
  have ⟨compile_expr, hcomp_expr, hty_comp_expr, hwf_comp_expr⟩ := ihexpr
  have ⟨hwf_get_comp_expr, hty_get_comp_expr⟩ := wf_option_get hwf_comp_expr hty_comp_expr
  -- Case analysis on the operator
  cases hwt with | unaryApp _ hopwt =>
  cases hopwt
  -- Some simplification on all goals
  all_goals simp only [
    hcomp_expr, hty_get_comp_expr,
    CompileWellTyped, TypedExpr.toExpr,
    compile, compileApp₁,
    Except.bind_ok,
  ]
  case not hty_expr =>
    simp only [hty_expr, TermType.ofType] at hty_comp_expr
    simp only [hty_expr, TermType.ofType, Factory.someOf, Except.bind_ok, Except.ok.injEq, exists_eq_left']
    rw [typeOf_ifSome_option]
    simp [TypedExpr.typeOf, TermType.ofType, Term.typeOf]
    apply (wf_not (εs := εnv.entities) ?_ ?_).right
    assumption
    simp [hty_get_comp_expr, hty_expr, TermType.ofType]
  case neg hty_expr =>
    simp only [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp only [hty_expr, TermType.ofType, Except.bind_ok, Except.ok.injEq, exists_eq_left']
    rw [typeOf_ifSome_option]
    simp [TypedExpr.typeOf, TermType.ofType, Factory.ifFalse, Factory.noneOf, Factory.someOf]
    have ⟨hwf_bvnego_get_expr, hty_bvnego_get_expr⟩ := wf_bvnego hwf_get_comp_expr hty_get_comp_expr
    have ⟨hwf_bvneg_get_expr, hty_bvneg_get_expr⟩ := wf_bvneg hwf_get_comp_expr hty_get_comp_expr
    apply wf_typeOf_ite
    any_goals assumption
    any_goals simp [Term.typeOf]
    · constructor
      simp [*]
      constructor
    · constructor; assumption
    · simp [*]
    · simp [*]
  case is hty_expr =>
    simp only [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp only [hty_expr, TermType.ofType, Factory.someOf, Except.bind_ok, Except.ok.injEq, exists_eq_left']
    rw [typeOf_ifSome_option]
    simp [
      TypedExpr.typeOf,
      TermType.ofType,
      Term.typeOf,
      TermPrim.typeOf,
    ]
  case isEmpty elem_ty hty_expr =>
    simp only [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp only [hty_expr, TermType.ofType, Factory.someOf, Except.bind_ok, Except.ok.injEq, exists_eq_left']
    rw [typeOf_ifSome_option]
    simp only [
      Factory.set.isEmpty, Term.typeOf,
      TypedExpr.typeOf, TermType.ofType,
      TermType.option.injEq,
    ]
    split
    · simp [Term.typeOf, TermPrim.typeOf]
    · simp [Term.typeOf, TermPrim.typeOf]
    · simp [hty_get_comp_expr]
      apply (wf_eq ?_ ?_ ?_).right
      any_goals assumption
      -- Prove that the empty set term is well-formed
      · constructor
        · intros; contradiction
        · intros; contradiction
        · have h : TermType.WellFormed εnv.entities (.set (TermType.ofType elem_ty))
          := by
            simp only [← hty_get_comp_expr]
            apply typeOf_wf_term_is_wf
            assumption
          cases h; assumption
        · constructor
      · simp only [hty_get_comp_expr, Term.typeOf]
  case like _ hty_expr =>
    simp only [hty_expr, TermType.ofType] at hty_comp_expr hty_get_comp_expr
    simp only [hty_expr, TermType.ofType, Factory.someOf, Except.bind_ok, Except.ok.injEq, exists_eq_left']
    rw [typeOf_ifSome_option]
    simp only [Term.typeOf, TypedExpr.typeOf, TermType.ofType, TermType.option.injEq]
    exact (wf_string_like (εs := εnv.entities)
      hwf_get_comp_expr
      hty_get_comp_expr).right

/--
Similar to `compileApp₂_wf_types`, but for `compile`
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
  simp only [TypedExpr.toExpr, compile, hok_a, hok_b, Except.bind_ok] at hok
  simp_do_let
    (compileApp₂ op
      (Factory.option.get tcomp_a)
      (Factory.option.get tcomp_b)
      εnv.entities)
    at hok
  simp only [Except.ok.injEq] at hok
  case ok tcomp_app hcomp_app =>
    have h := (compileApp₂_wf_types
      hwf_ent
      hwf_get_comp_a
      hwf_get_comp_b
      hcomp_app
    ).right
    -- tcomp_app and t should have the same type
    have heqty : t.typeOf = tcomp_app.typeOf
    := by
      simp only [← hok]
      cases op
      any_goals
        simp only [h]
        apply typeOf_ifSome_option
        apply typeOf_ifSome_option
        assumption
      -- Special case for getTag
      case getTag =>
        have ⟨_, _, _, _, h⟩ := h
        simp only [h]
        apply typeOf_ifSome_option
        apply typeOf_ifSome_option
        assumption
    cases op
    any_goals
      simp only [exists_and_left] at h
      simp [h, heqty]

/--
Since we have the nice lemma `compileApp₂_wf_types`,
it's enough to prove that `compile` of a `binaryApp` succeeds.
-/
theorem compile_ok_implies_compile_well_typed_binaryApp
  {op : BinaryOp} {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (iha : CompileWellTypedAndWF a εnv)
  (ihb : CompileWellTypedAndWF b εnv)
  (hcond : CompileWellTypedCondition (.binaryApp op a b ty) Γ εnv)
  (hok : ∃ t : Term,
    compile (TypedExpr.toExpr (.binaryApp op a b ty)) εnv = .ok t) :
  CompileWellTyped (.binaryApp op a b ty) εnv
:= by
  have ⟨hεnv, hwt_binary, ⟨hwf_εnv, hrefs_binary⟩⟩ := hcond
  have ⟨hwf_req, hwf_ent⟩ := hwf_εnv
  have ⟨tcomp_a, hcomp_a, hty_comp_a, hwf_comp_a⟩ := iha
  have ⟨tcomp_b, hcomp_b, hty_comp_b, hwf_comp_b⟩ := ihb
  have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
  have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b
  have ⟨t, hok⟩ := hok
  have htypes := compile_binaryApp_wf_types
    hwf_ent hcomp_a hcomp_b hwf_get_comp_a hwf_get_comp_b hok
  cases hwt_binary with | binaryApp _ _ hopwt =>
  cases hopwt
  -- Simplify and resolve most goals
  all_goals
    simp only [
      CompileWellTyped, TypedExpr.toExpr, TypedExpr.typeOf, TermType.ofType,
    ]
    simp only [TypedExpr.toExpr] at hok
    simp only [exists_and_left] at htypes
    simp only [hok, Except.ok.injEq, exists_eq_left', htypes]
  -- Special case for `getTag`
  case getTag _ ety tags htag hty_a hty_b _ _ =>
    have ⟨ety2, hty_get_comp_a2, τs, hτag, hτag_ty⟩ := htypes
    rw [← ofType_eq_ofType_liftBool]
    have ⟨τs2, hτag2, hτag_ty2⟩ := ofEnv_preserves_tags htag
    have heq_ety : ety = ety2 := by
      simp [hty_get_comp_a, hty_a, TermType.ofType] at hty_get_comp_a2
      assumption
    have hτs : τs = τs2 := by
      simp [← hεnv, heq_ety, hτag] at hτag2
      assumption
    simp [← hτag_ty2, hτag_ty, hτs]

theorem compile_well_typed_binaryApp
  {op : BinaryOp} {a : TypedExpr} {b : TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (iha : CompileWellTypedAndWF a εnv)
  (ihb : CompileWellTypedAndWF b εnv)
  (hcond : CompileWellTypedCondition (.binaryApp op a b ty) Γ εnv) :
  CompileWellTyped (.binaryApp op a b ty) εnv
:= by
  -- Some facts needed later
  have ⟨hεnv, hwt_binary, ⟨hwf_εnv, hrefs_binary⟩⟩ := hcond
  have ⟨hwf_req, hwf_ent⟩ := hwf_εnv
  have ⟨tcomp_a, hcomp_a, hty_comp_a, hwf_comp_a⟩ := iha
  have ⟨tcomp_b, hcomp_b, hty_comp_b, hwf_comp_b⟩ := ihb
  have ⟨hwf_get_comp_a, hty_get_comp_a⟩ := wf_option_get hwf_comp_a hty_comp_a
  have ⟨hwf_get_comp_b, hty_get_comp_b⟩ := wf_option_get hwf_comp_b hty_comp_b
  -- Reduce to proving that compilation succeeds
  apply compile_ok_implies_compile_well_typed_binaryApp iha ihb hcond
  cases hwt_binary with | binaryApp _ _ hopwt =>
  cases hopwt
  -- Apply some common definitions
  all_goals
    unfold compile TypedExpr.toExpr
    simp only [hcomp_a, hcomp_b, Except.bind_ok]
    simp only [hty_get_comp_a, hty_get_comp_b, compileApp₂, bind_assoc]
  -- Most cases in `BinaryOp.WellTyped`
  -- have the form <case> (a.typeOf = ...) (b.typeOf = ...)
  -- which can be resolved by some simplification
  any_goals try case _ hty_a hty_b =>
    simp [hty_a, hty_b, TermType.ofType]
  case eq_entity hty_a hty_b =>
    simp only [
      hty_a, hty_b,
      reducibleEq, TermType.ofType, TermType.prim.injEq,
      TermPrimType.entity.injEq,
      TermType.isPrimType,
      Bool.and_self, ↓reduceIte,
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
    simp only [
      hprim1, hprim2,
      reducibleEq, TypedExpr.typeOf,
      Bool.and_self, ↓reduceIte,
    ]
    split <;> simp
  case eq _ heqty =>
    simp [heqty, reducibleEq]
  case hasTag ety hty_a hty_b =>
    simp only [hty_a, hty_b, hεnv, TermType.ofType, compileHasTag]
    -- Show that `ety` is a valid entity type
    -- from the fact that `tcomp_a` is well-formed
    -- (so its (entity) type is well-formed)
    simp only [hty_a, TermType.ofType] at hty_comp_a
    have hwf_ty_a := typeOf_wf_term_is_wf hwf_comp_a
    simp only [hty_comp_a] at hwf_ty_a
    cases hwf_ty_a with | option_wf hwf_ty_a =>
    cases hwf_ty_a with | entity_wf hwf_ty_a =>
    simp only [SymEntities.isValidEntityType] at hwf_ty_a
    have ⟨_, hety_exists⟩ :=
      Cedar.Data.Map.contains_iff_some_find?.mp hwf_ty_a
    simp only [SymEntities.tags, ← hεnv, hety_exists, Option.map_some]
    split
    · contradiction
    · simp
    · simp
  case getTag _ _ htag hty_a hty_b =>
    have ⟨_, hτag, _⟩ := ofEnv_preserves_tags htag
    simp only [← hεnv] at hτag
    simp [hty_a, hty_b, hτag, compileGetTag, TermType.ofType]

theorem compile_well_typed_getAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (ihexpr : CompileWellTypedAndWF expr εnv)
  (hcond : CompileWellTypedCondition (.getAttr expr attr ty) Γ εnv) :
  CompileWellTyped (.getAttr expr attr ty) εnv
:= by
  have ⟨hεnv, hwt, hwf_εnv, hrefs⟩ := hcond
  have ⟨compile_expr, hcomp_expr, hty_comp_expr, hwf_comp_expr⟩ := ihexpr
  have ⟨hwf_get_comp_expr, hty_get_comp_expr⟩ := wf_option_get hwf_comp_expr hty_comp_expr
  cases hwt
  case getAttr_entity ety rty hent_attrs_exists hwt_expr hty_expr henv_attr_lookup =>
    simp only [
      hcomp_expr, hty_get_comp_expr, hty_expr,
      CompileWellTyped, TypedExpr.toExpr, compile, compileGetAttr,
      compileAttrsOf, bind_assoc, Except.bind_ok, TermType.ofType,
    ]
    simp only [Option.map_eq_some_iff] at hent_attrs_exists henv_attr_lookup
    have ⟨rty2, hrty2, hrty_rty2⟩ := hent_attrs_exists
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
        -- The exact attribute exists and has the correct type
        rty.find? attr = some attr_ty ∧
        match attr_ty with
        | .option attr_ty' => TermType.ofType ty = attr_ty'
        | _ => TermType.ofType ty = attr_ty
    := by
      have ⟨_, h1, h2, h3, h4⟩ := ofEnv_preserves_entity_attr hεnv hrty2 hwf_εnv
      simp only [hty_expr, TermType.ofType] at hty_get_comp_expr
      simp only [
        h1, h2, h3, hty_get_comp_expr,
        Option.some.injEq, exists_and_left,
        exists_eq_left', true_and,
      ]
      exists (Data.Map.mk (TermType.ofRecordType rty2.1))
      constructor
      -- Types of symbolic attrs are correct
      · simp only [← h4]
        apply (wf_app (εs := εnv.entities) hwf_get_comp_expr ?_ ?_).right
        simp only [hty_get_comp_expr, h3]
        apply h2
      -- Finally, show that TermType is agnostic to `rty2` and `rty2.liftBoolTypes`
      · have ⟨_, h1, h2⟩ := ofRecordType_preserves_attr henv_attr_lookup hty_env_attr
        have hlift := ofRecordType_eq_ofRecordType_liftBool rty2.1
        simp only [RecordType.liftBoolTypes] at hrty_rty2
        simp only at hlift
        simp only [← hrty_rty2, ← hlift] at h1
        simp only [h1, Option.some.injEq, exists_eq_left']
        split at h2 <;> simp [h2]
    simp only [hattrs_exists, Except.bind_ok, hattr_isrec, hattr_exists]
    split
    -- When the field is optional
    case h_1 _ _ h =>
      simp only [Option.some.injEq] at h
      simp only [h] at hattr_ty_eq
      simp only [Except.bind_ok, Except.ok.injEq, TypedExpr.typeOf, exists_eq_left']
      apply typeOf_ifSome_option
      rw [(wf_record_get (εs := εnv.entities) ?_ hattr_isrec hattr_exists).right]
      · simp only [hattr_ty_eq]; assumption
      · apply (wf_app hwf_get_comp_expr hattr_input hwf_attrs).left
    -- When the field is not optional
    case h_2 _ _ h =>
      simp only [Option.some.injEq] at h
      simp only [h] at hattr_ty_eq
      simp only [Factory.someOf, Except.bind_ok, Except.ok.injEq, TypedExpr.typeOf, exists_eq_left']
      apply typeOf_ifSome_option
      simp only [Term.typeOf, TermType.option.injEq]
      rw [(wf_record_get (εs := εnv.entities) ?_ hattr_isrec hattr_exists).right]
      · simp only [hattr_ty_eq]; assumption
      · apply (wf_app hwf_get_comp_expr hattr_input hwf_attrs).left
    case _ => contradiction
  case getAttr_record rty _ hty_expr henv_attr_lookup =>
    simp only [hty_expr, TermType.ofType] at hty_get_comp_expr
    simp only [
      hty_get_comp_expr, hcomp_expr,
      CompileWellTyped, TypedExpr.toExpr, compile, compileGetAttr,
      compileAttrsOf, bind_assoc, Except.bind_ok,
    ]
    -- Some some facts about record attr lookup
    -- from hypotheses in `getAttr_record` and `ofRecordType_preserves_attr`
    have ⟨attr_ty, hattr_exists, hattr_ty_eq⟩ :
      ∃ attr_ty : TermType,
        (Data.Map.mk (TermType.ofRecordType rty.1)).find? attr = some attr_ty ∧
        -- Result type matches attr_ty
        match attr_ty with
        | .option attr_ty' => TermType.ofType ty = attr_ty'
        | _ => TermType.ofType ty = attr_ty
    := by
      simp only [Option.map_eq_some_iff] at henv_attr_lookup
      have ⟨field_ty, field_exists, hfield_ty⟩ := henv_attr_lookup
      have ⟨attr_ty, h1, h2⟩ := ofRecordType_preserves_attr field_exists hfield_ty
      simp only [h1, Option.some.injEq, exists_eq_left']
      split
      · simp only [Bool.not_eq_true] at h2; simp [h2]
      · simp only at h2; simp [h2]
    simp only [hattr_exists]
    split
    -- Optional field
    case h_1 _ h =>
      simp only [Except.bind_ok, Except.ok.injEq, TypedExpr.typeOf, exists_eq_left']
      apply typeOf_ifSome_option
      rw [(wf_record_get (εs := εnv.entities)
        hwf_get_comp_expr
        hty_get_comp_expr hattr_exists).right]
      simp only [Option.some.injEq] at h
      simp only [h] at hattr_ty_eq
      simp [h, hattr_ty_eq]
    -- Required field
    case h_2 _ h =>
      simp [TypedExpr.typeOf, Factory.someOf]
      apply typeOf_ifSome_option
      simp [Term.typeOf]
      rw [(wf_record_get (εs := εnv.entities)
        hwf_get_comp_expr
        hty_get_comp_expr hattr_exists).right]
      simp only [Option.some.injEq] at h
      simp only [h] at hattr_ty_eq
      simp [h, hattr_ty_eq]
    case _ => contradiction

theorem compile_well_typed_hasAttr
  {expr : TypedExpr} {attr : Attr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (ihexpr : CompileWellTypedAndWF expr εnv)
  (hcond : CompileWellTypedCondition (.hasAttr expr attr ty) Γ εnv) :
  CompileWellTyped (.hasAttr expr attr ty) εnv
:= by
  have ⟨_, hwt, hwf_εnv, hrefs⟩ := hcond
  have ⟨compile_expr, hcomp_expr, hty_comp_expr, hwf_comp_expr⟩ := ihexpr
  have hwf_ty_expr := typeOf_wf_term_is_wf hwf_comp_expr
  have ⟨hwf_get_comp_expr, hty_get_comp_expr⟩ := wf_option_get hwf_comp_expr hty_comp_expr
  cases hwt
  case hasAttr_entity ety hwt_expr hty_expr =>
    -- Show that `ety` is a valid entity type
    -- from the fact that `tcomp_a` is well-formed
    -- (so its (entity) type is well-formed)
    simp only [hty_expr, TermType.ofType] at hty_comp_expr
    -- Simplify `hwf_ty_expr`
    simp only [hty_comp_expr] at hwf_ty_expr
    cases hwf_ty_expr; case option_wf hwf_ty_expr =>
    cases hwf_ty_expr; case entity_wf hwf_ty_expr =>
    simp only [SymEntities.isValidEntityType] at hwf_ty_expr
    have ⟨sym_ety_data, hety_exists⟩ :=
      Cedar.Data.Map.contains_iff_some_find?.mp hwf_ty_expr
    simp only [
      hty_get_comp_expr, hty_expr,
      hcomp_expr, hety_exists,
      CompileWellTyped, TypedExpr.toExpr, compile, compileHasAttr,
      compileAttrsOf, SymEntities.attrs,
      Option.bind_eq_bind, bind_assoc, Except.bind_ok,
      TermType.ofType, Option.bind_some,
    ]
    have hattrs_exists :
      εnv.entities.attrs ety = .some sym_ety_data.attrs
    := by simp [SymEntities.attrs, hety_exists]
    have ⟨hwf_attrs, hty_attrs_arg, hty_attrs_out⟩ := wf_εnv_implies_attrs_wf hwf_εnv hattrs_exists
    have ⟨rty, hty_attrs_out⟩ :
      ∃ rty : Data.Map Attr TermType,
        sym_ety_data.attrs.outType = .record rty
    := by
      have hty_attrs_out := isCedarRecordType_implies_isRecordType hty_attrs_out
      simp only [TermType.isRecordType] at hty_attrs_out
      cases e : sym_ety_data.attrs.outType with
      | record => simp
      | _ => simp [e] at hty_attrs_out
    have hty_app_attrs :
      (Factory.app sym_ety_data.attrs (Factory.option.get compile_expr)).typeOf
      = .record rty
    := by
      simp only [← hty_attrs_out]
      apply (wf_app (εs := εnv.entities) hwf_get_comp_expr ?_ ?_).right
      simp only [hty_expr] at hty_get_comp_expr
      simp only [hty_get_comp_expr]
      simp only [TermType.ofType, hty_attrs_arg]
      exact hwf_attrs
    simp only [hty_app_attrs]
    split
    -- Optional field
    case _ hattr_exists =>
      simp only [Except.bind_ok, Except.ok.injEq, exists_eq_left']
      apply typeOf_ifSome_option
      simp only [
        Factory.someOf, Factory.isSome,
        Term.typeOf, TypedExpr.typeOf, TermType.ofType,
        TermType.option.injEq,
      ]
      apply (wf_not (εs := εnv.entities) ?_ ?_).right
      apply (wf_isNone (εs := εnv.entities) ?_).left
      rotate_left
      apply (wf_isNone (εs := εnv.entities) ?_).right
      all_goals
        apply (wf_record_get ?_ hty_app_attrs hattr_exists).left
        apply (wf_app ?_ ?_ ?_).left
        exact hwf_get_comp_expr
        simp only [hty_get_comp_expr, hty_expr, TermType.ofType, hty_attrs_arg]
        exact hwf_attrs
    -- Required field
    case _ =>
      simp only [Except.bind_ok, Except.ok.injEq, exists_eq_left']
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        TermPrim.typeOf,
      ]
    -- Attribute does not exist
    case _ =>
      simp only [Except.bind_ok, Except.ok.injEq, exists_eq_left']
      apply typeOf_ifSome_option
      simp [
        Factory.someOf, TermType.ofType, TypedExpr.typeOf, Term.typeOf,
        TermPrim.typeOf,
      ]
  case hasAttr_record rty hwt_expr hty_expr =>
    simp only [
      hty_get_comp_expr, hty_expr, hcomp_expr,
      CompileWellTyped, TypedExpr.toExpr, compile, compileHasAttr,
      compileAttrsOf, SymEntities.attrs, Option.bind_eq_bind, bind_assoc,
      Except.bind_ok, TermType.ofType,
    ]
    simp only [hty_expr, TermType.ofType] at hty_get_comp_expr
    split <;> simp only [Except.bind_ok, Except.ok.injEq, exists_eq_left']
    -- Optional attribute
    case _ hattr_exists =>
      apply typeOf_ifSome_option
      simp only [
        Factory.someOf, Factory.isSome, Term.typeOf,
        TypedExpr.typeOf, TermType.ofType,
        TermType.option.injEq,
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
      simp only [Factory.someOf, Term.typeOf, TermPrim.typeOf, TypedExpr.typeOf, TermType.ofType]
    -- Attribute does not exist
    case _ =>
      apply typeOf_ifSome_option
      simp only [Factory.someOf, Term.typeOf, TermPrim.typeOf, TypedExpr.typeOf, TermType.ofType]

theorem compile_well_typed_set
  {xs : List TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (ihxs : ∀ x, x ∈ xs → CompileWellTypedAndWF x εnv)
  (hcond : CompileWellTypedCondition (.set xs ty) Γ εnv) :
  CompileWellTyped (.set xs ty) εnv
:= by
  have ⟨hεnv, hwt, hwf_εnv, hrefs⟩ := hcond
  simp only [
    CompileWellTyped, TypedExpr.toExpr,
    List.map₁, List.map_subtype, List.unattach_attach,
    compile, List.mapM₁, compileSet,
    List.all_eq_true, decide_eq_true_eq,
  ]
  -- Prove that mapM over `compile` succeeds
  have ⟨tcomp_xs, hcomp_xs⟩ :
    ∃ tcomp_xs,
    List.mapM (fun x => compile x.val εnv) (List.map TypedExpr.toExpr xs).attach
    = Except.ok tcomp_xs
  := by
    apply List.all_ok_implies_mapM_ok
    simp only [
      List.mem_attach, forall_const, Subtype.forall,
      List.mem_map, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂,
    ]
    intros x hx
    have ⟨_, h, _⟩ := ihxs x hx
    simp [h]
  simp only [hcomp_xs, Except.bind_ok]
  -- Get some info from well-typedness
  cases hwt with | set hwt_xs hty_sx hnon_empty =>
  case _ ty =>
  simp only [bne_iff_ne, ne_eq] at hnon_empty
  have htcomp_xs_non_empty :
    tcomp_xs ≠ []
  := by
    intros hcontra
    simp only [hcontra] at hcomp_xs
    have hxs_empty := List.mapM_implies_nil hcomp_xs
    simp only [List.attach_eq_nil_iff, List.map_eq_nil_iff] at hxs_empty
    exact hnon_empty hxs_empty
  -- Prove that each compiled result has the correct type
  have hty_comp_xs :
    ∀ y ∈ tcomp_xs,
      y.typeOf = (TermType.ofType ty).option ∧
      Term.WellFormed εnv.entities y
  := by
    intros y hy
    have ⟨⟨x', hx⟩, _, hcomp_x⟩ := List.mapM_ok_implies_all_from_ok hcomp_xs y hy
    simp only [List.mem_map] at hx
    have ⟨x, hx, hx_to_x'⟩ := hx
    have ⟨_, hcomp_x2, hty_comp_x⟩ := ihxs x hx
    simp only at hcomp_x
    simp only [← hx_to_x', hcomp_x2, Except.ok.injEq] at hcomp_x
    simp only [← hcomp_x, hty_comp_x, TermType.option.injEq, and_true]
    simp [hty_sx x hx]
  -- Prove that Option.get of each compiled result has the correct type
  have hty_get_comp_xs :
    ∀ y ∈ List.map Factory.option.get tcomp_xs,
      y.typeOf = TermType.ofType ty ∧
      Term.WellFormed εnv.entities y
  := by
    intros y hy
    simp only [List.mem_map] at hy
    have ⟨y', hy', hy_to_y'⟩ := hy
    have ⟨hty_y', hwf_y'⟩ := hty_comp_xs y' hy'
    simp only [← hy_to_y']
    constructor
    · exact (wf_option_get hwf_y' hty_y').right
    · exact (wf_option_get hwf_y' hty_y').left
  cases tcomp_xs with
  | nil => contradiction
  | cons tcomp_xs_hd tcomp_xs_tl =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons]
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
      simp only [hopt, TermType.option.injEq] at h2
      simp only [hopt, h2, true_and]
      split
      any_goals contradiction
      simp only [Except.ok.injEq, exists_eq_left']
      -- Finally, resolve some typing constraints
      apply (wf_ifAllSome (εs := εnv.entities) ?_ ?_ ?_).right
      intros g hg
      apply (hty_comp_xs g hg).right
      · constructor
        apply (wf_setOf ?_ ?_ ?_).left
        . intros t ht; apply (hty_get_comp_xs t ht).right
        · intros t ht; apply (hty_get_comp_xs t ht).left
        · have h := hty_get_comp_xs (Factory.option.get tcomp_xs_hd)
          simp only [List.map_cons, List.mem_cons, List.mem_map, true_or, forall_const] at h
          simp only [← h.left]
          apply typeOf_wf_term_is_wf
          apply h.right
      · simp only [
          Factory.someOf, Term.typeOf,
          TypedExpr.typeOf, TermType.ofType,
          TermType.option.injEq,
        ]
        apply (wf_setOf (εs := εnv.entities) ?_ ?_ ?_).right
        . intros t ht; apply (hty_get_comp_xs t ht).right
        . intros t ht; apply (hty_get_comp_xs t ht).left
        · have h := hty_get_comp_xs (Factory.option.get tcomp_xs_hd)
          simp only [List.map_cons, List.mem_cons, List.mem_map, true_or, forall_const] at h
          simp only [← h.left]
          apply typeOf_wf_term_is_wf
          apply h.right
    case _ hnot_opt =>
      have hty_comp_xs_hd := hty_comp_xs tcomp_xs_hd
      simp only [List.mem_cons, true_or, forall_const] at hty_comp_xs_hd
      simp [hty_comp_xs_hd] at hnot_opt

theorem compile_well_typed_record
  {xs : List (Attr × TypedExpr)} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (ihxs : ∀ a x, (a, x) ∈ xs → CompileWellTypedAndWF x εnv)
  (hcond : CompileWellTypedCondition (.record xs ty) Γ εnv) :
  CompileWellTyped (.record xs ty) εnv
:= by
  have ⟨hεnv, hwt, hwf_εnv, hrefs⟩ := hcond
  simp only [CompileWellTyped, TypedExpr.toExpr, compile, compileRecord]
  simp only [do_eq_ok, Except.ok.injEq]
  -- Strip mapM₂
  change ∃ (t : Term), (∃ (ats : List (Attr × Term)),
    ((xs.map₂ _).mapM₂ (λ x => compile x.val.snd εnv |>.bind λ t => Except.ok (x.val.fst, t))) = Except.ok ats ∧ _) ∧ t.typeOf = _
  rw [List.mapM₂_eq_mapM λ x => compile x.snd εnv |>.bind λ t => Except.ok (x.fst, t)]
  -- Strip map₂
  simp only [List.map₂_eq_map_snd, List.mapM_map, Function.comp_def]
  -- Compilation of all fields succeeds
  have ⟨tcomp_xs, hcomp_xs⟩ :
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
  -- Extract some info from well-typedness
  cases hwt with | record _ hrty =>
  case _ rty _ =>
  -- `rty` is a well-formed map
  have hwf_rty : rty.WellFormed
  := by
    simp only [Data.Map.WellFormed, hrty]
    apply Eq.symm
    apply Data.Map.make_of_make_is_id
  -- `tcomp_xs` and `xs` have some association (simplified version)
  have hassoc_comp_xs_simp :
    List.Forallᵥ
      (λ tx t =>
        TermType.ofQualifiedType (Qualified.required tx.typeOf) =
        (Factory.option.get t).typeOf)
      xs tcomp_xs
  := by
    apply List.mapM_implies_forall₂
    rotate_left
    apply hcomp_xs
    intros kv_x kv_y hkv_x hcomp_x
    have ⟨tcomp_x, hcomp_x2, hty_comp_x⟩ := ihxs kv_x.1 kv_x.2 hkv_x
    simp only [TermType.ofQualifiedType]
    simp only [hcomp_x2, Except.bind_ok, Except.ok.injEq] at hcomp_x
    have hkeq : kv_x.fst = kv_y.fst := by simp [← hcomp_x]
    have heq2 : kv_y.snd = tcomp_x := by simp [← hcomp_x]
    simp only [hkeq, heq2, true_and]
    apply Eq.symm
    exact (wf_option_get hty_comp_x.2 hty_comp_x.1).right
  -- `tcomp_xs` and `xs` have some association
  have hassoc_comp_xs :
    List.Forallᵥ
      (λ t ty =>
        t.typeOf = TermType.ofQualifiedType ty)
      (List.map (fun x => (x.fst, Factory.option.get x.snd)) tcomp_xs)
      (List.map (fun x => (x.fst, Qualified.required x.snd.typeOf)) xs)
  := by
    apply List.forall₂_swap
    apply List.map_preserves_forall₂
    rotate_left
    simp only [List.Forallᵥ] at hassoc_comp_xs_simp
    apply hassoc_comp_xs_simp
    simp only [and_imp, Prod.forall]
    intros k1 x k2 y hkeq h
    simp [hkeq, h]
  -- Each compiled term (and Option.get of it) is well-formed
  have hwf_comp_xs :
    ∀ (y : Term), y ∈ List.map Prod.snd tcomp_xs →
    Term.WellFormed εnv.entities y ∧
    Term.WellFormed εnv.entities (Factory.option.get y)
  := by
    simp only [List.mem_map, Prod.exists, exists_eq_right, forall_exists_index]
    intros y k hy
    have ⟨⟨k2, x⟩, hx, hy⟩ := List.mapM_ok_implies_all_from_ok hcomp_xs (k, y) hy
    have ⟨tcomp_x, hcomp_x, hty_comp_x, hwf_comp_x⟩ := ihxs k2 x hx
    simp only [hcomp_x, Except.bind_ok, Except.ok.injEq, Prod.mk.injEq] at hy
    simp only [hy.2] at hwf_comp_x hty_comp_x
    simp only [hwf_comp_x, true_and]
    apply (wf_option_get hwf_comp_x hty_comp_x).left
  -- Prove some typing obligations
  change xs.mapM (λ x => compile x.snd.toExpr εnv |>.bind λ t => Except.ok (x.fst, t)) = .ok tcomp_xs at hcomp_xs
  simp only [hcomp_xs, Factory.someOf, Except.ok.injEq, exists_eq_left']
  apply (wf_ifAllSome (εs := εnv.entities) ?_ ?_ ?_).right
  · intros g hg
    exact (hwf_comp_xs g hg).left
  · constructor
    apply wf_recordOf
    simp only [
      List.mem_map, Prod.exists, Prod.map_apply,
      id_eq, Prod.mk.injEq, forall_exists_index,
      and_imp,
    ]
    intros k y k2 y2 hy hk_to_k2 hopt_y
    simp only [← hopt_y]
    simp only [List.mem_map, Prod.exists, exists_eq_right, forall_exists_index] at hwf_comp_xs
    exact (hwf_comp_xs y2 k2 hy).right
  · simp only [
      Factory.recordOf, Data.Map.make, Term.typeOf,
      TypedExpr.typeOf, TermType.ofType,
      TermType.option.injEq, TermType.record.injEq,
      Data.Map.mk.injEq,
    ]
    simp only [ofRecordType_as_map rty.1]
    simp only [hrty, Data.Map.make]
    simp only [List.map₃_eq_map_snd Term.typeOf]
    apply List.forall₂_iff_map_eq.mp
    apply List.Forall₂.imp
    rotate_left
    · apply List.canonicalize_preserves_forallᵥ
      apply hassoc_comp_xs
    · simp

theorem compile_well_typed_call
  {xfn : ExtFun} {xs : List TypedExpr} {ty : CedarType}
  {Γ : TypeEnv} {εnv : SymEnv}
  (ihxs : ∀ x, x ∈ xs → CompileWellTypedAndWF x εnv)
  (hcond : CompileWellTypedCondition (.call xfn xs ty) Γ εnv) :
  CompileWellTyped (.call xfn xs ty) εnv
:= by
  have hcond_xs := hcond.eliminate_call
  have ⟨hεnv, hwt, hwf_εnv, hrefs⟩ := hcond
  simp only [
    CompileWellTyped, TypedExpr.toExpr,
    List.map₁, List.map_subtype, List.unattach_attach,
    compile, List.mapM₁,
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
  simp only [hcomp_xs, Except.bind_ok]
  simp only [compileCall]
  -- Get some info from well-typedness
  cases hwt with | call _ hwt_xfn =>
  cases hwt_xfn
  -- Resolve cases compiled with compileCall₀
  case
    decimal _ _ hparse _ |
    ip _ _ hparse _ |
    datetime _ _ hparse _ |
    duration _ _ hparse _
  =>
    simp only [
      List.map_cons, List.map_nil, List.attach_cons,
      List.attach_nil, List.mapM_cons,
      List.mapM_nil,
      bind, Except.bind,
    ] at hcomp_xs
    split at hcomp_xs
    case _ => contradiction
    case _ tcomp_x1 hcomp_x1 =>
      simp only [pure, Except.pure, Except.ok.injEq] at hcomp_xs
      simp only [
        TypedExpr.toExpr, compile,
        compilePrim, Factory.someOf,
        Except.ok.injEq,
      ] at hcomp_x1
      simp [
        ← hcomp_xs, ← hcomp_x1, ← hparse,
        compileCall₀,
        Factory.someOf,
        Term.typeOf,
        TermPrim.typeOf,
        TermType.ofType,
        TypedExpr.typeOf,
      ]
  -- Resolve cases compiled with compileCall₁
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
    have ⟨hwf_comp_x1, _⟩ := compile_wf ((hcond_xs x1 ?_).2.2) hcomp_x1
    have hcomp_xs : tcomp_xs = [tcomp_x1] := by
      simp only [
        List.map_cons, List.map_nil, List.attach_cons,
        List.attach_nil, List.mapM_cons,
        bind, Except.bind, List.mapM_nil,
        pure, Except.pure,
      ] at hcomp_xs
      simp only [hcomp_x1, Except.ok.injEq] at hcomp_xs
      simp [hcomp_xs]
    simp only [
      hcomp_xs, hty_comp_x1, hty_x1,
      compileCall₁, compileCallWithError₁, TermType.ofType,
      ↓reduceIte, Factory.someOf, Except.ok.injEq, exists_eq_left',
    ]
    simp only [TypedExpr.typeOf, TermType.ofType]
    apply typeOf_ifSome_option
    -- A special case for compileCallWithError₁
    try simp only [Term.typeOf, TermType.option.injEq]
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
    · assumption
    · simp [hty_comp_x1, hty_x1, TermType.ofType]
    · simp
    · simp
  -- Resolve cases compiled with compileCall₂
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
    have ⟨hwf_comp_x1, _⟩ := compile_wf ((hcond_xs x1 ?_).2.2) hcomp_x1
    have ⟨tcomp_x2, hcomp_x2, hty_comp_x2⟩ := ihxs x2 ?_
    have ⟨hwf_comp_x2, _⟩ := compile_wf ((hcond_xs x2 ?_).2.2) hcomp_x2
    any_goals simp only [List.mem_cons, List.not_mem_nil, or_false, or_true, true_or]
    have hcomp_xs : tcomp_xs = [tcomp_x1, tcomp_x2]
    := by
      simp only [
        List.map_cons, List.map_nil, List.attach_cons,
        List.attach_nil, List.mapM_cons,
        bind, Except.bind, List.mapM_nil,
        pure, Except.pure,
      ] at hcomp_xs
      simp only [hcomp_x1, hcomp_x2, Except.ok.injEq] at hcomp_xs
      simp [hcomp_xs]
    simp only [
      hcomp_xs,
      hty_comp_x1, hty_x1,
      hty_comp_x2, hty_x2,
      compileCall₂, compileCallWithError₂,
      TermType.ofType, decide_true,
      Bool.and_self, ↓reduceIte,
      Factory.someOf, Except.ok.injEq,
      exists_eq_left',
    ]
    simp only [TypedExpr.typeOf, TermType.ofType]
    apply typeOf_ifSome_option
    apply typeOf_ifSome_option
    try simp only [Term.typeOf, TermType.option.injEq]
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
Compiling a well-typed expression should produce a term of the corresponding `TermType`,
assuming that the expression is well-formed in the symbolic environment.
-/
theorem compile_well_typed_on_wf_expr {Γ : TypeEnv} {εnv : SymEnv} {tx : TypedExpr} :
  CompileWellTypedCondition tx Γ εnv →
  CompileWellTyped tx εnv
:= by
  intros h
  cases tx
  case lit => exact compile_well_typed_lit h
  case var => exact compile_well_typed_var h
  case ite =>
    have ⟨h1, h2, h3⟩ := h.eliminate_ite
    apply compile_well_typed_ite
    any_goals apply CompileWellTyped.add_wf
    any_goals apply compile_well_typed_on_wf_expr
    any_goals assumption
  case and =>
    have ⟨ha, hb⟩ := h.eliminate_or_and ?_
    apply (compile_well_typed_or_and ?_ ?_).right
    any_goals apply CompileWellTyped.add_wf
    any_goals apply compile_well_typed_on_wf_expr
    any_goals assumption
    any_goals simp
  case or =>
    have ⟨ha, hb⟩ := h.eliminate_or_and ?_
    apply (compile_well_typed_or_and ?_ ?_).left
    any_goals apply CompileWellTyped.add_wf
    any_goals apply compile_well_typed_on_wf_expr
    any_goals assumption
    any_goals simp
  case unaryApp =>
    have hcond := h.eliminate_unaryApp
    apply compile_well_typed_unaryApp
    any_goals apply CompileWellTyped.add_wf
    any_goals apply compile_well_typed_on_wf_expr
    all_goals assumption
  case binaryApp =>
    have ⟨ha, hb⟩ := h.eliminate_binaryApp
    apply compile_well_typed_binaryApp
    any_goals apply CompileWellTyped.add_wf
    any_goals apply compile_well_typed_on_wf_expr
    any_goals assumption
  case getAttr =>
    have hcond := h.eliminate_getAttr
    apply compile_well_typed_getAttr
    any_goals apply CompileWellTyped.add_wf
    any_goals apply compile_well_typed_on_wf_expr
    all_goals assumption
  case hasAttr =>
    have hcond := h.eliminate_hasAttr
    apply compile_well_typed_hasAttr
    any_goals apply CompileWellTyped.add_wf
    any_goals apply compile_well_typed_on_wf_expr
    all_goals assumption
  case set =>
    have hcond := h.eliminate_set
    apply compile_well_typed_set
    · intros x hx
      apply CompileWellTyped.add_wf
      apply compile_well_typed_on_wf_expr (hcond x hx)
      apply hcond
      assumption
    assumption
  case record =>
    have hcond := h.eliminate_record
    apply compile_well_typed_record
    · intros a x hx
      apply CompileWellTyped.add_wf
      apply compile_well_typed_on_wf_expr (hcond a x hx)
      apply hcond
      assumption
    assumption
  case call =>
    have hcond := h.eliminate_call
    apply compile_well_typed_call
    · intros x hx
      apply CompileWellTyped.add_wf
      apply compile_well_typed_on_wf_expr (hcond x hx)
      apply hcond
      assumption
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
