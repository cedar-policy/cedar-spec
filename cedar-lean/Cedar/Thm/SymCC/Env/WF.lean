/-
 Copyright Cedar Contributors

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Cedar.Thm.SymCC.Data.Basic

/-!
# Basic properties of well-formed symbolic environments

This file proves basic lemmas about well-formedness predicate on environments.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

theorem wf_εnv_for_policies_cons {εnv : SymEnv} {p : Policy} {ps : Policies} :
  εnv.WellFormedForPolicies (p::ps) →
  εnv.WellFormedFor p.toExpr ∧ εnv.WellFormedForPolicies ps
:= by
  intro hwε
  simp only [SymEnv.WellFormedForPolicies, SymEnv.WellFormedFor] at *
  simp only [List.mem_cons, forall_eq_or_imp] at hwε
  simp only [hwε, and_self, true_and]
  intro p hin
  exact hwε.right.right p hin

theorem wf_εnv_for_policies_implies_wf_for_filter (f : Policy → Bool) {εnv : SymEnv} {ps : Policies}  :
  εnv.WellFormedForPolicies ps →
  εnv.WellFormedForPolicies (ps.filter f)
:= by
  intro hwε
  simp only [SymEnv.WellFormedForPolicies] at *
  simp only [hwε.left, List.mem_filter, and_imp, true_and]
  intro p hin _
  exact hwε.right p hin

theorem wf_εnv_all_policies_implies_wf_all {εnv : SymEnv} {ps : Policies} :
  εnv.WellFormedForPolicies ps →
  ∀ p ∈ ps, εnv.WellFormedFor p.toExpr
:= by
  intro hwε p hin
  exact And.intro hwε.left (hwε.right p hin)

theorem wf_env_all_policies_implies_wf_all {env : Env} {ps : Policies} :
  env.WellFormedForPolicies ps →
  ∀ p ∈ ps, env.WellFormedFor p.toExpr
:= by
  intro hwε p hin
  exact And.intro hwε.left (hwε.right p hin)

theorem wf_εnv_valid_refs_implies_wf_εnv_for_set {xs : List Expr} {εnv : SymEnv}
  (hwε : εnv.WellFormed)
  (hvr : ∀ x ∈ xs, εnv.entities.ValidRefsFor x) :
  εnv.WellFormedFor (Expr.set xs)
:= by
  apply And.intro hwε
  apply Expr.ValidRefs.set_valid
  intro x hin
  exact hvr x hin

theorem wf_εnv_for_policies_iff_wf_εnv_for_set {ps : Policies} {εnv : SymEnv}  :
  εnv.WellFormedForPolicies ps ↔
  εnv.WellFormedFor (Expr.set (ps.map Policy.toExpr))
:= by
  constructor <;> intro ⟨hwε, hvr⟩
  case mp =>
    apply wf_εnv_valid_refs_implies_wf_εnv_for_set hwε
    intro x hx
    simp only [List.mem_map] at hx
    replace ⟨p, hin, hx⟩ := hx
    subst hx
    exact hvr p hin
  case mpr =>
    simp only [SymEnv.WellFormedForPolicies, hwε, true_and]
    intro p hin
    simp only [SymEntities.ValidRefsFor] at *
    cases hvr
    rename_i hvr
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hvr
    exact hvr p hin

theorem wf_env_valid_refs_implies_wf_env_for_set {xs : List Expr} {env : Env}
  (hwε : env.WellFormed)
  (hvr : ∀ x ∈ xs, env.entities.ValidRefsFor x) :
  env.WellFormedFor (Expr.set xs)
:= by
  apply And.intro hwε
  apply Expr.ValidRefs.set_valid
  intro x hin
  exact hvr x hin

theorem wf_env_for_policies_iff_wf_env_for_set {ps : Policies} {env : Env}  :
  env.WellFormedForPolicies ps ↔
  env.WellFormedFor (Expr.set (ps.map Policy.toExpr))
:= by
  constructor <;> intro ⟨hwe, hvr⟩
  case mp =>
    apply wf_env_valid_refs_implies_wf_env_for_set hwe
    intro x hx
    simp only [List.mem_map] at hx
    replace ⟨p, hin, hx⟩ := hx
    subst hx
    exact hvr p hin
  case mpr =>
    simp only [Env.WellFormedForPolicies, hwe, true_and]
    intro p hin
    simp only [Entities.ValidRefsFor] at *
    cases hvr
    rename_i hvr
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hvr
    exact hvr p hin

theorem wf_εnv_implies_wf_ρeq {εnv : SymEnv} :
  εnv.WellFormed →
  εnv.request.WellFormed εnv.entities
:= by simp [SymEnv.WellFormed]; intros; assumption

theorem wf_εs_implies_wf_attrs {ety : EntityType} {fₐ : UnaryFunction} {εs : SymEntities}
  (hwε : SymEntities.WellFormed εs)
  (hf  : SymEntities.attrs εs ety = some fₐ) :
  fₐ.WellFormed εs ∧
  fₐ.argType = .entity ety ∧
  fₐ.outType.isCedarRecordType
:= by
  simp only [SymEntities.attrs, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at hf
  replace ⟨d, hf⟩ := hf
  replace ⟨hf, hf'⟩ := hf
  subst hf'
  replace hwε := hwε.right
  specialize hwε ety d hf
  unfold SymEntityData.WellFormed at hwε
  simp only [hwε, and_self]

theorem wf_εs_implies_wf_ancs {ety₁ ety₂ : EntityType} {fₐ : UnaryFunction} {εs : SymEntities}
  (hwε : SymEntities.WellFormed εs)
  (hf  : SymEntities.ancestorsOfType εs ety₁ ety₂ = some fₐ) :
  fₐ.WellFormed εs ∧
  fₐ.argType = .entity ety₁ ∧
  fₐ.outType = .set (.entity ety₂)
:= by
  simp only [SymEntities.ancestorsOfType, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at hf
  replace ⟨ancs₁, ha, hf⟩ := hf
  simp only [SymEntities.ancestors, Option.bind_eq_bind, Option.bind_eq_some, Option.some.injEq] at ha
  replace ⟨εd, hf', ha⟩ := ha
  subst ha
  exact (hwε.right ety₁ εd hf').right.right.right.left ety₂ fₐ hf

theorem wf_εs_implies_wf_tags {ety : EntityType} {τs : SymTags} {εs : SymEntities}
  (hwε : SymEntities.WellFormed εs)
  (hτs : εs.tags ety = some (some τs)) :
  τs.WellFormed εs ety
:= by
  simp only [SymEntities.tags, Option.map_eq_some'] at hτs
  replace ⟨δ, hf, hτs⟩ := hτs
  exact (hwε.right ety δ hf).right.right.right.right.right.left τs hτs

theorem wf_udf_implies_lit {f : UDF} {εs : SymEntities} :
  f.WellFormed εs → f.isLiteral
:= by
  intro hwf
  simp only [UnaryFunction.WellFormed, UDF.WellFormed] at hwf
  simp only [UDF.isLiteral, hwf.left.right, Bool.true_and, List.all_eq_true, Bool.and_eq_true]
  intro (tᵢ, tₒ) hin
  replace hwf := hwf.right.right.right tᵢ tₒ hin
  simp only [hwf.left.right, hwf.right.right.left.right, and_self]

theorem wf_εnv_for_ite_implies {x₁ x₂ x₃ : Expr} {εnv : SymEnv} :
  εnv.WellFormedFor (.ite x₁ x₂ x₃) →
  εnv.WellFormedFor x₁ ∧
  εnv.WellFormedFor x₂ ∧
  εnv.WellFormedFor x₃
:= by
  simp only [SymEnv.WellFormedFor]
  intro h₁
  replace ⟨h₁, h₂⟩ := h₁
  cases h₂
  rename_i h₂ h₃ h₄
  simp only [h₁, h₂, and_self, h₃, h₄]

theorem wf_env_for_ite_implies {x₁ x₂ x₃ : Expr} {env : Env}
  (h₁ : env.WellFormedFor (.ite x₁ x₂ x₃)) :
  env.WellFormedFor x₁ ∧
  env.WellFormedFor x₂ ∧
  env.WellFormedFor x₃
:= by
  simp only [Env.WellFormedFor] at *
  replace ⟨h₁, h₂⟩ := h₁
  cases h₂
  rename_i h₂ h₃ h₄
  simp only [h₁, h₂, and_self, h₃, h₄]

local macro "show_wf_εnv_for_binary_expr_implies" : tactic => do
 `(tactic| (
    intro h₁
    replace ⟨h₁, h₂⟩ := h₁
    cases h₂
    rename_i h₂ h₃
    exact (And.intro (And.intro h₁ h₂) (And.intro h₁ h₃))
  ))

theorem wf_εnv_for_and_implies {x₁ x₂ : Expr} {εnv : SymEnv} :
  εnv.WellFormedFor (.and x₁ x₂) →
  εnv.WellFormedFor x₁ ∧
  εnv.WellFormedFor x₂
:= by show_wf_εnv_for_binary_expr_implies

theorem wf_env_for_and_implies {x₁ x₂ : Expr} {env : Env} :
  env.WellFormedFor (.and x₁ x₂) →
  env.WellFormedFor x₁ ∧
  env.WellFormedFor x₂
:= by show_wf_εnv_for_binary_expr_implies

theorem wf_εnv_for_or_implies {x₁ x₂ : Expr} {εnv : SymEnv} :
  εnv.WellFormedFor (.or x₁ x₂) →
  εnv.WellFormedFor x₁ ∧
  εnv.WellFormedFor x₂
:= by show_wf_εnv_for_binary_expr_implies

theorem wf_env_for_or_implies {x₁ x₂ : Expr} {env : Env} :
  env.WellFormedFor (.or x₁ x₂) →
  env.WellFormedFor x₁ ∧
  env.WellFormedFor x₂
:= by show_wf_εnv_for_binary_expr_implies

theorem wf_εnv_for_binaryApp_implies {op : BinaryOp} {x₁ x₂ : Expr} {εnv : SymEnv} :
  εnv.WellFormedFor (.binaryApp op x₁ x₂) →
  εnv.WellFormedFor x₁ ∧
  εnv.WellFormedFor x₂
:= by show_wf_εnv_for_binary_expr_implies

theorem wf_env_for_binaryApp_implies {op : BinaryOp} {x₁ x₂ : Expr} {env : Env} :
  env.WellFormedFor (.binaryApp op x₁ x₂) →
  env.WellFormedFor x₁ ∧
  env.WellFormedFor x₂
:= by show_wf_εnv_for_binary_expr_implies

local macro "show_wf_εnv_for_unary_expr_implies" : tactic => do
 `(tactic| (
    intro h₁
    replace ⟨h₁, h₂⟩ := h₁
    cases h₂
    rename_i h₂
    exact And.intro h₁ h₂
  ))

theorem wf_εnv_for_hasAttr_implies {x₁ : Expr} {a : Attr} {εnv : SymEnv} :
  εnv.WellFormedFor (.hasAttr x₁ a) →
  εnv.WellFormedFor x₁
:= by show_wf_εnv_for_unary_expr_implies

theorem wf_env_for_hasAttr_implies {x₁ : Expr} {a : Attr} {env : Env} :
  env.WellFormedFor (.hasAttr x₁ a) →
  env.WellFormedFor x₁
:= by show_wf_εnv_for_unary_expr_implies

theorem wf_εnv_for_getAttr_implies {x₁ : Expr} {a : Attr} {εnv : SymEnv} :
  εnv.WellFormedFor (.getAttr x₁ a) →
  εnv.WellFormedFor x₁
:= by show_wf_εnv_for_unary_expr_implies

theorem wf_env_for_getAttr_implies {x₁ : Expr} {a : Attr} {env : Env} :
  env.WellFormedFor (.getAttr x₁ a) →
  env.WellFormedFor x₁
:= by show_wf_εnv_for_unary_expr_implies

theorem wf_εnv_for_unaryApp_implies {op : UnaryOp} {x₁ : Expr} {εnv : SymEnv} :
  εnv.WellFormedFor (.unaryApp op x₁) →
  εnv.WellFormedFor x₁
:= by show_wf_εnv_for_unary_expr_implies

theorem wf_env_for_unaryApp_implies {op : UnaryOp} {x₁ : Expr} {env : Env} :
  env.WellFormedFor (.unaryApp op x₁) →
  env.WellFormedFor x₁
:= by show_wf_εnv_for_unary_expr_implies

local macro "show_wf_εnv_for_nary_expr_implies" : tactic => do
 `(tactic| (
    intro hwf x hmem
    replace ⟨hwf, hwr⟩ := hwf
    cases hwr
    rename_i hwr
    exact (And.intro hwf (hwr x hmem))
  ))

theorem wf_εnv_for_set_implies {xs : List Expr} {εnv : SymEnv} :
  εnv.WellFormedFor (.set xs) →
  ∀ x, x ∈ xs → εnv.WellFormedFor x
:= by show_wf_εnv_for_nary_expr_implies

theorem wf_env_for_set_implies {xs : List Expr} {env : Env} :
  env.WellFormedFor (.set xs) →
  ∀ x, x ∈ xs → env.WellFormedFor x
:= by show_wf_εnv_for_nary_expr_implies

theorem wf_εnv_for_record_implies {axs : List (Attr × Expr)} {εnv : SymEnv} :
  εnv.WellFormedFor (.record axs) →
  ∀ ax, ax ∈ axs → εnv.WellFormedFor ax.snd
:= by show_wf_εnv_for_nary_expr_implies

theorem wf_env_for_record_implies {axs : List (Attr × Expr)} {env : Env} :
  env.WellFormedFor (.record axs) →
  ∀ ax, ax ∈ axs → env.WellFormedFor ax.snd
:= by show_wf_εnv_for_nary_expr_implies

theorem wf_εnv_for_call_implies {f : ExtFun} {xs : List Expr} {εnv : SymEnv} :
  εnv.WellFormedFor (.call f xs) →
  ∀ x, x ∈ xs → εnv.WellFormedFor x
:= by show_wf_εnv_for_nary_expr_implies

theorem wf_env_for_call_implies {f : ExtFun} {xs : List Expr} {env : Env} :
  env.WellFormedFor (.call f xs) →
  ∀ x, x ∈ xs → env.WellFormedFor x
:= by show_wf_εnv_for_nary_expr_implies

def SameDomain (εs₁ εs₂ : SymEntities) : Prop :=
  (∀ uid, εs₁.isValidEntityUID uid = εs₂.isValidEntityUID uid) ∧
  (∀ ety, εs₁.isValidEntityType ety = εs₂.isValidEntityType ety)

theorem same_domain_symmetric {εs₁ εs₂ : SymEntities} :
  SameDomain εs₁ εs₂ → SameDomain εs₂ εs₁
:= by
  unfold SameDomain
  intro h
  constructor
  case left  => intro uid ; simp only [h.left uid]
  case right => intro ety ; simp only [h.right ety]

theorem wf_term_type_same_domain {εs₁ εs₂ : SymEntities} {ty : TermType} :
  SameDomain εs₁ εs₂ →
  TermType.WellFormed εs₁ ty →
  TermType.WellFormed εs₂ ty
:= by
  intro h₁ h₂
  induction h₂
  case bool_wf =>
    exact TermType.WellFormed.bool_wf
  case bitvec_wf =>
    exact TermType.WellFormed.bitvec_wf
  case string_wf =>
    exact TermType.WellFormed.string_wf
  case ext_wf =>
    exact TermType.WellFormed.ext_wf
  case option_wf ih =>
    exact TermType.WellFormed.option_wf ih
  case set_wf ih =>
    exact TermType.WellFormed.set_wf ih
  case entity_wf ety ih =>
    rw [h₁.right ety] at ih
    exact TermType.WellFormed.entity_wf ih
  case record_wf h₂ ih =>
    apply TermType.WellFormed.record_wf _ h₂
    intro a ty h₃
    exact ih a ty h₃

theorem wf_term_var_same_domain {εs₁ εs₂ : SymEntities} {v : TermVar} :
  SameDomain εs₁ εs₂ →
  TermVar.WellFormed εs₁ v →
  TermVar.WellFormed εs₂ v
:= by
  simp only [TermVar.WellFormed]
  intro h₁ h₂
  exact wf_term_type_same_domain h₁ h₂

theorem wf_term_prim_same_domain {εs₁ εs₂ : SymEntities} {p : TermPrim} :
  SameDomain εs₁ εs₂ →
  TermPrim.WellFormed εs₁ p →
  TermPrim.WellFormed εs₂ p
:= by
  intro h₁ h₂
  cases h₂
  case bool_wf        => exact TermPrim.WellFormed.bool_wf
  case bitvec_wf      => exact TermPrim.WellFormed.bitvec_wf
  case string_wf      => exact TermPrim.WellFormed.string_wf
  case ext_wf         => exact TermPrim.WellFormed.ext_wf
  case entity_wf _ h₃ =>
    rw [h₁.left] at h₃
    exact TermPrim.WellFormed.entity_wf h₃

theorem wf_uuf_same_domain {εs₁ εs₂ : SymEntities} {f : UUF} :
  SameDomain εs₁ εs₂ →
  f.WellFormed εs₁ →
  f.WellFormed εs₂
:= by
  simp only [UUF.WellFormed, and_imp]
  intro h₁ h₂ h₃
  simp only [wf_term_type_same_domain h₁ h₂, wf_term_type_same_domain h₁ h₃, and_self]

theorem wt_op_same_domain {εs₁ εs₂ : SymEntities} {op : Op} {ts : List Term} {ty : TermType} :
  SameDomain εs₁ εs₂ →
  Op.WellTyped εs₁ op ts ty →
  Op.WellTyped εs₂ op ts ty
:= by
  intro h₁ h₂
  cases h₂
  case not_wt h           => exact Op.WellTyped.not_wt h
  case and_wt h h'        => exact Op.WellTyped.and_wt h h'
  case or_wt h h'         => exact Op.WellTyped.or_wt h h'
  case eq_wt h            => exact Op.WellTyped.eq_wt h
  case ite_wt h h'        => exact Op.WellTyped.ite_wt h h'
  case uuf_wt h h'        => exact Op.WellTyped.uuf_wt h (wf_uuf_same_domain h₁ h')
  case bvneg_wt h         => exact Op.WellTyped.bvneg_wt h
  case bvnego_wt h        => exact Op.WellTyped.bvnego_wt h
  case bvadd_wt h h'      => exact Op.WellTyped.bvadd_wt h h'
  case bvsub_wt h h'      => exact Op.WellTyped.bvsub_wt h h'
  case bvmul_wt h h'      => exact Op.WellTyped.bvmul_wt h h'
  case bvsdiv_wt h h'     => exact Op.WellTyped.bvsdiv_wt h h'
  case bvudiv_wt h h'     => exact Op.WellTyped.bvudiv_wt h h'
  case bvsrem_wt h h'     => exact Op.WellTyped.bvsrem_wt h h'
  case bvsmod_wt h h'     => exact Op.WellTyped.bvsmod_wt h h'
  case bvumod_wt h h'     => exact Op.WellTyped.bvumod_wt h h'
  case bvshl_wt h h'      => exact Op.WellTyped.bvshl_wt h h'
  case bvlshr_wt h h'     => exact Op.WellTyped.bvlshr_wt h h'
  case bvsaddo_wt h h'    => exact Op.WellTyped.bvsaddo_wt h h'
  case bvssubo_wt h h'    => exact Op.WellTyped.bvssubo_wt h h'
  case bvsmulo_wt h h'    => exact Op.WellTyped.bvsmulo_wt h h'
  case bvslt_wt h h'      => exact Op.WellTyped.bvslt_wt h h'
  case bvsle_wt h h'      => exact Op.WellTyped.bvsle_wt h h'
  case bvult_wt h h'      => exact Op.WellTyped.bvult_wt h h'
  case bvule_wt h h'      => exact Op.WellTyped.bvule_wt h h'
  case zero_extend_wt h   => exact Op.WellTyped.zero_extend_wt h
  case set.member_wt h    => exact Op.WellTyped.set.member_wt h
  case set.subset_wt h h' => exact Op.WellTyped.set.subset_wt h h'
  case set.inter_wt h h'  => exact Op.WellTyped.set.inter_wt h h'
  case option.get_wt h    => exact Op.WellTyped.option.get_wt h
  case record.get_wt h h' => exact Op.WellTyped.record.get_wt h h'
  case string.like_wt h   => exact Op.WellTyped.string.like_wt h
  case ext_wt h           => exact Op.WellTyped.ext_wt h

theorem wf_term_same_domain {εs₁ εs₂ : SymEntities} {t : Term} :
  SameDomain εs₁ εs₂ →
  t.WellFormed εs₁ →
  t.WellFormed εs₂
:= by
  intro h₁ h₂
  induction h₂
  case prim_wf h₃ =>
    exact Term.WellFormed.prim_wf (wf_term_prim_same_domain h₁ h₃)
  case var_wf h₃ =>
    exact Term.WellFormed.var_wf (wf_term_var_same_domain h₁ h₃)
  case none_wf h₃ =>
    exact Term.WellFormed.none_wf (wf_term_type_same_domain h₁ h₃)
  case some_wf ih =>
    exact Term.WellFormed.some_wf ih
  case app_wf h₃ ih =>
    apply Term.WellFormed.app_wf
    case h₁ => intro t ht ; exact ih t ht
    case h₂ => exact wt_op_same_domain h₁ h₃
  case set_wf h₃ h₄ h₅ ih =>
    apply Term.WellFormed.set_wf
    case h₁ => intro t ht ; exact ih t ht
    case h₂ => exact h₃
    case h₃ => exact wf_term_type_same_domain h₁ h₄
    case h₄ => exact h₅
  case record_wf h₃ ih =>
    apply Term.WellFormed.record_wf
    case h₁ => intro a t ht ; exact ih a t ht
    case h₂ => exact h₃

theorem wfl_term_same_domain {εs₁ εs₂ : SymEntities} {t : Term} :
  SameDomain εs₁ εs₂ →
  t.WellFormedLiteral εs₁ →
  t.WellFormedLiteral εs₂
:= by
  simp only [Term.WellFormedLiteral, and_imp]
  intro h₁ h₂ h₃
  simp only [h₃, and_true]
  exact wf_term_same_domain h₁ h₂

theorem wf_udf_same_domain {εs₁ εs₂ : SymEntities} {f : UDF} :
  SameDomain εs₁ εs₂ →
  f.WellFormed εs₁ →
  f.WellFormed εs₂
:= by
  simp only [UDF.WellFormed, and_imp]
  intro h₁ h₂ h₃ h₄ h₅
  simp only [h₃, h₄, true_and]
  constructor
  case left =>
    exact wfl_term_same_domain h₁ h₂
  case right =>
    intro tᵢ tₒ h₆
    specialize h₅ tᵢ tₒ h₆
    replace ⟨h₅, h₇, h₈, h₉⟩ := h₅
    simp only [and_self, h₇, h₉,
      wfl_term_same_domain h₁ h₅,
      wfl_term_same_domain h₁ h₈]

theorem wfp_term_app_same_domain {εs₁ εs₂ : SymEntities} {t : Term} :
  SameDomain εs₁ εs₂ →
  Term.WellFormedPartialApp εs₁ t →
  Term.WellFormedPartialApp εs₂ t
:= by
  intro hd h₂
  cases h₂
  case none_wfp h₁ =>
    exact Term.WellFormedPartialApp.none_wfp (wf_term_type_same_domain hd h₁)
  case ext_ipddr_addr4_wfp ip h₁ =>
    exact Term.WellFormedPartialApp.ext_ipddr_addr4_wfp h₁
  case ext_ipddr_prefix4_wfp h₁ =>
    exact Term.WellFormedPartialApp.ext_ipddr_prefix4_wfp h₁
  case ext_ipddr_addr6_wfp h₁ =>
    exact Term.WellFormedPartialApp.ext_ipddr_addr6_wfp h₁
  case ext_ipddr_prefix6_wfp h₁ =>
    exact Term.WellFormedPartialApp.ext_ipddr_prefix6_wfp h₁

theorem wf_interpretation_same_domain {εs₁ εs₂ : SymEntities} {I : Interpretation} :
  SameDomain εs₁ εs₂ →
  I.WellFormed εs₁ →
  I.WellFormed εs₂
:= by
  intro h₁ h₂
  have h₁' := same_domain_symmetric h₁
  simp only [Interpretation.WellFormed]
  simp only [Interpretation.WellFormed] at h₂
  constructor
  case left =>
    intro v h₃
    replace h₂ := h₂.left v (wf_term_var_same_domain h₁' h₃)
    simp only [Interpretation.WellFormed.WellFormedVarInterpretation, Term.WellFormedLiteral] at *
    constructor
    case left =>
      simp only [h₂, and_true]
      exact wf_term_same_domain h₁ h₂.left.left
    case right =>
      simp only [TermVar.WellFormed] at h₃
      exact h₂.right
  case right =>
    constructor
    case left =>
      intro f h₃
      replace h₂ := h₂.right.left f (wf_uuf_same_domain h₁' h₃)
      simp only [Interpretation.WellFormed.WellFormedUUFInterpretation] at *
      simp only [h₂, and_self, and_true]
      exact wf_udf_same_domain h₁ h₂.left
    case right =>
      intro t h₃
      replace h₂ := h₂.right.right t (wfp_term_app_same_domain h₁' h₃)
      simp only [Interpretation.WellFormed.WellFormedPartialAppInterpretation] at *
      simp only [h₂, and_true]
      exact wfl_term_same_domain h₁ h₂.left

theorem wf_ρeq_same_domain {εs₁ εs₂ : SymEntities} {ρeq : SymRequest} :
  SameDomain εs₁ εs₂ →
  SymRequest.WellFormed εs₁ ρeq →
  SymRequest.WellFormed εs₂ ρeq
:= by
  simp only [SymRequest.WellFormed]
  intro h₁ h₂
  have ⟨hp, hp', ha, ha', hr, hr', hc, hc'⟩ := h₂
  simp only [and_self,
    wf_term_same_domain h₁ hp, hp',
    wf_term_same_domain h₁ ha, ha',
    wf_term_same_domain h₁ hr, hr',
    wf_term_same_domain h₁ hc, hc']

theorem wf_uf_same_domain {εs₁ εs₂ : SymEntities} {f : UnaryFunction} :
  SameDomain εs₁ εs₂ →
  f.WellFormed εs₁ →
  f.WellFormed εs₂
:= by
  simp only [UnaryFunction.WellFormed]
  intro h₁ h₂
  cases f <;> simp only at *
  case uuf => exact wf_uuf_same_domain h₁ h₂
  case udf => exact wf_udf_same_domain h₁ h₂

theorem wf_εdata_same_domain {εs₁ εs₂ : SymEntities} {ety : EntityType} {εd : SymEntityData} :
  SameDomain εs₁ εs₂ →
  SymEntityData.WellFormed εs₁ ety εd →
  SymEntityData.WellFormed εs₂ ety εd
:= by
  simp only [SymEntityData.WellFormed, and_imp]
  intro h₁ h₂ h₃ h₄ h₅
  simp only [wf_uf_same_domain h₁ h₂, h₃, h₄, true_and]
  intro hwf
  simp only [hwf, true_and]
  intro htags hmems
  constructor
  · intro pty f h₆
    specialize h₅ pty f h₆
    simp only [wf_uf_same_domain h₁ h₅.left, h₅, and_self]
  · constructor
    · intro τs h₆
      specialize htags τs h₆
      simp only [SymTags.WellFormed] at *
      simp only [wf_uf_same_domain h₁ htags.left, htags,
        wf_uf_same_domain h₁ htags.right.right.right.left, and_self]
    · exact hmems

theorem prim_valid_refs_same_domain {εs₁ εs₂ : SymEntities} {p : Prim} :
  SameDomain εs₁ εs₂ →
  p.ValidRef (εs₁.isValidEntityUID · = true) →
  p.ValidRef (εs₂.isValidEntityUID · = true)
:= by
  intro h₁ h₂
  cases p <;> simp only [Prim.ValidRef] at *
  rename_i uid
  rw [h₁.left uid] at h₂
  exact h₂

theorem expr_valid_refs_same_domain {εs₁ εs₂ : SymEntities} {x : Expr} :
  SameDomain εs₁ εs₂ →
  x.ValidRefs (εs₁.isValidEntityUID · = true) →
  x.ValidRefs (εs₂.isValidEntityUID · = true)
:= by
  intro h₁ h₂
  induction h₂
  case lit_valid h =>
    exact Expr.ValidRefs.lit_valid (prim_valid_refs_same_domain h₁ h)
  case var_valid =>
    exact Expr.ValidRefs.var_valid
  case ite_valid ih₁ ih₂ ih₃ =>
    exact Expr.ValidRefs.ite_valid ih₁ ih₂ ih₃
  case and_valid ih₁ ih₂ =>
    exact Expr.ValidRefs.and_valid ih₁ ih₂
  case or_valid ih₁ ih₂ =>
    exact Expr.ValidRefs.or_valid ih₁ ih₂
  case binaryApp_valid ih₁ ih₂ =>
    exact Expr.ValidRefs.binaryApp_valid ih₁ ih₂
  case unaryApp_valid ih₁ =>
    exact Expr.ValidRefs.unaryApp_valid ih₁
  case hasAttr_valid ih₁ =>
    exact Expr.ValidRefs.hasAttr_valid ih₁
  case getAttr_valid ih₁ =>
    exact Expr.ValidRefs.getAttr_valid ih₁
  case set_valid ih₁ =>
    exact Expr.ValidRefs.set_valid ih₁
  case record_valid ih₁ =>
    exact Expr.ValidRefs.record_valid ih₁
  case call_valid ih₁ =>
    exact Expr.ValidRefs.call_valid ih₁


end Cedar.Thm
