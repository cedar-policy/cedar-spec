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

import Cedar.Thm.SymCC.Compiler.Basic

/-!
This file proves inversion lemmas for `compile`.
--/

namespace Cedar.Thm

open Batteries Data Spec SymCC Factory

def CompileIfSym (t t₁ : Term) (r₂ r₃ : SymCC.Result Term) : Prop :=
  t₁.typeOf = (.option .bool) ∧
  ∃ t₂ t₃,
    r₂ = .ok t₂ ∧
    r₃ = .ok t₃ ∧
    t₂.typeOf = t₃.typeOf ∧
    t = ifSome t₁ (ite (option.get t₁) t₂ t₃)

theorem compile_ite_ok_implies {x₁ x₂ x₃ : Expr} {εnv : SymEnv} {t : Term}
  (h₁ : compile (.ite x₁ x₂ x₃) εnv = .ok t) :
  ∃ t₁,
    (compile x₁ εnv) = .ok t₁ ∧
    match t₁ with
     | .some (.prim (.bool true))  => t = compile x₂ εnv
     | .some (.prim (.bool false)) => t = compile x₃ εnv
     | t₁ => CompileIfSym t t₁ (compile x₂ εnv) (compile x₃ εnv)
:= by
  simp only [CompileIfSym]
  simp only [compile, compileIf] at h₁
  simp_do_let (compile x₁ εnv) at h₁
  split at h₁
  case h_1 =>
    exists Term.some (Term.prim (TermPrim.bool true))
    simp only [h₁, and_self]
  case h_2 =>
    exists Term.some (Term.prim (TermPrim.bool false))
    simp only [h₁, and_self]
  case h_3 t₁ _ _ _ _ _ h₂ =>
    simp_do_let (compile x₂ εnv) at h₁
    simp_do_let (compile x₃ εnv) at h₁
    split at h₁ <;> try { contradiction }
    rename_i h₃
    simp only [Except.ok.injEq] at h₁
    exists t₁
    simp only [h₁, h₂, h₃, Except.ok.injEq, exists_and_left, exists_eq_left', true_and,
      compile_ite_ok_implies]
  case h_4 => simp only [reduceCtorEq] at h₁

def CompileAndSym (t t₁ : Term) (r₂ : SymCC.Result Term): Prop :=
  t₁.typeOf = .option .bool ∧
  ∃ t₂,
    r₂ = .ok t₂ ∧
    t₂.typeOf = .option .bool ∧
    t = ifSome t₁ (ite (option.get t₁) t₂ (.some (.prim (.bool false))))

theorem compile_and_ok_implies {x₁ x₂ : Expr} {εnv : SymEnv} {t : Term}
  (h₁ : compile (.and x₁ x₂) εnv = .ok t) :
  ∃ t₁,
    (compile x₁ εnv) = .ok t₁ ∧
    match t₁ with
     | .some (.prim (.bool false)) => t = t₁
     | _ => CompileAndSym t t₁ (compile x₂ εnv)
:= by
  simp only [compile] at h₁
  simp_do_let (compile x₁ εnv) at h₁ ; rename_i t₁ h₂
  exists t₁
  simp only [true_and, CompileAndSym]
  simp only [compileAnd] at h₁
  split at h₁
  case h_1 =>
    simp only [Except.ok.injEq] at *
    simp only [h₁]
  case h_2 h₃ h₄ =>
    simp_do_let (compile x₂ εnv) at h₁ ; rename_i t₂ h₅
    split
    case h_1 => simp only [forall_const] at h₃
    case h_2 =>
      simp only [h₄, Except.ok.injEq, exists_eq_left', true_and]
      split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
      rename_i h₆
      simp only [someOf] at h₁
      simp only [h₆, h₁, and_self]
  case h_3 => simp only [reduceCtorEq] at h₁

def CompileOrSym (t t₁ : Term) (r₂ : SymCC.Result Term): Prop :=
  t₁.typeOf = .option .bool ∧
  ∃ t₂,
    r₂ = .ok t₂ ∧
    t₂.typeOf = .option .bool ∧
    t = ifSome t₁ (ite (option.get t₁) (.some (.prim (.bool true))) t₂)

theorem compile_or_ok_implies {x₁ x₂ : Expr} {εnv : SymEnv} {t : Term}
  (h₁ : compile (.or x₁ x₂) εnv = .ok t) :
  ∃ t₁,
    (compile x₁ εnv) = .ok t₁ ∧
    match t₁ with
    | .some (.prim (.bool true)) => t = t₁
    | _ => CompileOrSym t t₁ (compile x₂ εnv)
:= by
  simp only [compile] at h₁
  simp_do_let (compile x₁ εnv) at h₁ ; rename_i t₁ h₂
  exists t₁
  simp only [true_and, CompileOrSym]
  simp only [compileOr] at h₁
  split at h₁
  case h_1 =>
    simp only [Except.ok.injEq] at *
    simp only [h₁]
  case h_2 h₃ h₄ =>
    simp_do_let (compile x₂ εnv) at h₁ ; rename_i t₂ h₅
    split
    case h_1 => simp only [forall_const] at h₃
    case h_2 =>
      simp only [h₄, Except.ok.injEq, exists_eq_left', true_and]
      split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
      rename_i h₆
      simp only [someOf] at h₁
      simp only [h₆, h₁, and_self]
  case h_3 => simp only [reduceCtorEq] at h₁

theorem compileAttrsOf_ok_implies {t t₁ : Term} {εs : SymEntities}
  (h₁ : compileAttrsOf t₁ εs = .ok t) :
  (∃ rty, t₁.typeOf = .record rty ∧ t = t₁) ∨
  (∃ ety fₐ, t₁.typeOf = .entity ety ∧ εs.attrs ety = .some fₐ ∧ t = app fₐ t₁)
:= by
  simp only [compileAttrsOf] at h₁
  split at h₁
  case h_3 => simp only [reduceCtorEq] at h₁
  case h_2 rty heq =>
    simp only [Except.ok.injEq] at h₁
    subst h₁
    apply Or.inl
    exists rty
  case h_1 ety heq =>
    split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
    subst h₁
    rename_i fₐ hf
    apply Or.inr
    exists ety, fₐ

def RecordHasAttr (t t₁ : Term) (rty : Map Attr TermType) (a : Attr) : Prop :=
  t₁.typeOf = .record rty ∧
  match rty.find? a with
  | .some (.option _) => t = .some (isSome (record.get t₁ a))
  | .some _           => t = .some (.prim (.bool true))
  | .none             => t = .some (.prim (.bool false))

theorem compileHasAttr_ok_implies {t t₁ : Term} {a : Attr} {εs : SymEntities}
  (h₁ : compileHasAttr t₁ a εs = .ok t) :
  ∃ t₂ rty,
    compileAttrsOf t₁ εs = .ok t₂ ∧
    RecordHasAttr t t₂ rty a
:= by
  simp only [compileHasAttr] at h₁
  simp_do_let (compileAttrsOf t₁ εs) at h₁
  rename_i t₂ h₂
  split at h₁ <;> simp only [someOf, reduceCtorEq] at h₁
  rename_i rty heq
  exists t₂, rty ; simp only [true_and]
  unfold RecordHasAttr
  simp only [Except.ok.injEq, heq, true_and] at *
  split <;> rename_i hfind <;>
  simp only [hfind, someOf, Except.ok.injEq] at h₁ <;>
  simp only [h₁]

theorem compile_hasAttr_ok_implies {a : Attr} {x₁ : Expr} {εnv : SymEnv} {t : Term}
  (h₁ : compile (.hasAttr x₁ a) εnv = .ok t) :
  ∃ t₁ t₂,
    (compile x₁ εnv) = .ok t₁ ∧
    (compileHasAttr (option.get t₁) a εnv.entities) = .ok t₂ ∧
    t = ifSome t₁ t₂
:= by
  simp only [compile] at h₁
  simp_do_let (compile x₁ εnv) at h₁
  rename_i t₂ h₂
  simp_do_let (compileHasAttr (option.get t₂) a εnv.entities) at h₁
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₁
  exists t₂, t₃
  simp only [h₃, h₁, and_self]

def RecordGetAttr (t t₁ : Term) (rty : Map Attr TermType) (a : Attr) : Prop :=
  t₁.typeOf = .record rty ∧
  ∃ tyₐ, rty.find? a = .some tyₐ ∧
    match tyₐ with
    | .option _ => t = (record.get t₁ a)
    | _         => t = .some (record.get t₁ a)

theorem compileGetAttr_ok_implies {t t₁ : Term} {a : Attr} {εs : SymEntities}
  (h₁ : compileGetAttr t₁ a εs = .ok t) :
  ∃ t₂ rty,
    compileAttrsOf t₁ εs = .ok t₂ ∧
    RecordGetAttr t t₂ rty a
:= by
  simp only [compileGetAttr] at h₁
  simp_do_let (compileAttrsOf t₁ εs) at h₁
  rename_i t₂ h₂
  split at h₁ <;> simp only [someOf, reduceCtorEq] at h₁
  rename_i rty heq
  exists t₂, rty ; simp only [true_and]
  unfold RecordGetAttr
  simp only [Except.ok.injEq, heq, true_and] at *
  split at h₁ <;>
  simp only [Except.ok.injEq, reduceCtorEq] at h₁ <;>
  subst h₁
  case h_1 =>
    rename_i tyₐ _
    exists (.option tyₐ)
  case h_2 =>
    rename_i tyₐ _ heq
    exists tyₐ
    simp only [heq, RecordGetAttr.match_1.eq_2, and_self]

theorem compile_getAttr_ok_implies {a : Attr} {x₁ : Expr} {εnv : SymEnv} {t : Term}
  (h₁ : compile (.getAttr x₁ a) εnv = .ok t) :
  ∃ t₁ t₂,
    (compile x₁ εnv) = .ok t₁ ∧
    (compileGetAttr (option.get t₁) a εnv.entities) = .ok t₂ ∧
    t = ifSome t₁ t₂
:= by
  simp only [compile] at h₁
  simp_do_let (compile x₁ εnv) at h₁
  rename_i t₂ h₂
  simp_do_let (compileGetAttr (option.get t₂) a εnv.entities) at h₁
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₁
  exists t₂, t₃
  simp only [h₃, h₁, and_self]

theorem compileApp₁_ok_implies {op₁ : UnaryOp} {t t₁ : Term}
  (h₁ : compileApp₁ op₁ t₁ = .ok t) :
  match op₁ with
  | .not     => t₁.typeOf = .bool ∧ t = Term.some (not t₁)
  | .neg     => t₁.typeOf = .bitvec 64 ∧ t = ifFalse (bvnego t₁) (bvneg t₁)
  | .like p  => t₁.typeOf = .string ∧ t = Term.some (string.like t₁ p)
  | .is ety₁ => ∃ ety₂, t₁.typeOf = .entity ety₂ ∧ t = Term.some (ety₁ = ety₂ : Bool)
  | .isEmpty => (∃ ty, t₁.typeOf = .set ty) ∧ t = Term.some (set.isEmpty t₁)
:= by
  cases op₁ <;> simp only
  case not | neg | like | isEmpty =>
    simp only [compileApp₁] at h₁
    split at h₁ <;>
    rename_i hop hty <;>
    simp only [false_implies, forall_const, UnaryOp.like.injEq, forall_eq', reduceCtorEq] at hop h₁
    simp only [someOf, Except.ok.injEq] at h₁
    simp only [hop, hty, h₁, TermType.set.injEq, exists_eq', and_self]
  case is =>
    simp only [compileApp₁] at h₁
    split at h₁ <;>
    rename_i hop hty <;>
    simp only [Except.ok.injEq, false_implies, forall_const, UnaryOp.like.injEq, reduceCtorEq] at hop h₁
    simp only [someOf, Except.ok.injEq] at h₁
    simp only [UnaryOp.is.injEq] at hop
    subst hop
    simp only [hty, TermType.prim.injEq, TermPrimType.entity.injEq, exists_eq_left', h₁]

theorem compile_unaryApp_ok_implies {op₁ : UnaryOp} {x₁ : Expr} {εnv : SymEnv} {t : Term}
  (h₁ : compile (.unaryApp op₁ x₁) εnv = .ok t) :
  ∃ t₁ t₂,
    (compile x₁ εnv) = .ok t₁ ∧
    (compileApp₁ op₁ (option.get t₁)) = .ok t₂ ∧
    t = ifSome t₁ t₂
:= by
  simp only [compile] at h₁
  simp_do_let (compile x₁ εnv) at h₁
  rename_i t₂ h₂
  simp_do_let (compileApp₁ op₁ (option.get t₂)) at h₁
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₁
  exists t₂, t₃
  simp only [h₃, h₁, and_self]

local macro "show_compileApp₂_arith_op_ok_implies" : tactic => do
 `(tactic| (
  intro h₁
  simp only [compileApp₂] at h₁
  split at h₁ <;> simp only [reduceCtorEq] at *
  all_goals(
    rename_i hty₁ hty₂ _
    simp only [someOf, Except.ok.injEq] at h₁
    simp only [hty₁, hty₂, h₁, Or.inl, Or.inr, and_self]
  )
))

theorem compileApp₂_less_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .less t₁ t₂ εs = .ok t →
  (
    (t₁.typeOf = .bitvec 64 ∧ t₂.typeOf = .bitvec 64 ∧ t = Term.some (bvslt t₁ t₂)) ∨
    (t₁.typeOf = .ext .duration ∧ t₂.typeOf = .ext .duration ∧ t = Term.some (bvslt (ext.duration.val t₁) (ext.duration.val t₂))) ∨
    (t₁.typeOf = .ext .datetime ∧ t₂.typeOf = .ext .datetime ∧ t = Term.some (bvslt (ext.datetime.val t₁) (ext.datetime.val t₂)))
  )
:= by show_compileApp₂_arith_op_ok_implies

theorem compileApp₂_lessEq_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .lessEq t₁ t₂ εs = .ok t →
  (
    (t₁.typeOf = .bitvec 64 ∧ t₂.typeOf = .bitvec 64 ∧ t = Term.some (bvsle t₁ t₂)) ∨
    (t₁.typeOf = .ext .duration ∧ t₂.typeOf = .ext .duration ∧ t = Term.some (bvsle (ext.duration.val t₁) (ext.duration.val t₂))) ∨
    (t₁.typeOf = .ext .datetime ∧ t₂.typeOf = .ext .datetime ∧ t = Term.some (bvsle (ext.datetime.val t₁) (ext.datetime.val t₂)))
  )
:= by show_compileApp₂_arith_op_ok_implies

theorem compileApp₂_add_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .add t₁ t₂ εs = .ok t →
  t₁.typeOf = .bitvec 64 ∧ t₂.typeOf = .bitvec 64 ∧ t = ifFalse (bvsaddo t₁ t₂) (bvadd t₁ t₂)
:= by show_compileApp₂_arith_op_ok_implies

theorem compileApp₂_sub_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .sub t₁ t₂ εs = .ok t →
  t₁.typeOf = .bitvec 64 ∧ t₂.typeOf = .bitvec 64 ∧ t = ifFalse (bvssubo t₁ t₂) (bvsub t₁ t₂)
:= by show_compileApp₂_arith_op_ok_implies

theorem compileApp₂_mul_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .mul t₁ t₂ εs = .ok t →
  t₁.typeOf = .bitvec 64 ∧ t₂.typeOf = .bitvec 64 ∧ t = ifFalse (bvsmulo t₁ t₂) (bvmul t₁ t₂)
:= by show_compileApp₂_arith_op_ok_implies

theorem reducibleEq_ok_false_implies {ty₁ ty₂ : TermType} :
  reducibleEq ty₁ ty₂ = Except.ok false →
  (¬ ty₁ = ty₂ ∧ ty₁.isPrimType ∧ ty₂.isPrimType)
:= by
  intro hok
  simp only [reducibleEq] at hok
  split at hok <;>
  simp only [Except.ok.injEq, Bool.and_eq_true, reduceCtorEq] at hok
  split at hok
  · rename_i h₁ h₂ ; simp only [h₁, not_false_eq_true, h₂, and_self]
  · contradiction

theorem reducibleEq_ok_true_implies {ty₁ ty₂ : TermType} :
  reducibleEq ty₁ ty₂ = .ok true → ty₁ = ty₂
:= by
  intro h
  unfold reducibleEq at h
  split at h
  · assumption
  · split at h <;> simp only [Except.ok.injEq, reduceCtorEq] at h

theorem compileApp₂_eq_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .eq t₁ t₂ εs = .ok t →
  ((reducibleEq t₁.typeOf t₂.typeOf = .ok true ∧ t = Term.some (eq t₁ t₂)) ∨
   (reducibleEq t₁.typeOf t₂.typeOf = .ok false ∧ t = Term.some false))
:= by
  intro h₁
  simp only [compileApp₂] at h₁
  simp_do_let (reducibleEq (Term.typeOf t₁) (Term.typeOf t₂)) at h₁
  rename_i b hty
  cases b
  all_goals {
    simp only [someOf, ite_true, ite_false, Except.ok.injEq, false_and, true_and, false_or, or_false, reduceCtorEq] at *
    rw [eq_comm, h₁]
  }

theorem compileApp₂_contains_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .contains t₁ t₂ εs = .ok t →
  t₁.typeOf = .set t₂.typeOf ∧ t = Term.some (set.member t₂ t₁)
:= by
  intro h₁
  simp only [compileApp₂] at h₁
  split at h₁ <;> simp only [reduceCtorEq] at *
  rename_i hty₁ _
  simp only [someOf, Except.ok.injEq] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
  rename_i hty₂
  simp only [hty₁, hty₂, h₁, and_self]

theorem compileApp₂_containsAll_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .containsAll t₁ t₂ εs = .ok t →
  ∃ ty, t₁.typeOf = .set ty ∧ t₂.typeOf = .set ty ∧ t = Term.some (set.subset t₂ t₁)
:= by
  intro h₁
  simp only [compileApp₂] at h₁
  split at h₁ <;> simp only [reduceCtorEq] at *
  rename_i ty₁ _ hty₁ hty₂ _
  simp only [someOf, Except.ok.injEq] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
  rename_i h ; subst h
  exists ty₁
  simp only [hty₁, hty₂, h₁, and_self]

theorem compileApp₂_containsAny_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .containsAny t₁ t₂ εs = .ok t →
  ∃ ty, t₁.typeOf = .set ty ∧ t₂.typeOf = .set ty ∧ t = Term.some (set.intersects t₁ t₂)
:= by
  intro h₁
  simp only [compileApp₂] at h₁
  split at h₁ <;> simp only [reduceCtorEq] at *
  rename_i ty₁ _ hty₁ hty₂ _
  simp only [someOf, Except.ok.injEq] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, reduceCtorEq] at h₁
  rename_i h ; subst h
  exists ty₁
  simp only [hty₁, hty₂, h₁, and_self]

theorem compileHasTag_ok_implies {t t₁ t₂ : Term} {tags : Option (Option SymTags)} :
  compileHasTag t₁ t₂ tags = .ok t →
  (tags = .some .none ∧ t = Term.some false) ∨
  (∃ τs, tags = .some (.some τs) ∧ t = Term.some (τs.hasTag t₁ t₂))
:= by
  intro h₁
  simp only [compileHasTag] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, someOf, reduceCtorEq] at h₁
  · simp_all only [and_self, Option.some.injEq, false_and, exists_const, or_false, reduceCtorEq]
  · simp_all only [Option.some.injEq, false_and, exists_eq_left', or_true]

theorem compileApp₂_hasTag_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .hasTag t₁ t₂ εs = .ok t →
  ∃ ety, t₁.typeOf = .entity ety ∧ t₂.typeOf = .string ∧ compileHasTag t₁ t₂ (εs.tags ety) = .ok t
:= by
  intro h₁
  simp only [compileApp₂] at h₁
  split at h₁ <;> simp only [reduceCtorEq] at *
  simp_all only [TermType.prim.injEq, TermPrimType.entity.injEq, true_and, exists_eq_left']

theorem compileGetTag_ok_implies {t t₁ t₂ : Term} {tags : Option (Option SymTags)} :
  compileGetTag t₁ t₂ tags = .ok t →
  ∃ τs, tags = .some (.some τs) ∧ t = τs.getTag t₁ t₂
:= by
  intro h₁
  simp only [compileGetTag] at h₁
  split at h₁ <;> simp only [Except.ok.injEq, Option.some.injEq, exists_eq_left', reduceCtorEq] at *
  simp only [h₁]

theorem compileApp₂_getTag_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .getTag t₁ t₂ εs = .ok t →
  ∃ ety, t₁.typeOf = .entity ety ∧ t₂.typeOf = .string ∧ compileGetTag t₁ t₂ (εs.tags ety) = .ok t
:= by
  intro h₁
  simp only [compileApp₂] at h₁
  split at h₁ <;> simp only [reduceCtorEq] at *
  simp_all only [TermType.prim.injEq, TermPrimType.entity.injEq, true_and, exists_eq_left']

def compileInₑ.isEq (t₁ t₂ : Term) : Term :=
  if t₁.typeOf = t₂.typeOf then eq t₁ t₂ else false

def compileInₑ.isIn (t₁ t₂ : Term) (ancs? : Option UnaryFunction) : Term :=
  match ancs? with
  | .some ancs => set.member t₂ (app ancs t₁)
  | .none      => false

theorem compileInₑ_def  {t₁ t₂ : Term} {ancs? : Option UnaryFunction} :
  compileInₑ t₁ t₂ ancs? = Factory.or (compileInₑ.isEq t₁ t₂) (compileInₑ.isIn t₁ t₂ ancs?)
:= by
  simp only [compileInₑ, compileInₑ.isEq, compileInₑ.isIn]
  cases ancs? <;> simp only

def compileInₛ.isIn₁ (t ts : Term) : Term :=
  if ts.typeOf = .set t.typeOf then set.member t ts else false

def compileInₛ.isIn₂ (t ts : Term) (ancs? : Option UnaryFunction) : Term :=
  match ancs? with
  | .some ancs => set.intersects ts (app ancs t)
  | .none      => false

theorem compileInₛ_def  {t ts : Term} {ancs? : Option UnaryFunction} :
  compileInₛ t ts ancs? = Factory.or (compileInₛ.isIn₁ t ts) (compileInₛ.isIn₂ t ts ancs?)
:= by
  simp only [compileInₛ, compileInₛ.isIn₁, compileInₛ.isIn₂]
  cases ancs? <;> simp only

theorem compileApp₂_mem_ok_implies {t t₁ t₂ : Term} {εs : SymEntities} :
  compileApp₂ .mem t₁ t₂ εs = .ok t →
  ∃ ety₁ ety₂, t₁.typeOf = .entity ety₁ ∧
    ((t₂.typeOf = .entity ety₂ ∧ t = Term.some (compileInₑ t₁ t₂ (εs.ancestorsOfType ety₁ ety₂))) ∨
     (t₂.typeOf = .set (.entity ety₂) ∧ t = Term.some (compileInₛ t₁ t₂ (εs.ancestorsOfType ety₁ ety₂))))
:= by
  intro h₁
  simp only [compileApp₂] at h₁
  split at h₁ <;> simp only [reduceCtorEq] at *
  all_goals {
    rename_i ety₁ ety₂ hty₁ hty₂ _
    simp only [someOf, Except.ok.injEq] at h₁
    exists ety₁, ety₂
    simp only [hty₁, hty₂, h₁, and_self, false_and, or_false, or_true, reduceCtorEq]
  }

theorem compile_binaryApp_ok_implies {op₂ : BinaryOp} {x₁ x₂ : Expr} {εnv : SymEnv} {t : Term}
  (hok : compile (.binaryApp op₂ x₁ x₂) εnv = .ok t) :
  ∃ t₁ t₂ t₃,
    (compile x₁ εnv) = .ok t₁ ∧
    (compile x₂ εnv) = .ok t₂ ∧
    (compileApp₂ op₂ (option.get t₁) (option.get t₂) εnv.entities) = .ok t₃ ∧
    t = ifSome t₁ (ifSome t₂ t₃)
:= by
  simp only [compile] at hok
  simp_do_let (compile x₁ εnv) at hok
  simp_do_let (compile x₂ εnv) at hok
  rename_i t₁ h₁ t₂ h₂
  simp_do_let (compileApp₂ op₂ (option.get t₁) (option.get t₂) εnv.entities) at hok
  rename_i t₃ h₃
  simp only [Except.ok.injEq] at h₃ hok
  exists t₁, t₂, t₃
  simp only [h₃, hok, and_self]

theorem compileSet_ok_implies {ts : List Term} {t : Term}
  (hok : compileSet ts = .ok t) :
  ∃ ty hd tl,
    ts = hd :: tl ∧
    (∀ t ∈ ts, t.typeOf = .option ty) ∧
    t = ifAllSome ts (Term.some (setOf (ts.map option.get) ty))
:= by
  simp only [compileSet, List.all_eq_true, decide_eq_true_eq] at hok
  split at hok <;> simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, reduceCtorEq] at hok
  simp only [ne_eq, not_false_eq_true, List.mem_cons, forall_eq_or_imp, true_and]
  split at hok <;> try (simp only [reduceCtorEq] at hok)
  rename_i hd tl _ ty _
  split at hok <;> simp only [Except.ok.injEq, someOf, reduceCtorEq] at hok
  rename_i heq
  exists ty, hd, tl
  simp only [not_false_eq_true, List.mem_cons, forall_eq_or_imp, heq.left, true_and, List.map_cons,
    hok, and_true]
  exact heq.right

theorem compile_set_ok_implies {xs : List Expr} {εnv : SymEnv} {t : Term}
  (hok : compile (.set xs) εnv = .ok t) :
  ∃ ts,
    List.Forall₂ (λ x t => (compile x εnv) = .ok t) xs ts ∧
    compileSet ts = .ok t
:= by
  simp only [compile] at hok
  simp_do_let (List.mapM₁ xs fun x => compile x.val εnv) at hok
  rename_i ts hm
  simp only [List.mapM₁_eq_mapM (fun x => compile x εnv), ← List.mapM'_eq_mapM] at hm
  rw [List.mapM'_ok_iff_forall₂] at hm
  exists ts

theorem compile_record_ok_implies {axs : List (Attr × Expr)} {εnv : SymEnv} {t : Term}
  (hok : compile (.record axs) εnv = .ok t) :
  ∃ ats,
    List.Forall₂ (λ px pt => px.fst = pt.fst ∧ compile px.snd εnv = .ok pt.snd) axs ats ∧
    t = compileRecord ats
:= by
  simp only [compile] at hok
  simp_do_let (axs.mapM₂ (λ ⟨(a₁, x₁), _⟩ => do .ok (a₁, ← compile x₁ εnv))) at hok
  rename_i ats hts
  simp only [List.mapM₂, List.attach₂,
    List.mapM_pmap_subtype λ (p : Attr × Expr) => do
      .ok (p.fst, ← compile p.snd εnv),
    List.mapM_ok_iff_forall₂] at hts
  simp only [Except.ok.injEq] at hok
  exists ats
  simp only [hok, and_true]
  apply List.Forall₂.imp _ hts
  intro px pt hp
  simp_do_let (compile px.snd εnv) at hp
  rename_i t' hr
  simp only [Except.ok.injEq] at hp
  simp only [← hp, and_self]

theorem compile_record_val_ok_implies {axs : Map Attr Value} {εs : SymEntities} {t : Term}
  (hok : compileVal (.record axs) εs = .ok t) :
  ∃ ats,
    List.Forall₂ (λ px pt => px.fst = pt.fst ∧ compileVal px.snd εs = .ok pt.snd) axs.kvs ats ∧
    t = compileRecord ats
:= by
  sorry

local macro "simp_compileCall₀" : tactic => do
 `(tactic| (
    intro hok
    unfold compileCall at hok
    split at hok <;> simp only [List.cons.injEq, and_true, exists_and_left, reduceCtorEq] at *
    rename_i t₀ _
    unfold compileCall₀ at hok
    split at hok <;> try simp only [reduceCtorEq] at hok
    rename_i s
    split at hok <;> simp only [Except.ok.injEq, reduceCtorEq] at hok
    rename_i ext heq
    exists s
    simp only [true_and]
    exists ext
    simp only [heq, true_and]
    simp only [someOf, Coe.coe] at hok
    simp only [hok]
  ))

local macro "simp_compileCall₂" : tactic => do
 `(tactic| (
    intro hok
    unfold compileCall at hok
    split at hok <;> simp only [List.cons.injEq, and_true, exists_and_left, reduceCtorEq] at *
    rename_i t₁ t₂ _
    exists t₁, t₂
    simp only [and_self, true_and]
    simp only [compileCall₂, compileCallWithError₂, Bool.and_eq_true, decide_eq_true_eq] at hok
    split at hok <;> simp only [someOf, Except.ok.injEq, reduceCtorEq] at hok
    rename_i hty
    simp only [hty, hok, and_self]
  ))

local macro "simp_compileCall₁" : tactic => do
 `(tactic| (
    intro hok
    unfold compileCall at hok
    split at hok <;>
    simp only [List.cons.injEq, and_true, exists_eq_left', false_implies, forall_const, reduceCtorEq] at *
    rename_i t₁ _
    simp only [compileCall₁, compileCallWithError₁] at hok
    split at hok <;> simp only [Except.ok.injEq, someOf, reduceCtorEq] at hok
    rename_i hty
    simp only [hty, hok, and_self]
  ))

theorem compileCall_decimal_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.decimal ts = .ok t →
  ∃ (s : String) (d : Ext.Decimal),
    ts = [.some (.prim (.string s))] ∧
    Ext.Decimal.decimal s = .some d ∧
    t = Term.some (.prim (.ext (.decimal d)))
:= by simp_compileCall₀

theorem compileCall_decimal_lessThan_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.lessThan ts = .ok t →
  ∃ t₁ t₂,
    ts = [t₁, t₂] ∧
    t₁.typeOf = .option (.ext .decimal) ∧
    t₂.typeOf = .option (.ext .decimal) ∧
    t = ifSome t₁ (ifSome t₂ (Term.some (Decimal.lessThan (option.get t₁) (option.get t₂))))
:= by simp_compileCall₂

theorem compileCall_decimal_lessThanOrEqual_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.lessThanOrEqual ts = .ok t →
  ∃ t₁ t₂,
    ts = [t₁, t₂] ∧
    t₁.typeOf = .option (.ext .decimal) ∧
    t₂.typeOf = .option (.ext .decimal) ∧
    t = ifSome t₁ (ifSome t₂ (Term.some (Decimal.lessThanOrEqual (option.get t₁) (option.get t₂))))
:= by simp_compileCall₂

theorem compileCall_decimal_greaterThan_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.greaterThan ts = .ok t →
  ∃ t₁ t₂,
    ts = [t₁, t₂] ∧
    t₁.typeOf = .option (.ext .decimal) ∧
    t₂.typeOf = .option (.ext .decimal) ∧
    t = ifSome t₁ (ifSome t₂ (Term.some (Decimal.greaterThan (option.get t₁) (option.get t₂))))
:= by simp_compileCall₂

theorem compileCall_decimal_greaterThanOrEqual_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.greaterThanOrEqual ts = .ok t →
  ∃ t₁ t₂,
    ts = [t₁, t₂] ∧
    t₁.typeOf = .option (.ext .decimal) ∧
    t₂.typeOf = .option (.ext .decimal) ∧
    t = ifSome t₁ (ifSome t₂ (Term.some (Decimal.greaterThanOrEqual (option.get t₁) (option.get t₂))))
:= by simp_compileCall₂

theorem compileCall_ipAddr_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.ip ts = .ok t →
  ∃ (s : String) (ip : Ext.IPAddr.IPNet),
    ts = [.some (.prim (.string s))] ∧
    Ext.IPAddr.ip s = .some ip ∧
    t = Term.some (.prim (.ext (.ipaddr ip)))
:= by simp_compileCall₀

theorem compileCall_ipAddr_isIpv4_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.isIpv4 ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .ipAddr) ∧
    t = ifSome t₁ (Term.some (IPAddr.isIpv4 (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_ipAddr_isIpv6_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.isIpv6 ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .ipAddr) ∧
    t = ifSome t₁ (Term.some (IPAddr.isIpv6 (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_ipAddr_isLoopback_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.isLoopback ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .ipAddr) ∧
    t = ifSome t₁ (Term.some (IPAddr.isLoopback (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_ipAddr_isMulticast_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.isMulticast ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .ipAddr) ∧
    t = ifSome t₁ (Term.some (IPAddr.isMulticast (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_ipAddr_isInRange_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.isInRange ts = .ok t →
  ∃ t₁ t₂,
    ts = [t₁, t₂] ∧
    t₁.typeOf = .option (.ext .ipAddr) ∧
    t₂.typeOf = .option (.ext .ipAddr) ∧
    t = ifSome t₁ (ifSome t₂ (Term.some (IPAddr.isInRange (option.get t₁) (option.get t₂))))
:= by simp_compileCall₂

theorem compileCall_datetime_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.datetime ts = .ok t →
  ∃ (s : String) (d : Ext.Datetime),
    ts = [.some (.prim (.string s))] ∧
    Ext.Datetime.datetime s = .some d ∧
    t = Term.some (.prim (.ext (.datetime d)))
:= by simp_compileCall₀

theorem compileCall_datetime_offset_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.offset ts = .ok t →
  ∃ t₁ t₂,
    ts = [t₁, t₂] ∧
    t₁.typeOf = .option (.ext .datetime) ∧
    t₂.typeOf = .option (.ext .duration) ∧
    t = ifSome t₁ (ifSome t₂ (Datetime.offset (option.get t₁) (option.get t₂)))
:= by simp_compileCall₂

theorem compileCall_datetime_durationSince_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.durationSince ts = .ok t →
  ∃ t₁ t₂,
    ts = [t₁, t₂] ∧
    t₁.typeOf = .option (.ext .datetime) ∧
    t₂.typeOf = .option (.ext .datetime) ∧
    t = ifSome t₁ (ifSome t₂ (Datetime.durationSince (option.get t₁) (option.get t₂)))
:= by simp_compileCall₂

theorem compileCall_datetime_toDate_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.toDate ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .datetime) ∧
    t = ifSome t₁ (Datetime.toDate (option.get t₁))
:= by simp_compileCall₁

theorem compileCall_datetime_toTime_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.toTime ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .datetime) ∧
    t = ifSome t₁ (Term.some (Datetime.toTime (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_duration_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.duration ts = .ok t →
  ∃ (s : String) (d : Ext.Datetime.Duration),
    ts = [.some (.prim (.string s))] ∧
    Ext.Datetime.duration s = .some d ∧
    t = Term.some (.prim (.ext (.duration d)))
:= by simp_compileCall₀

theorem compileCall_duration_toMilliseconds_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.toMilliseconds ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .duration) ∧
    t = ifSome t₁ (Term.some (Duration.toMilliseconds (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_duration_toSeconds_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.toSeconds ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .duration) ∧
    t = ifSome t₁ (Term.some (Duration.toSeconds (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_duration_toMinutes_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.toMinutes ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .duration) ∧
    t = ifSome t₁ (Term.some (Duration.toMinutes (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_duration_toHours_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.toHours ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .duration) ∧
    t = ifSome t₁ (Term.some (Duration.toHours (option.get t₁)))
:= by simp_compileCall₁

theorem compileCall_duration_toDays_ok_implies {ts : List Term} {t : Term} :
  compileCall ExtFun.toDays ts = .ok t →
  ∃ t₁,
    ts = [t₁] ∧
    t₁.typeOf = .option (.ext .duration) ∧
    t = ifSome t₁ (Term.some (Duration.toDays (option.get t₁)))
:= by simp_compileCall₁

theorem compile_call_ok_implies {f : ExtFun} {xs : List Expr} {εnv : SymEnv} {t : Term}
  (hok : compile (.call f xs) εnv = .ok t) :
  ∃ ts,
    List.Forall₂ (λ x t => (compile x εnv) = .ok t) xs ts ∧
    compileCall f ts = .ok t
:= by
  simp only [compile] at hok
  simp_do_let (List.mapM₁ xs fun x => compile x.val εnv) at hok
  rename_i ts hm
  simp only [List.mapM₁_eq_mapM (fun x => compile x εnv), ← List.mapM'_eq_mapM] at hm
  rw [List.mapM'_ok_iff_forall₂] at hm
  exists ts

end Cedar.Thm
