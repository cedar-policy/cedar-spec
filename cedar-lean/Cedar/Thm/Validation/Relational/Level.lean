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

module

public import Cedar.Thm.Validation.Relational.Policy
public import Cedar.Validation.Relational.Level
import Batteries.Data.List.Lemmas
import all Cedar.Data.List -- unfolds `attach₂`
import all Cedar.Data.Map -- unfolds `find`, `keys`, `make`, …
import all Cedar.Data.Set -- unfolds `all`, `any`, `make`, …
import all Cedar.Spec.Policy -- unfolds `Policies`, `toExpr`
import all Cedar.Spec.Value -- unfolds `Attr`
import all Cedar.Validation.EnvironmentValidator -- unfolds `validateWellFormed`
import all Cedar.Validation.Levels -- unfolds `checkEntityAccessLevel`, `checkLevel`, `extHasAttrFirstEntityPath`
import all Cedar.Validation.Typechecker -- unfolds `Capabilities`, `ResultType`, `entityUID`, …
import all Cedar.Validation.TypedExpr -- unfolds `toExpr`, `typeOf`
import all Cedar.Validation.Types -- unfolds `map`, `not`, `schema`
import all Cedar.Validation.Validator -- unfolds `allFalse`, `checkEntities`, `environment`, …

/-! # `ValidPolicyAtLevel` characterizes `validateWithLevel` -/

@[expose] public section

namespace Cedar.Validation.Relational

open Cedar.Spec
open Cedar.Data
open Cedar.Validation

/-! ## `HasType` premises and `typeOf` -/

/-- A `HasType` derivation under capabilities equivalent to `c` determines the type `typeOf`
    gives under `c`, and the capabilities it earns up to equivalence. -/
theorem hasType_det {decl syn : Bool} {env : TypeEnv} (hwf : EnvAssumptions env) {x : Expr}
    {c₀ c : Capabilities} {ty : CedarType} {ca : Capabilities} {tx : TypedExpr} {c₁ : Capabilities}
    (hHT : HasType decl syn x c₀ env ty ca) (hc : CapsEquiv c₀ c) (h : typeOf x c env = .ok (tx, c₁)) :
    tx.typeOf = ty ∧ CapsEquiv ca c₁ := by
  obtain ⟨tx', c₁', h', hty, hca⟩ := hasType_sound hwf hHT
  obtain ⟨o, ho, hco⟩ := typeOf_capsEquiv hc h'
  rw [h] at ho
  simp only [Except.ok.injEq, Prod.mk.injEq] at ho
  obtain ⟨rfl, rfl⟩ := ho
  exact ⟨hty, hca.trans hco⟩

/-- A typed subexpression has a `HasType` derivation under any equivalent capabilities. -/
theorem hasType_of_typeOf {env : TypeEnv} (hwf : EnvAssumptions env) {x : Expr}
    {c₀ c : Capabilities} {tx : TypedExpr} {c₁ : Capabilities}
    (h : typeOf x c env = .ok (tx, c₁)) (hc : CapsEquiv c₀ c) :
    ∃ ca, HasType false false x c₀ env tx.typeOf ca ∧ CapsEquiv ca c₁ := by
  obtain ⟨o, ho, hco⟩ := typeOf_capsEquiv hc.symm h
  obtain ⟨cout, hHT, hce⟩ := typeOf_complete hwf ho
  exact ⟨cout, hHT, hce.trans hco.symm⟩

theorem capMerge_capsEquiv {c₀ c ca c₁ cca : Capabilities} (hm : CapMerge c₀ ca cca)
    (hc : CapsEquiv c₀ c) (hca : CapsEquiv ca c₁) : CapsEquiv cca (c ∪ c₁) :=
  (capMerge_capsEquiv_union hm).trans (CapsEquiv.union hc hca)

/-! ## Shapes of typed expressions -/

private theorem typeOfLit_shape {p : Prim} {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (h : typeOfLit p env = .ok (tx, c')) : ∃ ty, tx = .lit p ty := by
  simp only [typeOfLit] at h
  split at h <;> (try split at h) <;>
    simp only [ok, err, Function.comp, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    exact ⟨_, h.1.symm⟩

private theorem typeOfVar_shape {v : Var} {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (h : typeOfVar v env = .ok (tx, c')) : ∃ ty, tx = .var v ty := by
  simp only [typeOfVar] at h
  split at h <;> simp only [ok, Function.comp, Except.ok.injEq, Prod.mk.injEq] at h <;>
    exact ⟨_, h.1.symm⟩

private theorem typeOfIf_shape {tx₁ : TypedExpr} {c₁ : Capabilities} {r₂ r₃ : ResultType}
    {tx : TypedExpr} {c' : Capabilities} (h : typeOfIf (tx₁, c₁) r₂ r₃ = .ok (tx, c')) :
    (tx₁.typeOf = .bool .tt ∧ ∃ tx₂ c₂, r₂ = .ok (tx₂, c₂) ∧ tx = .ite tx₁ tx₂ tx₂ tx₂.typeOf) ∨
    (tx₁.typeOf = .bool .ff ∧ ∃ tx₃ c₃, r₃ = .ok (tx₃, c₃) ∧ tx = .ite tx₁ tx₃ tx₃ tx₃.typeOf) ∨
    (tx₁.typeOf = .bool .anyBool ∧ ∃ tx₂ c₂ tx₃ c₃ ty, r₂ = .ok (tx₂, c₂) ∧ r₃ = .ok (tx₃, c₃) ∧
      tx = .ite tx₁ tx₂ tx₃ ty) := by
  simp only [typeOfIf] at h
  split at h
  · rename_i heq
    cases r₂ with
    | error => simp at h
    | ok r => obtain ⟨tx₂, c₂⟩ := r; simp only [Except.bind_ok, ok, Except.ok.injEq,
        Prod.mk.injEq] at h; exact .inl ⟨heq, tx₂, c₂, rfl, h.1.symm⟩
  · rename_i heq
    cases r₃ with
    | error => simp at h
    | ok r => obtain ⟨tx₃, c₃⟩ := r; simp only [Except.bind_ok, ok, Except.ok.injEq,
        Prod.mk.injEq] at h; exact .inr (.inl ⟨heq, tx₃, c₃, rfl, h.1.symm⟩)
  · rename_i heq
    cases r₂ with
    | error => simp at h
    | ok r =>
      obtain ⟨tx₂, c₂⟩ := r
      cases r₃ with
      | error => simp at h
      | ok r =>
        obtain ⟨tx₃, c₃⟩ := r
        simp only [Except.bind_ok] at h
        split at h
        · rename_i ty _
          simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
          exact .inr (.inr ⟨heq, tx₂, c₂, tx₃, c₃, ty, rfl, rfl, h.1.symm⟩)
        · simp [err] at h
  · simp [err] at h

private theorem typeOfAnd_shape {tx₁ : TypedExpr} {c₁ : Capabilities} {r₂ : ResultType}
    {tx : TypedExpr} {c' : Capabilities} (h : typeOfAnd (tx₁, c₁) r₂ = .ok (tx, c')) :
    (tx₁.typeOf = .bool .ff ∧ tx = tx₁) ∨
    (∃ b₁, tx₁.typeOf = .bool b₁ ∧ b₁ ≠ .ff ∧
      ∃ tx₂ c₂ ty, r₂ = .ok (tx₂, c₂) ∧ tx = .and tx₁ tx₂ ty) := by
  simp only [typeOfAnd] at h
  split at h
  · rename_i heq
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact .inl ⟨heq, h.1.symm⟩
  · rename_i b₁ hne heq
    cases r₂ with
    | error => simp at h
    | ok r =>
      obtain ⟨tx₂, c₂⟩ := r
      simp only [Except.bind_ok] at h
      refine .inr ⟨b₁, heq, fun h' => hne h', tx₂, c₂, ?_⟩
      split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
        exact ⟨_, rfl, h.1.symm⟩
  · simp [err] at h

private theorem typeOfOr_shape {tx₁ : TypedExpr} {c₁ : Capabilities} {r₂ : ResultType}
    {tx : TypedExpr} {c' : Capabilities} (h : typeOfOr (tx₁, c₁) r₂ = .ok (tx, c')) :
    (tx₁.typeOf = .bool .tt ∧ tx = tx₁) ∨
    (∃ b₁, tx₁.typeOf = .bool b₁ ∧ b₁ ≠ .tt ∧
      ∃ tx₂ c₂ ty, r₂ = .ok (tx₂, c₂) ∧ tx = .or tx₁ tx₂ ty) := by
  simp only [typeOfOr] at h
  split at h
  · rename_i heq
    simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
    exact .inl ⟨heq, h.1.symm⟩
  · rename_i heq
    cases r₂ with
    | error => simp at h
    | ok r =>
      obtain ⟨tx₂, c₂⟩ := r
      simp only [Except.bind_ok] at h
      refine .inr ⟨.ff, heq, by simp, tx₂, c₂, ?_⟩
      split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
      exact ⟨_, rfl, h.1.symm⟩
  · rename_i b₁ hne _ heq
    cases r₂ with
    | error => simp at h
    | ok r =>
      obtain ⟨tx₂, c₂⟩ := r
      simp only [Except.bind_ok] at h
      refine .inr ⟨b₁, heq, fun h' => hne h', tx₂, c₂, ?_⟩
      split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
        exact ⟨_, rfl, h.1.symm⟩
  · simp [err] at h

private theorem typeOfUnaryApp_shape {op : UnaryOp} {tx₁ tx : TypedExpr} {c' : Capabilities}
    (h : typeOfUnaryApp op tx₁ = .ok (tx, c')) : ∃ ty, tx = .unaryApp op tx₁ ty := by
  simp only [typeOfUnaryApp] at h
  split at h <;> simp only [ok, err, Function.comp, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    exact ⟨_, h.1.symm⟩

private theorem typeOfBinaryApp_shape {op : BinaryOp} {tx₁ tx₂ : TypedExpr} {x₁ x₂ : Expr}
    {c : Capabilities} {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (h : typeOfBinaryApp op tx₁ tx₂ x₁ x₂ c env = .ok (tx, c')) :
    ∃ ty, tx = .binaryApp op tx₁ tx₂ ty := by
  simp only [typeOfBinaryApp] at h
  split at h <;>
    simp only [typeOfEq, ifLubThenBool, typeOfHasTag, typeOfGetTag, ok, err, Function.comp,
      bind, Except.bind] at h <;>
    (repeat' split at h) <;>
    simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    exact ⟨_, h.1.symm⟩

private theorem typeOfHasAttr_shape {tx₁ : TypedExpr} {x : Expr} {a : Attr} {c : Capabilities}
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (h : typeOfHasAttr tx₁ x a c env = .ok (tx, c')) :
    ∃ ty, tx = .hasAttr tx₁ a ty ∧
      ((∃ ety, tx₁.typeOf = .entity ety) ∨ (∃ rty, tx₁.typeOf = .record rty)) := by
  simp only [typeOfHasAttr] at h
  split at h
  · rename_i rty heq
    cases hr : hasAttrInRecord rty x a c true with
    | error => rw [hr] at h; simp at h
    | ok r => rw [hr] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨_, h.1.symm, .inr ⟨rty, heq⟩⟩
  · rename_i ety heq
    split at h
    · rename_i rty _
      cases hr : hasAttrInRecord rty x a c false with
      | error => rw [hr] at h; simp at h
      | ok r => rw [hr] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
                exact ⟨_, h.1.symm, .inl ⟨ety, heq⟩⟩
    · split at h
      · simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨_, h.1.symm, .inl ⟨ety, heq⟩⟩
      · simp [err] at h
  · simp [err] at h

private theorem typeOfGetAttr_shape {tx₁ : TypedExpr} {x : Expr} {a : Attr} {c : Capabilities}
    {env : TypeEnv} {tx : TypedExpr} {c' : Capabilities}
    (h : typeOfGetAttr tx₁ x a c env = .ok (tx, c')) :
    ∃ ty, tx = .getAttr tx₁ a ty ∧
      ((∃ ety, tx₁.typeOf = .entity ety) ∨ (∃ rty, tx₁.typeOf = .record rty)) := by
  simp only [typeOfGetAttr] at h
  split at h
  · rename_i rty heq
    cases hr : getAttrInRecord tx₁.typeOf rty x a c with
    | error => rw [hr] at h; simp at h
    | ok r => rw [hr] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
              exact ⟨_, h.1.symm, .inr ⟨rty, heq⟩⟩
  · rename_i ety heq
    split at h
    · rename_i rty _
      cases hr : getAttrInRecord tx₁.typeOf rty x a c with
      | error => rw [hr] at h; simp at h
      | ok r => rw [hr] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
                exact ⟨_, h.1.symm, .inl ⟨ety, heq⟩⟩
    · simp [err] at h
  · simp [err] at h

private theorem typeOfExtHasAttr_receiver {tx₁ : TypedExpr} {x : Expr} {a : Attr} {as' : List Attr}
    {c : Capabilities} {env : TypeEnv} {r : BoolType × Capabilities}
    (h : typeOfExtHasAttr tx₁ x (a :: as') c env = .ok r) :
    (∃ ety, tx₁.typeOf = .entity ety) ∨ (∃ rty, tx₁.typeOf = .record rty) := by
  have hha : ∃ r', typeOfHasAttr tx₁ x a c env = .ok r' := by
    cases as' with
    | nil =>
      simp only [typeOfExtHasAttr] at h
      cases hh : typeOfHasAttr tx₁ x a c env with
      | error => rw [hh] at h; simp at h
      | ok r' => exact ⟨r', rfl⟩
    | cons _ _ =>
      simp only [typeOfExtHasAttr] at h
      cases hh : typeOfHasAttr tx₁ x a c env with
      | error => rw [hh] at h; simp at h
      | ok r' => exact ⟨r', rfl⟩
  obtain ⟨⟨tx', c'⟩, hh⟩ := hha
  obtain ⟨_, _, hr⟩ := typeOfHasAttr_shape hh
  exact hr

private theorem typeOfSet_shape {tys : List TypedExpr} {tx : TypedExpr} {c' : Capabilities}
    (h : typeOfSet tys = .ok (tx, c')) : ∃ ty, tx = .set tys ty := by
  simp only [typeOfSet] at h
  split at h
  · simp [err] at h
  · split at h <;> simp only [ok, err, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h
    exact ⟨_, h.1.symm⟩

private theorem typeOfCall_shape {xfn : ExtFun} {tys : List TypedExpr} {xs : List Expr}
    {tx : TypedExpr} {c' : Capabilities} (h : typeOfCall xfn tys xs = .ok (tx, c')) :
    ∃ ty, tx = .call xfn tys ty := by
  simp only [typeOfCall] at h
  split at h <;>
    simp only [typeOfConstructor, typeOfIsInRange, ok, err, bind, Except.bind] at h <;>
    (repeat' split at h) <;>
    simp only [Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    exact ⟨_, h.1.symm⟩

/-! ## Lists and records -/

private theorem mapM_justType_forall₂ {c : Capabilities} {env : TypeEnv} {P : Expr → TypedExpr → Prop} :
    ∀ {xs : List Expr} {tys : List TypedExpr},
      xs.mapM (fun x => justType (typeOf x c env)) = .ok tys →
      (∀ x ∈ xs, ∀ {tx c'}, typeOf x c env = .ok (tx, c') → P x tx) → List.Forall₂ P xs tys
  | [], tys, h, _ => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact .nil
  | x :: xs, tys, h, hP => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i tx hx
      split at h
      · simp at h
      · rename_i tys' hxs
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [justType, Except.map] at hx
        split at hx
        · simp at hx
        · rename_i r hr
          simp only [Except.ok.injEq] at hx; subst hx
          exact .cons (hP x (List.mem_cons_self ..) hr)
            (mapM_justType_forall₂ hxs fun y hy => hP y (List.mem_cons_of_mem _ hy))

private theorem mapM_record_forall₂ {c : Capabilities} {env : TypeEnv} {P : Expr → TypedExpr → Prop} :
    ∀ {axs : List (Attr × Expr)} {atys : List (Attr × TypedExpr)},
      axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) = .ok atys →
      (∀ ax ∈ axs, ∀ {tx c'}, typeOf ax.2 c env = .ok (tx, c') → P ax.2 tx) →
      List.Forall₂ (fun ax atx => atx.1 = ax.1 ∧ P ax.2 atx.2) axs atys
  | [], atys, h, _ => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact .nil
  | ax :: axs, atys, h, hP => by
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i atx hx
      split at h
      · simp at h
      · rename_i atys' hxs
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        simp only [Except.map] at hx
        split at hx
        · simp at hx
        · rename_i r hr
          simp only [Except.ok.injEq] at hx; subst hx
          exact .cons ⟨rfl, hP ax (List.mem_cons_self ..) hr⟩
            (mapM_record_forall₂ hxs fun y hy => hP y (List.mem_cons_of_mem _ hy))

private theorem attach_all_val {α : Type} (l : List α) (f : α → Bool) :
    (l.attach.all fun e => f e.val) = l.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  simp only [List.mem_attach, true_implies, Subtype.forall]

private theorem attach₂_all_val {α β : Type} [SizeOf α] [SizeOf β] (l : List (α × β))
    (f : α × β → Bool) : (l.attach₂.all fun e => f e.val) = l.all f := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor
  · intro h p hp
    exact h _ (by simp only [List.attach₂, List.mem_pmap]; exact ⟨p, hp, rfl⟩)
  · intro h x hx
    exact h x.val (List.mem_attach₂ hx)

/-! ## Level checks of typed lists and records -/

/-- `LevelOk` and `EntityAccessOk` on `x` agree with the level checks on the typed
    expression `tx`. -/
def LevelIff (x : Expr) (c : Capabilities) (env : TypeEnv) (tx : TypedExpr) : Prop :=
  (∀ n, LevelOk x c env n ↔ tx.checkLevel env n = true) ∧
  ∀ n nmax path, EntityAccessOk x c env n nmax path ↔
    tx.checkEntityAccessLevel env n nmax path = true

theorem levelOkList_iff {c : Capabilities} {env : TypeEnv} {n : Nat} :
    ∀ {xs : List Expr} {tys : List TypedExpr}, List.Forall₂ (fun x tx => LevelIff x c env tx) xs tys →
      (LevelOkList xs c env n ↔ ∀ tx ∈ tys, tx.checkLevel env n = true)
  | [], [], .nil => ⟨fun _ => by simp, fun _ => .nil _ _ _⟩
  | x :: xs, tx :: tys, .cons hx hxs => by
    rw [List.forall_mem_cons, ← levelOkList_iff hxs, ← hx.1 n]
    constructor
    · intro h; cases h with | cons _ _ _ _ _ h hs => exact ⟨h, hs⟩
    · rintro ⟨h, hs⟩; exact .cons _ _ _ _ _ h hs

theorem levelOkRecord_iff {c : Capabilities} {env : TypeEnv} {n : Nat} :
    ∀ {axs : List (Attr × Expr)} {atys : List (Attr × TypedExpr)},
      List.Forall₂ (fun ax atx => atx.1 = ax.1 ∧ LevelIff ax.2 c env atx.2) axs atys →
      (LevelOkRecord axs c env n ↔ ∀ p ∈ atys, p.2.checkLevel env n = true)
  | [], [], .nil => ⟨fun _ => by simp, fun _ => .nil _ _ _⟩
  | (a, x) :: axs, (a', tx) :: atys, .cons hx hxs => by
    rw [List.forall_mem_cons, ← levelOkRecord_iff hxs, ← hx.2.1 n]
    constructor
    · intro h; cases h with | cons _ _ _ _ _ _ h hs => exact ⟨h, hs⟩
    · rintro ⟨h, hs⟩; exact .cons _ _ _ _ _ _ h hs

/-- `Map.make` keeps the first of duplicate keys, so its lookups are those of the unsorted
    list. -/
private theorem make_find?_eq_mk_find? {l : List (Attr × TypedExpr)} {k : Attr} :
    (Map.make l).find? k = (Map.mk l).find? k := by
  rw [Map.make_find?_eq_list_find?]
  simp only [Map.find?, Map.toList_mk_id]
  cases List.find? (fun x => x.fst == k) l with
  | none => rfl
  | some p => rfl

theorem recordFieldFind_find? {S : Expr → TypedExpr → Prop} {k : Attr} {x : Expr}
    {axs : List (Attr × Expr)} {atys : List (Attr × TypedExpr)}
    (h : List.Forall₂ (fun ax atx => atx.1 = ax.1 ∧ S ax.2 atx.2) axs atys)
    (hr : RecordFieldFind k x axs) : ∃ tx, (Map.mk atys).find? k = some tx ∧ S x tx := by
  induction hr generalizing atys with
  | here axs =>
    cases h with
    | @cons _ atx _ _ hx _ =>
      obtain ⟨a', tx⟩ := atx
      obtain ⟨ha, hS⟩ := hx
      simp only at ha; subst ha
      exact ⟨tx, by simp [Map.find?, Map.toList], hS⟩
  | there a' x' axs hne _ ih =>
    cases h with
    | @cons _ atx _ _ hx hxs =>
      obtain ⟨a'', tx⟩ := atx
      obtain ⟨ha, _⟩ := hx
      simp only at ha; subst ha
      obtain ⟨tx', hfind, hS⟩ := ih hxs
      refine ⟨tx', ?_, hS⟩
      have : (a'' == k) = false := by simp only [beq_eq_false_iff_ne]; exact fun h => hne h.symm
      simp only [Map.find?, Map.toList, List.find?_cons, this] at hfind ⊢
      exact hfind

theorem find?_recordFieldFind {S : Expr → TypedExpr → Prop} {k : Attr} {tx : TypedExpr} :
    ∀ {axs : List (Attr × Expr)} {atys : List (Attr × TypedExpr)},
      List.Forall₂ (fun ax atx => atx.1 = ax.1 ∧ S ax.2 atx.2) axs atys →
      (Map.mk atys).find? k = some tx → ∃ x, RecordFieldFind k x axs ∧ S x tx
  | [], [], .nil, h => by simp [Map.find?, Map.toList] at h
  | (a, x) :: axs, (a', tx') :: atys, .cons ⟨ha, hS⟩ hxs, h => by
    simp only at ha; subst ha
    by_cases hk : a' = k
    · subst hk
      simp only [Map.find?, Map.toList, List.find?_cons, beq_self_eq_true, Option.some.injEq] at h
      subst h
      exact ⟨x, .here _ _ _, hS⟩
    · have : (a' == k) = false := by simp only [beq_eq_false_iff_ne]; exact hk
      have h' : (Map.mk atys).find? k = some tx := by
        simp only [Map.find?, Map.toList, List.find?_cons, this] at h ⊢; exact h
      obtain ⟨x', hf, hS'⟩ := find?_recordFieldFind hxs h'
      exact ⟨x', .there _ _ _ _ _ (fun h => hk h.symm) hf, hS'⟩

theorem notTt_iff {b : BoolType} : NotTt b ↔ b ≠ .tt := by
  constructor
  · intro h; cases h <;> simp
  · intro h
    cases b with
    | tt => exact absurd rfl h
    | ff => exact .ff
    | anyBool => exact .anyBool

/-! ## The level checks of a typed expression -/

/-- Two `HasType` derivations of one subexpression under equivalent capabilities agree with
    the `typeOf` result on its Boolean type. -/
theorem hasType_bool_eq {decl syn : Bool} {env : TypeEnv} (hwf : EnvAssumptions env) {x : Expr}
    {c₀ c : Capabilities} {b : BoolType} {ca : Capabilities} {tx : TypedExpr} {c₁ : Capabilities}
    (hHT : HasType decl syn x c₀ env (.bool b) ca) (hc : CapsEquiv c₀ c)
    (h : typeOf x c env = .ok (tx, c₁)) : tx.typeOf = .bool b :=
  (hasType_det hwf hHT hc h).1

/-- **Level checking.** For an expression `x` that `typeOf` types as `tx` under capabilities
    `c`, `LevelOk` and `EntityAccessOk` (under any capabilities equivalent to `c`) agree with
    `tx.checkLevel` and `tx.checkEntityAccessLevel`. -/
theorem levelIff_of_typeOf {env : TypeEnv} (hwf : EnvAssumptions env) :
    ∀ (x : Expr) {c c₀ : Capabilities} {tx : TypedExpr} {c' : Capabilities},
      typeOf x c env = .ok (tx, c') → CapsEquiv c₀ c → LevelIff x c₀ env tx
  | .lit p, c, c₀, tx, c', h, _ => by
    simp only [typeOf] at h
    obtain ⟨ty, rfl⟩ := typeOfLit_shape h
    refine ⟨fun n => ⟨fun _ => by simp [TypedExpr.checkLevel], fun _ => .lit _ _ _ _⟩,
      fun n nmax path => ?_⟩
    obtain ⟨ets, acts, ⟨pr, act, r, ctx⟩⟩ := env
    cases p
    case entityUID uid =>
      simp only [TypedExpr.checkEntityAccessLevel, beq_iff_eq]
      constructor
      · intro he; cases he; rfl
      · rintro rfl; exact .action _ _ _ _ _ _ _ _ _ _
    all_goals
      simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
      intro he; cases he
  | .var v, c, c₀, tx, c', h, _ => by
    simp only [typeOf] at h
    obtain ⟨ty, rfl⟩ := typeOfVar_shape h
    exact ⟨fun n => ⟨fun _ => by simp [TypedExpr.checkLevel], fun _ => .var _ _ _ _⟩,
      fun n nmax path => ⟨fun _ => by simp [TypedExpr.checkEntityAccessLevel],
        fun _ => .var _ _ _ _ _ _⟩⟩
  | .ite a b e, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      have ih1 := levelIff_of_typeOf hwf a h1 hc
      obtain ⟨ca, hHTa, hca⟩ := hasType_of_typeOf hwf h1 hc
      have hm₀ := capMerge_append c₀ ca
      rcases typeOfIf_shape h with ⟨hty, tx₂, c₂, h2, rfl⟩ | ⟨hty, tx₃, c₃, h3, rfl⟩ |
        ⟨hty, tx₂, c₂, tx₃, c₃, ty, h2, h3, rfl⟩
      · rw [hty] at hHTa
        have ihb := fun {cb} (hcb : CapsEquiv cb (c ∪ c₁)) => levelIff_of_typeOf hwf b h2 hcb
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · simp only [TypedExpr.checkLevel, Bool.and_eq_true, and_assoc, and_self]
          constructor
          · intro hl
            cases hl with
            | iteTt _ _ _ _ _ _ ca' cca' hHT' hm hla hlb =>
              exact ⟨(ih1.1 n).mp hla,
                ((ihb (capMerge_capsEquiv hm hc (hasType_det hwf hHT' hc h1).2)).1 n).mp hlb⟩
            | iteFf _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteAnyBool _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
          · rintro ⟨hla, hlb⟩
            exact .iteTt _ _ _ _ _ _ _ _ hHTa hm₀ ((ih1.1 n).mpr hla)
              (((ihb (capMerge_capsEquiv hm₀ hc hca)).1 n).mpr hlb)
        · simp only [TypedExpr.checkEntityAccessLevel, Bool.and_eq_true, and_assoc, and_self]
          constructor
          · intro he
            cases he with
            | iteTt _ _ _ _ _ _ _ _ ca' cca' hHT' hm hla heb =>
              exact ⟨(ih1.1 nmax).mp hla,
                ((ihb (capMerge_capsEquiv hm hc (hasType_det hwf hHT' hc h1).2)).2 n nmax path).mp heb⟩
            | iteFf _ _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteAnyBool _ _ _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
          · rintro ⟨hla, heb⟩
            exact .iteTt _ _ _ _ _ _ _ _ _ _ hHTa hm₀ ((ih1.1 nmax).mpr hla)
              (((ihb (capMerge_capsEquiv hm₀ hc hca)).2 n nmax path).mpr heb)
      · rw [hty] at hHTa
        have ihe := levelIff_of_typeOf hwf e h3 hc
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · simp only [TypedExpr.checkLevel, Bool.and_eq_true, and_assoc, and_self]
          constructor
          · intro hl
            cases hl with
            | iteTt _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteFf _ _ _ _ _ _ _ _ hla hle => exact ⟨(ih1.1 n).mp hla, (ihe.1 n).mp hle⟩
            | iteAnyBool _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
          · rintro ⟨hla, hle⟩
            exact .iteFf _ _ _ _ _ _ _ hHTa ((ih1.1 n).mpr hla) ((ihe.1 n).mpr hle)
        · simp only [TypedExpr.checkEntityAccessLevel, Bool.and_eq_true, and_assoc, and_self]
          constructor
          · intro he
            cases he with
            | iteTt _ _ _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteFf _ _ _ _ _ _ _ _ _ _ hla hee =>
              exact ⟨(ih1.1 nmax).mp hla, (ihe.2 n nmax path).mp hee⟩
            | iteAnyBool _ _ _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
          · rintro ⟨hla, hee⟩
            exact .iteFf _ _ _ _ _ _ _ _ _ hHTa ((ih1.1 nmax).mpr hla) ((ihe.2 n nmax path).mpr hee)
      · rw [hty] at hHTa
        have ihb := fun {cb} (hcb : CapsEquiv cb (c ∪ c₁)) => levelIff_of_typeOf hwf b h2 hcb
        have ihe := levelIff_of_typeOf hwf e h3 hc
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · simp only [TypedExpr.checkLevel, Bool.and_eq_true, and_assoc]
          constructor
          · intro hl
            cases hl with
            | iteTt _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteFf _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteAnyBool _ _ _ _ _ _ ca' cca' hHT' hm hla hlb hle =>
              exact ⟨(ih1.1 n).mp hla,
                ((ihb (capMerge_capsEquiv hm hc (hasType_det hwf hHT' hc h1).2)).1 n).mp hlb,
                (ihe.1 n).mp hle⟩
          · rintro ⟨hla, hlb, hle⟩
            exact .iteAnyBool _ _ _ _ _ _ _ _ hHTa hm₀ ((ih1.1 n).mpr hla)
              (((ihb (capMerge_capsEquiv hm₀ hc hca)).1 n).mpr hlb) ((ihe.1 n).mpr hle)
        · simp only [TypedExpr.checkEntityAccessLevel, Bool.and_eq_true, and_assoc]
          constructor
          · intro he
            cases he with
            | iteTt _ _ _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteFf _ _ _ _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this
            | iteAnyBool _ _ _ _ _ _ _ _ ca' cca' hHT' hm hla heb hee =>
              exact ⟨(ih1.1 nmax).mp hla,
                ((ihb (capMerge_capsEquiv hm hc (hasType_det hwf hHT' hc h1).2)).2 n nmax path).mp heb,
                (ihe.2 n nmax path).mp hee⟩
          · rintro ⟨hla, heb, hee⟩
            exact .iteAnyBool _ _ _ _ _ _ _ _ _ _ hHTa hm₀ ((ih1.1 nmax).mpr hla)
              (((ihb (capMerge_capsEquiv hm₀ hc hca)).2 n nmax path).mpr heb)
              ((ihe.2 n nmax path).mpr hee)
  | .and a b, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      have ih1 := levelIff_of_typeOf hwf a h1 hc
      obtain ⟨ca, hHTa, hca⟩ := hasType_of_typeOf hwf h1 hc
      have hm₀ := capMerge_append c₀ ca
      rcases typeOfAnd_shape h with ⟨hty, rfl⟩ | ⟨b₁, hty, hne, tx₂, c₂, ty, h2, rfl⟩
      · rw [hty] at hHTa
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · rw [← ih1.1 n]
          constructor
          · intro hl
            cases hl with
            | andFf _ _ _ _ _ _ _ hla => exact hla
            | and _ _ _ _ _ _ _ _ hHT' hnf =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this; cases hnf
          · exact fun hla => .andFf _ _ _ _ _ _ hHTa hla
        · rw [← ih1.2 n nmax path]
          constructor
          · intro he; cases he with | andFf _ _ _ _ _ _ _ _ _ hea => exact hea
          · exact fun hea => .andFf _ _ _ _ _ _ _ _ hHTa hea
      · rw [hty] at hHTa
        have hnf : NotFf b₁ := notFf_iff.mpr hne
        have ihb := fun {cb} (hcb : CapsEquiv cb (c ∪ c₁)) => levelIff_of_typeOf hwf b h2 hcb
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · simp only [TypedExpr.checkLevel, Bool.and_eq_true]
          constructor
          · intro hl
            cases hl with
            | andFf _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this; exact absurd rfl hne
            | and _ _ _ _ _ _ ca' cca' hHT' _ hm hla hlb =>
              exact ⟨(ih1.1 n).mp hla,
                ((ihb (capMerge_capsEquiv hm hc (hasType_det hwf hHT' hc h1).2)).1 n).mp hlb⟩
          · rintro ⟨hla, hlb⟩
            exact .and _ _ _ _ _ _ _ _ hHTa hnf hm₀ ((ih1.1 n).mpr hla)
              (((ihb (capMerge_capsEquiv hm₀ hc hca)).1 n).mpr hlb)
        · simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
          intro he
          cases he with
          | andFf _ _ _ _ _ _ _ _ hHT' =>
            have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this; exact hne rfl
  | .or a b, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      have ih1 := levelIff_of_typeOf hwf a h1 hc
      obtain ⟨ca, hHTa, hca⟩ := hasType_of_typeOf hwf h1 hc
      rcases typeOfOr_shape h with ⟨hty, rfl⟩ | ⟨b₁, hty, hne, tx₂, c₂, ty, h2, rfl⟩
      · rw [hty] at hHTa
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · rw [← ih1.1 n]
          constructor
          · intro hl
            cases hl with
            | orTt _ _ _ _ _ _ _ hla => exact hla
            | or _ _ _ _ _ _ _ hHT' hnt =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this; cases hnt
          · exact fun hla => .orTt _ _ _ _ _ _ hHTa hla
        · rw [← ih1.2 n nmax path]
          constructor
          · intro he; cases he with | orTt _ _ _ _ _ _ _ _ _ hea => exact hea
          · exact fun hea => .orTt _ _ _ _ _ _ _ _ hHTa hea
      · rw [hty] at hHTa
        have hnt : NotTt b₁ := notTt_iff.mpr hne
        have ihb := levelIff_of_typeOf hwf b h2 hc
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · simp only [TypedExpr.checkLevel, Bool.and_eq_true]
          constructor
          · intro hl
            cases hl with
            | orTt _ _ _ _ _ _ hHT' =>
              have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this; exact absurd rfl hne
            | or _ _ _ _ _ _ _ _ _ hla hlb => exact ⟨(ih1.1 n).mp hla, (ihb.1 n).mp hlb⟩
          · rintro ⟨hla, hlb⟩
            exact .or _ _ _ _ _ _ _ hHTa hnt ((ih1.1 n).mpr hla) ((ihb.1 n).mpr hlb)
        · simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
          intro he
          cases he with
          | orTt _ _ _ _ _ _ _ _ hHT' =>
            have := hasType_bool_eq hwf hHT' hc h1; rw [hty] at this; cases this; exact hne rfl
  | .unaryApp op a, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨ty, rfl⟩ := typeOfUnaryApp_shape h
      have ih1 := levelIff_of_typeOf hwf a h1 hc
      refine ⟨fun n => ?_, fun n nmax path => ?_⟩
      · simp only [TypedExpr.checkLevel]
        rw [← ih1.1 n]
        constructor
        · intro hl; cases hl with | unaryApp _ _ _ _ _ hla => exact hla
        · exact fun hla => .unaryApp _ _ _ _ _ hla
      · simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
        intro he; cases he
  | .binaryApp op a b, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      cases h2 : typeOf b c env with
      | error => rw [h2] at h; simp at h
      | ok r2 =>
        obtain ⟨tx₂, c₂⟩ := r2
        rw [h2] at h; simp only [Except.bind_ok] at h
        obtain ⟨ty, rfl⟩ := typeOfBinaryApp_shape h
        have ih1 := levelIff_of_typeOf hwf a h1 hc
        have ih2 := levelIff_of_typeOf hwf b h2 hc
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · have hderef : ∀ op', DerefOp op' → op = op' →
              (LevelOk (.binaryApp op a b) c₀ env n ↔
                (decide (n > 0) && tx₁.checkEntityAccessLevel env (n - 1) n [] &&
                  tx₂.checkLevel env n) = true) := by
            rintro op' hop rfl
            cases n with
            | zero =>
              simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, iff_false]
              intro hl
              cases hl with
              | binaryApp _ _ _ _ _ _ hop' => cases hop <;> cases hop'
            | succ m =>
              simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, Bool.and_eq_true,
                Nat.add_one_sub_one]
              rw [← ih1.2 m (m + 1) [], ← ih2.1 (m + 1)]
              constructor
              · intro hl
                cases hl with
                | binaryAppDeref _ _ _ _ _ _ _ hea hlb => exact ⟨hea, hlb⟩
                | binaryApp _ _ _ _ _ _ hop' => cases hop <;> cases hop'
              · rintro ⟨hea, hlb⟩; exact .binaryAppDeref _ _ _ _ _ _ hop hea hlb
          have hplain : NotDerefOp op →
              (LevelOk (.binaryApp op a b) c₀ env n ↔
                (tx₁.checkLevel env n && tx₂.checkLevel env n) = true) := by
            intro hop
            rw [Bool.and_eq_true, ← ih1.1 n, ← ih2.1 n]
            constructor
            · intro hl
              cases hl with
              | binaryAppDeref _ _ _ _ _ _ hop' => cases hop <;> cases hop'
              | binaryApp _ _ _ _ _ _ _ hla hlb => exact ⟨hla, hlb⟩
            · rintro ⟨hla, hlb⟩; exact .binaryApp _ _ _ _ _ _ hop hla hlb
          cases op
          case mem => simp only [TypedExpr.checkLevel]; exact hderef _ .mem rfl
          case getTag => simp only [TypedExpr.checkLevel]; exact hderef _ .getTag rfl
          case hasTag => simp only [TypedExpr.checkLevel]; exact hderef _ .hasTag rfl
          all_goals (simp only [TypedExpr.checkLevel]; exact hplain (by constructor))
        · cases op
          case getTag =>
            simp only [TypedExpr.checkEntityAccessLevel]
            cases n with
            | zero =>
              simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, iff_false]
              intro he; cases he
            | succ m =>
              simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, Bool.and_eq_true,
                Nat.add_one_sub_one]
              rw [← ih1.2 m nmax [], ← ih2.1 nmax]
              constructor
              · intro he; cases he with | getTag _ _ _ _ _ _ _ hea hlb => exact ⟨hea, hlb⟩
              · rintro ⟨hea, hlb⟩; exact .getTag _ _ _ _ _ _ _ hea hlb
          all_goals
            simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
            intro he; cases he
  | .getAttr a k, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨ty, rfl, hrecv⟩ := typeOfGetAttr_shape h
      have ih1 := levelIff_of_typeOf hwf a h1 hc
      obtain ⟨ca, hHTa, hca⟩ := hasType_of_typeOf hwf h1 hc
      rcases hrecv with ⟨ety, hety⟩ | ⟨rty, hrty⟩
      · rw [hety] at hHTa
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · simp only [TypedExpr.checkLevel, hety]
          cases n with
          | zero =>
            simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, iff_false]
            intro hl
            cases hl with
            | getAttrRecord _ _ _ _ _ _ _ hHT' =>
              have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
          | succ m =>
            simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.add_one_sub_one]
            rw [← ih1.2 m (m + 1) []]
            constructor
            · intro hl
              cases hl with
              | getAttrEntity _ _ _ _ _ _ _ _ hea => exact hea
              | getAttrRecord _ _ _ _ _ _ _ hHT' =>
                have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
            · exact fun hea => .getAttrEntity _ _ _ _ _ _ _ hHTa hea
        · simp only [TypedExpr.checkEntityAccessLevel, hety]
          cases n with
          | zero =>
            simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, iff_false]
            intro he
            cases he with
            | getAttrRecord _ _ _ _ _ _ _ _ _ hHT' =>
              have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
          | succ m =>
            simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.add_one_sub_one]
            rw [← ih1.2 m nmax []]
            constructor
            · intro he
              cases he with
              | getAttrEntity _ _ _ _ _ _ _ _ _ _ hea => exact hea
              | getAttrRecord _ _ _ _ _ _ _ _ _ hHT' =>
                have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
            · exact fun hea => .getAttrEntity _ _ _ _ _ _ _ _ _ hHTa hea
      · rw [hrty] at hHTa
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · simp only [TypedExpr.checkLevel, hrty]
          rw [← ih1.1 n]
          constructor
          · intro hl
            cases hl with
            | getAttrEntity _ _ _ _ _ _ _ hHT' =>
              have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
            | getAttrRecord _ _ _ _ _ _ _ _ hla => exact hla
          · exact fun hla => .getAttrRecord _ _ _ _ _ _ _ hHTa hla
        · simp only [TypedExpr.checkEntityAccessLevel, hrty]
          rw [← ih1.2 n nmax (k :: path)]
          constructor
          · intro he
            cases he with
            | getAttrEntity _ _ _ _ _ _ _ _ _ hHT' =>
              have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
            | getAttrRecord _ _ _ _ _ _ _ _ _ _ hea => exact hea
          · exact fun hea => .getAttrRecord _ _ _ _ _ _ _ _ _ hHTa hea
  | .hasAttr a k, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      obtain ⟨ty, rfl, hrecv⟩ := typeOfHasAttr_shape h
      have ih1 := levelIff_of_typeOf hwf a h1 hc
      obtain ⟨ca, hHTa, hca⟩ := hasType_of_typeOf hwf h1 hc
      refine ⟨fun n => ?_, fun n nmax path => ?_⟩
      · rcases hrecv with ⟨ety, hety⟩ | ⟨rty, hrty⟩
        · rw [hety] at hHTa
          simp only [TypedExpr.checkLevel, hety]
          cases n with
          | zero =>
            simp only [Nat.lt_irrefl, decide_false, Bool.false_and, Bool.false_eq_true, iff_false]
            intro hl
            cases hl with
            | hasAttrRecord _ _ _ _ _ _ _ hHT' =>
              have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
          | succ m =>
            simp only [Nat.zero_lt_succ, decide_true, Bool.true_and, Nat.add_one_sub_one]
            rw [← ih1.2 m (m + 1) []]
            constructor
            · intro hl
              cases hl with
              | hasAttrEntity _ _ _ _ _ _ _ _ hea => exact hea
              | hasAttrRecord _ _ _ _ _ _ _ hHT' =>
                have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
            · exact fun hea => .hasAttrEntity _ _ _ _ _ _ _ hHTa hea
        · rw [hrty] at hHTa
          simp only [TypedExpr.checkLevel, hrty]
          rw [← ih1.1 n]
          constructor
          · intro hl
            cases hl with
            | hasAttrEntity _ _ _ _ _ _ _ hHT' =>
              have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
            | hasAttrRecord _ _ _ _ _ _ _ _ hla => exact hla
          · exact fun hla => .hasAttrRecord _ _ _ _ _ _ _ hHTa hla
      · simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
        intro he; cases he
  | .extHasAttr a k ks, c, c₀, tx, c', h, hc => by
    simp only [typeOf] at h
    cases h1 : typeOf a c env with
    | error => rw [h1] at h; simp at h
    | ok r1 =>
      obtain ⟨tx₁, c₁⟩ := r1
      rw [h1] at h; simp only [Except.bind_ok] at h
      cases h2 : typeOfExtHasAttr tx₁ a (k :: ks) c env with
      | error => rw [h2] at h; simp at h
      | ok r2 =>
        obtain ⟨bty, c₂⟩ := r2
        rw [h2] at h
        simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hrecv := typeOfExtHasAttr_receiver h2
        have ih1 := levelIff_of_typeOf hwf a h1 hc
        obtain ⟨ca, hHTa, hca⟩ := hasType_of_typeOf hwf h1 hc
        refine ⟨fun n => ?_, fun n nmax path => ?_⟩
        · rcases hrecv with ⟨ety, hety⟩ | ⟨rty, hrty⟩
          · rw [hety] at hHTa
            simp only [TypedExpr.checkLevel, hety, Bool.and_eq_true, decide_eq_true_eq]
            rw [← ih1.2]
            constructor
            · intro hl
              cases hl with
              | extHasAttrEntity _ _ _ _ _ _ _ _ hHT' hlt hea =>
                have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
                exact ⟨hlt, hea⟩
              | extHasAttrRecordPath _ _ _ _ _ _ _ _ _ hHT' =>
                have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
              | extHasAttrRecordNoPath _ _ _ _ _ _ _ _ hHT' =>
                have := (hasType_det hwf hHT' hc h1).1; rw [hety] at this; cases this
            · rintro ⟨hlt, hea⟩; exact .extHasAttrEntity _ _ _ _ _ _ _ _ hHTa hlt hea
          · rw [hrty] at hHTa
            simp only [TypedExpr.checkLevel, hrty, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
            rw [← ih1.1 n]
            cases hp : extHasAttrFirstEntityPath? env (.record rty) (k :: ks) with
            | none =>
              simp only [true_and]
              constructor
              · intro hl
                cases hl with
                | extHasAttrEntity _ _ _ _ _ _ _ _ hHT' =>
                  have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
                | extHasAttrRecordPath _ _ _ _ _ _ _ _ _ hHT' hp' =>
                  have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
                  rw [hp] at hp'; cases hp'
                | extHasAttrRecordNoPath _ _ _ _ _ _ _ _ hHT' _ hle hla =>
                  have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
                  exact ⟨hle, hla⟩
              · rintro ⟨hle, hla⟩; exact .extHasAttrRecordNoPath _ _ _ _ _ _ _ _ hHTa hp hle hla
            | some path =>
              simp only
              rw [← ih1.2]
              constructor
              · intro hl
                cases hl with
                | extHasAttrEntity _ _ _ _ _ _ _ _ hHT' =>
                  have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
                | extHasAttrRecordPath _ _ _ _ _ _ _ _ _ hHT' hp' hea hle hla =>
                  have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
                  rw [hp] at hp'; cases hp'
                  exact ⟨hea, hle, hla⟩
                | extHasAttrRecordNoPath _ _ _ _ _ _ _ _ hHT' hp' =>
                  have := (hasType_det hwf hHT' hc h1).1; rw [hrty] at this; cases this
                  rw [hp] at hp'; cases hp'
              · rintro ⟨hea, hle, hla⟩
                exact .extHasAttrRecordPath _ _ _ _ _ _ _ _ _ hHTa hp hea hle hla
        · simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
          intro he; cases he
  | .set xs, c, c₀, tx, c', h, hc => by
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
    cases hm : xs.mapM (fun x => justType (typeOf x c env)) with
    | error => rw [hm] at h; simp at h
    | ok tys =>
      rw [hm] at h; simp only [Except.bind_ok] at h
      obtain ⟨ty, rfl⟩ := typeOfSet_shape h
      have hf : List.Forall₂ (fun x tx => LevelIff x c₀ env tx) xs tys :=
        mapM_justType_forall₂ hm fun x hx _ _ htx =>
          have : sizeOf x < 1 + sizeOf xs := by have := List.sizeOf_lt_of_mem hx; omega
          levelIff_of_typeOf hwf x htx hc
      refine ⟨fun n => ?_, fun n nmax path => ?_⟩
      · simp only [TypedExpr.checkLevel, attach_all_val tys (TypedExpr.checkLevel · env n),
          List.all_eq_true]
        rw [← levelOkList_iff hf]
        constructor
        · intro hl; cases hl with | set _ _ _ _ hl => exact hl
        · exact fun hl => .set _ _ _ _ hl
      · simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
        intro he; cases he
  | .call f xs, c, c₀, tx, c', h, hc => by
    simp only [typeOf, List.mapM₁_eq_mapM (fun x => justType (typeOf x c env))] at h
    cases hm : xs.mapM (fun x => justType (typeOf x c env)) with
    | error => rw [hm] at h; simp at h
    | ok tys =>
      rw [hm] at h; simp only [Except.bind_ok] at h
      obtain ⟨ty, rfl⟩ := typeOfCall_shape h
      have hf : List.Forall₂ (fun x tx => LevelIff x c₀ env tx) xs tys :=
        mapM_justType_forall₂ hm fun x hx _ _ htx =>
          have : sizeOf x < 1 + sizeOf f + sizeOf xs := by
            have := List.sizeOf_lt_of_mem hx; omega
          levelIff_of_typeOf hwf x htx hc
      refine ⟨fun n => ?_, fun n nmax path => ?_⟩
      · simp only [TypedExpr.checkLevel, attach_all_val tys (TypedExpr.checkLevel · env n),
          List.all_eq_true]
        rw [← levelOkList_iff hf]
        constructor
        · intro hl; cases hl with | call _ _ _ _ _ hl => exact hl
        · exact fun hl => .call _ _ _ _ _ hl
      · simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
        intro he; cases he
  | .record axs, c, c₀, tx, c', h, hc => by
    simp only [typeOf,
      List.mapM₂_eq_mapM (fun p : Attr × Expr => (typeOf p.2 c env).map (fun r => (p.1, r.1)))] at h
    cases hm : axs.mapM (fun ax => (typeOf ax.2 c env).map (fun r => (ax.1, r.1))) with
    | error => rw [hm] at h; simp at h
    | ok atys =>
      rw [hm] at h; simp only [Except.bind_ok, ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hf : List.Forall₂ (fun ax atx => atx.1 = ax.1 ∧ LevelIff ax.2 c₀ env atx.2) axs atys :=
        mapM_record_forall₂ (P := fun x tx => LevelIff x c₀ env tx) hm fun ax hax _ _ htx =>
          have : sizeOf ax.2 < 1 + sizeOf axs := by
            have := List.sizeOf_lt_of_mem hax
            have : sizeOf ax.2 < sizeOf ax := by
              obtain ⟨a, x⟩ := ax; simp only [Prod.mk.sizeOf_spec]; omega
            omega
          levelIff_of_typeOf hwf ax.2 htx hc
      have hall : ∀ n, LevelOkRecord axs c₀ env n ↔
          (atys.attach₂.all fun e => e.val.snd.checkLevel env n) = true := by
        intro n
        rw [attach₂_all_val atys (fun p => p.2.checkLevel env n), List.all_eq_true]
        exact levelOkRecord_iff hf
      refine ⟨fun n => ?_, fun n nmax path => ?_⟩
      · simp only [TypedExpr.checkLevel]
        rw [← hall n]
        constructor
        · intro hl; cases hl with | record _ _ _ _ hl => exact hl
        · exact fun hl => .record _ _ _ _ hl
      · cases path with
        | nil =>
          simp only [TypedExpr.checkEntityAccessLevel, Bool.false_eq_true, iff_false]
          intro he; cases he
        | cons k path =>
          simp only [TypedExpr.checkEntityAccessLevel]
          split
          · rename_i tx' hfind
            rw [make_find?_eq_mk_find?] at hfind
            rw [Bool.and_eq_true, ← hall nmax]
            constructor
            · intro he
              cases he with
              | record _ _ x _ _ _ _ _ hff hex hl =>
                obtain ⟨tx'', hfind', hS⟩ := recordFieldFind_find? (S := fun x tx => LevelIff x c₀ env tx) hf hff
                rw [hfind] at hfind'; cases hfind'
                exact ⟨(hS.2 n nmax path).mp hex, hl⟩
            · rintro ⟨hex, hl⟩
              obtain ⟨x, hff, hS⟩ := find?_recordFieldFind (S := fun x tx => LevelIff x c₀ env tx) hf hfind
              exact .record _ _ _ _ _ _ _ _ hff ((hS.2 n nmax path).mpr hex) hl
          · rename_i hfind
            rw [make_find?_eq_mk_find?] at hfind
            simp only [Bool.false_eq_true, iff_false]
            intro he
            cases he with
            | record _ _ x _ _ _ _ _ hff =>
              obtain ⟨tx'', hfind', _⟩ := recordFieldFind_find? (S := fun x tx => LevelIff x c₀ env tx) hf hff
              rw [hfind] at hfind'; cases hfind'
termination_by x => sizeOf x

/-! ## Validation at a level -/

theorem typecheckPolicyWithLevel_eq {p : Policy} {n : Nat} {env : TypeEnv} {tx : TypedExpr} :
    typecheckPolicyWithLevel p n env = .ok tx ↔
      typecheckPolicy p env = .ok tx ∧ tx.checkLevel env n = true := by
  simp only [typecheckPolicyWithLevel, bind, Except.bind]
  cases typecheckPolicy p env with
  | error e => simp
  | ok tx' =>
    simp only [Except.ok.injEq]
    cases hcl : tx'.checkLevel env n
    · simp only [Bool.false_eq_true, ite_false, reduceCtorEq, false_iff, not_and]
      rintro rfl; simp [hcl]
    · simp only [ite_true, Except.ok.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hcl⟩
      · rintro ⟨rfl, _⟩; rfl

/-- `typecheckPolicyWithLevel` gives type `.bool b` exactly when `HasType` derives it for the
    policy expression with `action` replaced by the environment's action, and `LevelOk` holds
    for that expression at the level. -/
theorem typecheckPolicyWithLevel_ok_iff {p : Policy} {n : Nat} {env : TypeEnv}
    (hwf : EnvAssumptions env)
    {b : BoolType} :
    (∃ tx, typecheckPolicyWithLevel p n env = .ok tx ∧ tx.typeOf = .bool b) ↔
      ∃ cout, HasType false false (substituteAction env.reqty.action p.toExpr) [] env (.bool b)
        cout ∧
        LevelOk (substituteAction env.reqty.action p.toExpr) [] env n := by
  have hlevel : ∀ tx, typecheckPolicy p env = .ok tx →
      (LevelOk (substituteAction env.reqty.action p.toExpr) [] env n ↔
        tx.checkLevel env n = true) := by
    intro tx htc
    simp only [typecheckPolicy, List.empty_eq] at htc
    split at htc
    · rename_i tx' c' hto
      split at htc
      · simp only [Except.ok.injEq] at htc; subst htc
        exact (levelIff_of_typeOf hwf _ hto (CapsEquiv.refl [])).1 n
      · simp at htc
    · simp at htc
  constructor
  · rintro ⟨tx, h, hty⟩
    obtain ⟨htc, hcl⟩ := typecheckPolicyWithLevel_eq.mp h
    obtain ⟨cout, hHT⟩ := (typecheckPolicy_ok_iff hwf).mp ⟨tx, htc, hty⟩
    exact ⟨cout, hHT, (hlevel tx htc).mpr hcl⟩
  · rintro ⟨cout, hHT, hl⟩
    obtain ⟨tx, htc, hty⟩ := (typecheckPolicy_ok_iff hwf).mpr ⟨cout, hHT⟩
    exact ⟨tx, typecheckPolicyWithLevel_eq.mpr ⟨htc, (hlevel tx htc).mp hl⟩, hty⟩

/-- Every environment's level-checked typed policy has a Boolean type. -/
theorem mapM_typecheckPolicyWithLevel_bool {p : Policy} {n : Nat} {envs : List TypeEnv}
    {txs : List TypedExpr} (h : envs.mapM (typecheckPolicyWithLevel p n) = .ok txs) :
    ∃ bs : List BoolType, txs.map TypedExpr.typeOf = bs.map .bool := by
  induction envs generalizing txs with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h; exact ⟨[], rfl⟩
  | cons env envs ih =>
    simp only [List.mapM_cons, bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i tx htc
      split at h
      · simp at h
      · rename_i txs' hrest
        simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        obtain ⟨bs, hbs⟩ := ih hrest
        have htc' := (typecheckPolicyWithLevel_eq.mp htc).1
        simp only [typecheckPolicy] at htc'
        split at htc'
        · split at htc'
          · rename_i hsub
            simp only [Except.ok.injEq] at htc'; subst htc'
            obtain ⟨b, hb⟩ := subty_bool_anyBool.mp hsub
            exact ⟨b :: bs, by simp [hb, hbs]⟩
          · simp at htc'
        · simp at htc'

/-- `TypedAtLevelInEnvs` is `typecheckPolicyWithLevel` succeeding in every environment. -/
theorem typedAtLevelInEnvs_iff {p : Policy} {n : Nat} :
    ∀ {envs : List TypeEnv}, (∀ env ∈ envs, EnvAssumptions env) →
      ∀ {bs : List BoolType},
        TypedAtLevelInEnvs envs n p.toExpr bs ↔
          ∃ txs, envs.mapM (typecheckPolicyWithLevel p n) = .ok txs ∧
            txs.map TypedExpr.typeOf = bs.map .bool
  | [], _, bs => by
    constructor
    · intro h; cases h; exact ⟨[], rfl, rfl⟩
    · rintro ⟨txs, h, hbs⟩
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h; subst h
      cases bs with
      | nil => exact .nil _ _
      | cons _ _ => simp at hbs
  | env :: envs, hwf, bs => by
    obtain ⟨ets, acts, ⟨pr, act, r, ctx⟩⟩ := env
    have hwf₀ := hwf _ (List.mem_cons_self ..)
    have hwf' : ∀ e ∈ envs, EnvAssumptions e := fun e he => hwf e (List.mem_cons_of_mem _ he)
    constructor
    · intro h
      cases h with
      | cons _ _ _ _ _ _ _ _ x' b cout _ bs' hs hht hl hrest =>
        rw [hs.eq_substituteAction] at hht hl
        obtain ⟨tx, htc, hty⟩ :=
          (typecheckPolicyWithLevel_ok_iff (n := n) (b := b) hwf₀).mpr ⟨cout, hht, hl⟩
        obtain ⟨txs, hm, hbs⟩ := (typedAtLevelInEnvs_iff (bs := bs') hwf').mp hrest
        exact ⟨tx :: txs, by simp [List.mapM_cons, htc, hm, bind, Except.bind, pure, Except.pure],
          by simp [hty, hbs]⟩
    · rintro ⟨txs, hm, hbs⟩
      simp only [List.mapM_cons, bind, Except.bind] at hm
      split at hm
      · simp at hm
      · rename_i tx htc
        split at hm
        · simp at hm
        · rename_i txs' hrest
          simp only [pure, Except.pure, Except.ok.injEq] at hm; subst hm
          cases bs with
          | nil => simp at hbs
          | cons b bs' =>
            simp only [List.map_cons, List.cons.injEq] at hbs
            obtain ⟨hty, hbs'⟩ := hbs
            obtain ⟨cout, hht, hl⟩ :=
              (typecheckPolicyWithLevel_ok_iff (n := n) (b := b) hwf₀).mp ⟨tx, htc, hty⟩
            exact .cons _ _ _ _ _ _ _ _ _ _ _ _ _ (substAction_substituteAction act p.toExpr) hht hl
              ((typedAtLevelInEnvs_iff (bs := bs') hwf').mpr ⟨txs', hrest, hbs'⟩)

theorem typedAtLevelInEnvs_ne_nil {envs : List TypeEnv} {n : Nat} {x : Expr} {bs : List BoolType}
    (h : TypedAtLevelInEnvs envs n x bs) (hs : SomeNotFf bs) : ∃ env, env ∈ envs := by
  cases h with
  | nil => cases hs
  | cons ets acts pr act r ctx => exact ⟨_, List.mem_cons_self ..⟩

theorem typecheckPolicyWithEnvironments_level_ok_iff {p : Policy} {schema : Schema} {n : Nat} :
    typecheckPolicyWithEnvironments (typecheckPolicyWithLevel · n) p schema = .ok () ↔
      checkEntities schema p.toExpr = .ok () ∧
        ∃ txs, schema.environments.mapM (typecheckPolicyWithLevel p n) = .ok txs ∧
          allFalse txs = false := by
  simp only [typecheckPolicyWithEnvironments]
  cases hce : checkEntities schema p.toExpr with
  | error e => simp [Except.mapError, bind, Except.bind]
  | ok u =>
    cases u
    cases hm : schema.environments.mapM (typecheckPolicyWithLevel p n) with
    | error e => simp [Except.mapError, bind, Except.bind]
    | ok txs => cases haf : allFalse txs <;> simp [haf, Except.mapError, bind, Except.bind]

/-- **Level-based policy validation.** On a schema whose environments satisfy
    `EnvAssumptions`, `validateWithLevel` accepts a policy at level `n` exactly when
    `ValidPolicyAtLevel` holds for it. -/
theorem validateWithLevel_singleton_iff {schema : Schema} {p : Policy} {n : Nat}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env) :
    validateWithLevel [p] schema n = .ok () ↔
      ValidPolicyAtLevel schema.ets schema.acts schema.environments n p := by
  rw [validateWithLevel, forM_singleton, typecheckPolicyWithEnvironments_level_ok_iff]
  constructor
  · rintro ⟨hce, txs, hm, hnf⟩
    have hent : ∀ env ∈ schema.environments, EntitiesDeclared schema.ets schema.acts p.toExpr := by
      intro env henv
      have hnd := (hwf env henv).ets_keys_nodup
      rw [(mem_environments henv).1] at hnd
      exact entitiesDeclared_of_checkEntities (acts := schema.acts) hnd _ hce
    obtain ⟨bs, hbs⟩ := mapM_typecheckPolicyWithLevel_bool hm
    have hsome := (allFalse_eq_false_iff hbs).mp hnf
    have htyped := (typedAtLevelInEnvs_iff hwf).mpr ⟨txs, hm, hbs⟩
    obtain ⟨env, henv⟩ := typedAtLevelInEnvs_ne_nil htyped hsome
    exact .mk _ _ _ _ _ _ bs (policyExpr_toExpr p) (hent env henv) htyped hsome
  · intro h
    cases h with
    | mk x bs hpe hent htyped hsome =>
      rw [hpe.eq_toExpr] at hent htyped
      obtain ⟨env, henv⟩ := typedAtLevelInEnvs_ne_nil htyped hsome
      obtain ⟨hets, hacts⟩ := mem_environments henv
      have hndE := (hwf env henv).ets_keys_nodup
      have hndA := (hwf env henv).acts_keys_nodup
      rw [hets] at hndE
      rw [hacts] at hndA
      obtain ⟨txs, hm, hbs⟩ := (typedAtLevelInEnvs_iff hwf).mp htyped
      exact ⟨hent.checkEntities_ok hndE hndA, txs, hm, (allFalse_eq_false_iff hbs).mpr hsome⟩

/-- **Level-based validation.** On a schema whose environments satisfy `EnvAssumptions`,
    `validateWithLevel` accepts a set of policies at level `n` exactly when
    `ValidPolicyAtLevel` holds for each of them. -/
theorem validateWithLevel_iff {schema : Schema} {ps : Policies} {n : Nat}
    (hwf : ∀ env ∈ schema.environments, EnvAssumptions env) :
    validateWithLevel ps schema n = .ok () ↔
      ∀ p ∈ ps, ValidPolicyAtLevel schema.ets schema.acts schema.environments n p := by
  have hone : ∀ p ∈ ps,
      (typecheckPolicyWithEnvironments (typecheckPolicyWithLevel · n) p schema = .ok () ↔
        ValidPolicyAtLevel schema.ets schema.acts schema.environments n p) := by
    intro p hp
    have := validateWithLevel_singleton_iff (p := p) (n := n) hwf
    rwa [validateWithLevel, forM_singleton] at this
  constructor
  · intro h p hp
    exact (hone p hp).mp (List.forM_ok_implies_all_ok _ _ h p hp)
  · intro h
    exact List.all_ok_implies_forM_ok _ _ (fun p hp => (hone p hp).mpr (h p hp))

/-- `validateWithLevel_iff` on a schema that passes Cedar's schema well-formedness check. -/
theorem validateWithLevel_iff_of_validateWellFormed {schema : Schema} {ps : Policies} {n : Nat}
    (hwf : schema.validateWellFormed = .ok ()) :
    validateWithLevel ps schema n = .ok () ↔
      ∀ p ∈ ps, ValidPolicyAtLevel schema.ets schema.acts schema.environments n p :=
  validateWithLevel_iff (envAssumptions_of_validateWellFormed hwf)

end Cedar.Validation.Relational
