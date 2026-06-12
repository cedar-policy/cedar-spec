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

import Cedar.Thm.Validation.Typechecker.Basic

/-!
This file proves that typechecking of `.call` expressions is sound.
-/

namespace Cedar.Thm

open Cedar.Data
open Cedar.Spec
open Cedar.Validation

theorem type_of_call_args_inversion {xs : List Expr} {txs : List TypedExpr} {c : Capabilities} {env : TypeEnv}
  (htxs : (xs.mapM₁ λ x => justType (typeOf x.val c env)) = Except.ok txs) :
  List.Forall₂ (λ xᵢ txᵢ => ∃ cᵢ, typeOf xᵢ c env = Except.ok (txᵢ, cᵢ)) xs txs
:=
match xs with
| [] => by
  replace htxs : txs = [] :=
    by simpa [List.mapM₁, pure, Except.pure] using htxs
  subst htxs
  constructor
| x :: xs => by
  simp only [List.mapM₁_eq_mapM λ x => justType (typeOf x c env), List.mapM_cons, bind_pure_comp] at htxs
  simp_do_let (justType (typeOf x c env)) as htx at htxs
  simp only [justType, Except.map] at htx
  split at htx <;> simp only [reduceCtorEq, Except.ok.injEq] at htx
  subst htx
  cases htxs' : List.mapM (fun x => justType (typeOf x c env)) xs <;>
    simp only [htxs', Except.map_error, Except.map_ok, reduceCtorEq, Except.ok.injEq] at htxs
  subst txs
  constructor
  · rename_i r _ _
    exists r.snd
  · have ih := @type_of_call_args_inversion xs
    simp [ih, htxs', List.mapM₁]

theorem type_of_call_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {tx : TypedExpr}
  (htx : typeOf (Expr.call xfn xs) c env = Except.ok (tx, c')) :
  ∃ txs,
    (∃ ty, tx = .call xfn txs ty) ∧
    List.Forall₂ (λ xᵢ txᵢ => ∃ cᵢ, typeOf xᵢ c env = .ok (txᵢ, cᵢ)) xs txs
:= by
  simp only [typeOf, typeOfCall] at htx
  simp_do_let (xs.mapM₁ fun x => justType (typeOf x.val c env)) as htx₁ at htx
  rename_i txs
  exists txs
  and_intros
  · split at htx <;>
    (first
    | contradiction
    | cases htx₁ : typeOfConstructor Ext.Decimal.decimal xs (CedarType.ext ExtType.decimal) <;> simp only [htx₁] at htx
    | cases htx₁ : typeOfConstructor Ext.IPAddr.ip xs (CedarType.ext ExtType.ipAddr) <;> simp only [htx₁] at htx
    | cases htx₁ : typeOfConstructor Cedar.Spec.Ext.Datetime.parse xs (.ext .datetime) <;> simp only [htx₁] at htx
    | cases htx₁ : typeOfConstructor Cedar.Spec.Ext.Datetime.Duration.parse xs (.ext .duration) <;> simp only [htx₁] at htx
    | (simp [typeOfIsInRange] at htx; split at htx <;> try contradiction)
    | skip) <;>
    (try simp only [ok, Except.ok.injEq, Prod.mk.injEq, Except.bind_ok, Except.bind_err, reduceCtorEq] at htx) <;>
    first
      | simp [←htx]
      | exact ⟨_, rfl⟩
      | (split at htx <;> simp [err] at htx
         obtain ⟨htx, _⟩ := htx
         exact ⟨_, htx.symm⟩)
  · exact type_of_call_args_inversion htx₁

theorem type_of_call_decimal_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .decimal xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .decimal ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.Decimal.decimal s).isSome
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall, typeOfConstructor] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  cases h₁ ; subst ty c'
  rename_i h₃
  simp [TypedExpr.typeOf, h₃]

theorem type_of_call_decimal_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .decimal xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .decimal xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .decimal xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₂, h₃, s, h₄, h₅⟩ := type_of_call_decimal_inversion h₁
  rw [h₂]
  subst h₃ h₄
  apply And.intro empty_guarded_capabilities_invariant
  rw [Option.isSome_iff_exists] at h₅
  have ⟨d, h₅⟩ := h₅
  exists .ext d
  constructor
  · simp [EvaluatesTo, evaluate, List.mapM₁, List.mapM, List.mapM.loop, call, res, h₅, Coe.coe]
  · exact decimal_is_instance_of_decimal

theorem type_of_call_datetime_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .datetime xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .datetime ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.Datetime.parse s).isSome
:= by
  simp only [typeOf] at h₁
  simp_do_let (List.mapM₁ xs fun x => justType (typeOf x.val c env)) as h₂ at h₁
  rename_i tys
  simp only [typeOfCall, typeOfConstructor, List.empty_eq] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  simp only [h₁, List.empty_eq, List.cons.injEq, Expr.lit.injEq, Prim.string.injEq, and_true,
    exists_eq_left', true_and]
  rename_i h₃
  cases h₁ ; subst ty
  simp only [TypedExpr.typeOf, h₃, Option.isSome_some, and_self]

theorem type_of_call_datetime_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .datetime xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .datetime xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .datetime xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₂, h₃, s, h₄, h₅⟩ := type_of_call_datetime_inversion h₁
  rw [h₂]
  subst h₃ h₄
  apply And.intro empty_guarded_capabilities_invariant
  rw [Option.isSome_iff_exists] at h₅
  have ⟨dt, h₅⟩ := h₅
  exists .ext dt
  constructor
  · simp [EvaluatesTo, evaluate, List.mapM₁, List.mapM, List.mapM.loop, call, res, h₅, Coe.coe]
  · exact datetime_is_instance_of_datetime

theorem type_of_call_duration_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .duration xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .duration ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.Datetime.duration s).isSome
:= by
  simp only [typeOf] at h₁
  simp_do_let (List.mapM₁ xs fun x => justType (typeOf x.val c env)) as h₂ at h₁
  rename_i tys
  simp only [typeOfCall, typeOfConstructor, List.empty_eq] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  cases h₁ ; subst ty c'
  rename_i h₃
  simp [TypedExpr.typeOf, h₃]

theorem type_of_call_duration_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .duration xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .duration xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .duration xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₂, h₃, s, h₄, h₅⟩ := type_of_call_duration_inversion h₁
  rw [h₂]
  subst h₃ h₄
  apply And.intro empty_guarded_capabilities_invariant
  rw [Option.isSome_iff_exists] at h₅
  have ⟨dt, h₅⟩ := h₅
  exists .ext dt
  constructor
  · simp [EvaluatesTo, evaluate, List.mapM₁, List.mapM, List.mapM.loop, call, res, h₅, Coe.coe]
  · exact duration_is_instance_of_duration

theorem type_of_call_ip_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .ip xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .ipAddr ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.IPAddr.ip s).isSome
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall, typeOfConstructor] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  simp [h₁]
  rename_i h₃
  cases h₁ ; subst ty
  simp [h₃, TypedExpr.typeOf]

theorem type_of_call_ip_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .ip xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .ip xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .ip xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₂, h₃, s, h₄, h₅⟩ := type_of_call_ip_inversion h₁
  rw [h₂]
  subst h₃ h₄
  apply And.intro empty_guarded_capabilities_invariant
  rw [Option.isSome_iff_exists] at h₅
  have ⟨ip, h₅⟩ := h₅
  exists .ext ip
  constructor
  · simp [EvaluatesTo, evaluate, List.mapM₁, List.mapM, List.mapM.loop, call, res, h₅, Coe.coe]
  · exact ipaddr_is_instance_of_ipaddr

theorem typeOf_of_binary_call_inversion {xs : List Expr} {c : Capabilities} {env : TypeEnv} {ty₁ ty₂ : TypedExpr}
  (h₁ : (xs.mapM₁ fun x => justType (typeOf x.val c env)) = Except.ok [ty₁, ty₂]) :
  ∃ x₁ x₂ c₁ c₂,
    xs = [x₁, x₂] ∧
    (typeOf x₁ c env).typeOf = .ok (ty₁.typeOf, c₁) ∧
    (typeOf x₂ c env).typeOf = .ok (ty₂.typeOf, c₂)
:= by
  simp [List.mapM₁] at h₁
  cases xs
  case nil =>
    simp [List.mapM, List.mapM.loop, pure, Except.pure] at h₁
  case cons hd₁ tl₁ =>
    cases tl₁
    case nil =>
      simp [List.mapM, List.mapM.loop] at h₁
      cases h₂ : justType (typeOf hd₁ c env) <;>
      simp only [h₂,
        Except.map_error, reduceCtorEq,
        Except.map_ok, Except.ok.injEq, List.cons.injEq, List.ne_cons_self, and_false] at h₁
    case cons hd₂ tl₂ =>
      cases tl₂
      case nil =>
        rw [List.mapM, List.mapM.loop, justType, Except.map.eq_def] at h₁
        split at h₁ <;> simp at h₁
        rw [List.mapM.loop, justType, Except.map.eq_def] at h₁
        split at h₁ <;> simp at h₁
        simp [List.mapM.loop, pure, Except.pure] at h₁
        rename_i res₁ h₂ _ res₂ h₃
        exists hd₁, hd₂, res₁.2, res₂.2
        simp [ResultType.typeOf, Except.map]
        have ⟨hl₁, hr₁⟩ := h₁ ; clear h₁
        subst hl₁ hr₁
        simp [h₂, h₃]
      case cons hd₃ tl₃ =>
        simp only [List.mapM_cons, bind_assoc, pure_bind] at h₁
        rw [justType, Except.map.eq_def] at h₁
        split at h₁ <;> simp at h₁
        rw [justType, Except.map.eq_def] at h₁
        split at h₁ <;> simp at h₁
        rw [justType, Except.map.eq_def] at h₁
        split at h₁ <;> simp at h₁
        rename_i res₁ _ _ res₂ _ _ res₃ _
        cases h₂ : List.mapM (fun x => justType (typeOf x c env)) tl₃ <;> simp [h₂] at h₁

def IsDecimalComparator : ExtFun → Prop
  | .lessThan
  | .lessThanOrEqual
  | .greaterThan
  | .greaterThanOrEqual => True
  | _                   => False

theorem type_of_call_decimal_comparator_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₀ : IsDecimalComparator xfn)
  (h₁ : typeOf (Expr.call xfn xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .bool .anyBool ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂ : Capabilities),
    xs = [x₁, x₂] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .decimal), c₁) ∧
    (typeOf x₂ c env).typeOf = .ok ((CedarType.ext .decimal), c₂)
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall] at h₁
  simp [IsDecimalComparator] at h₀
  split at h₀
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp [ok] at h₁
      have ⟨ h₁ₗ, h₁ᵣ ⟩ := h₁
      subst h₁ₗ h₁ᵣ
      simp only [List.empty_eq, true_and, TypedExpr.typeOf]
      rename_i h₃
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      have ⟨ h₃ₗ, h₃ᵣ ⟩ := h₃
      rw (config := {occs := .pos [1]}) [←h₃ₗ]
      rw [←h₃ᵣ]
      apply typeOf_of_binary_call_inversion h₂
    }
  }

theorem type_of_call_decimal_comparator_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : IsDecimalComparator xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_decimal_comparator_inversion h₀ h₃
  rw [h₄]
  subst h₅ h₆
  apply And.intro empty_guarded_capabilities_invariant
  simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
    List.mapM_nil, pure_bind, bind_assoc]
  have ih₁ := ih x₁
  have ih₂ := ih x₂
  simp [TypeOfIsSound] at ih₁ ih₂
  split_type_of h₇ ; rename_i h₇ hl₇ hr₇
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  split_type_of h₈ ; rename_i h₈ hl₈ hr₈
  have ⟨_, v₂, hl₂, hr₂⟩ := ih₂ h₁ h₂ h₈
  simp [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp [hl₁] <;>
  try { exact type_is_inhabited_bool}
  rcases hl₂ with hl₂ | hl₂ | hl₂ | hl₂ <;>
  simp [hl₂] <;>
  try { exact type_is_inhabited_bool}
  rw [hl₇] at  hr₁
  have ⟨d₁, hr₁⟩ := instance_of_decimal_type_is_decimal hr₁
  rw [hl₈] at  hr₂
  have ⟨d₂, hr₂⟩ := instance_of_decimal_type_is_decimal hr₂
  subst hr₁ hr₂
  simp [IsDecimalComparator] at h₀
  split at h₀ <;>
  simp [call] <;> try { contradiction }
  all_goals {
    apply bool_is_instance_of_anyBool
  }

/--
Structural inversion for `typeOfIsInRange`: if it succeeds with `.bool .anyBool`,
then it typed at least two arguments and every argument's type is `.ext .ipAddr`.
-/
theorem typeOfIsInRange_ok_inversion {tys : List TypedExpr} {xs : List Expr} {ty : TypedExpr} {c' : Capabilities}
  (h : typeOfIsInRange tys xs = Except.ok (ty, c')) :
  ty.typeOf = .bool .anyBool ∧
  c' = ∅ ∧
  2 ≤ tys.length ∧
  ∀ t ∈ tys, t.typeOf = .ext .ipAddr
:= by
  simp only [typeOfIsInRange] at h
  split at h
  case h_2 => simp only [err, reduceCtorEq] at h
  case h_1 heq =>
    split at h
    case isFalse => simp only [err, reduceCtorEq] at h
    case isTrue hif =>
      simp only [ok, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hty, hc'⟩ := h
      subst hty hc'
      refine ⟨by simp only [TypedExpr.typeOf], rfl, ?_, ?_⟩
      · -- 2 ≤ tys.length : the map matched a two-or-more-element list
        have hlen := congrArg List.length heq
        simp only [List.length_map, List.length_cons] at hlen
        omega
      · -- every element of tys is an ipAddr
        intro t ht
        have hmem : t.typeOf ∈ List.map TypedExpr.typeOf tys := List.mem_map.mpr ⟨t, ht, rfl⟩
        rw [heq, List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · exact hmem
        · rw [List.all_eq_true] at hif
          simpa only [beq_iff_eq] using hif _ hmem

theorem type_of_call_isInRange_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .isInRange xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .bool .anyBool ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (xrest : List Expr) (c₁ : Capabilities),
    xs = x₁ :: xrest ∧
    xrest.length > 0 ∧
    (typeOf x₁ c env).typeOf = .ok ((.ext .ipAddr), c₁) ∧
    ∀ xᵢ ∈ xrest, ∃ cᵢ, (typeOf xᵢ c env).typeOf = .ok ((.ext .ipAddr), cᵢ)
:= by
  simp only [typeOf] at h₁
  cases h₂ : List.mapM₁ xs (fun x => justType (typeOf x.val c env)) <;>
    simp only [h₂, Except.bind_err, Except.bind_ok, reduceCtorEq] at h₁
  rename_i tys
  simp only [typeOfCall] at h₁
  -- Structural facts about `tys`: at least two elements, all `ipAddr`.
  obtain ⟨htyOf, hc', hlen, hall⟩ := typeOfIsInRange_ok_inversion h₁
  refine ⟨htyOf, hc', ?_⟩
  -- Positional correspondence between `xs` and `tys`.
  have hforall := type_of_call_args_inversion h₂
  cases tys with
  | nil => simp only [List.length_nil] at hlen; omega
  | cons ty₁ tytail =>
    cases hforall with
    | cons hhead htail =>
      rename_i x₁ xrest
      obtain ⟨c₁', hx₁⟩ := hhead
      refine ⟨x₁, xrest, c₁', rfl, ?_, ?_, ?_⟩
      · -- xrest.length > 0 : `tytail` is nonempty, and matches `xrest` positionally
        cases htail with
        | nil => simp only [List.length_cons, List.length_nil] at hlen; omega
        | cons => simp only [List.length_cons]; omega
      · -- typeOf x₁ is an ipAddr
        have hty₁ : ty₁.typeOf = .ext .ipAddr := hall ty₁ List.mem_cons_self
        simp only [ResultType.typeOf, hx₁, Except.map, hty₁]
      · -- every element of xrest is an ipAddr
        intro xᵢ hxᵢ
        obtain ⟨tyᵢ, htyᵢ_mem, cᵢ, hxᵢ_ok⟩ := List.forall₂_implies_all_left htail xᵢ hxᵢ
        refine ⟨cᵢ, ?_⟩
        have htyᵢ : tyᵢ.typeOf = .ext .ipAddr := hall tyᵢ (List.mem_cons_of_mem _ htyᵢ_mem)
        simp only [ResultType.typeOf, hxᵢ_ok, Except.map, htyᵢ]

theorem type_of_call_isInRange_comparator_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call .isInRange xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .isInRange xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .isInRange xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₄, h₅, x₁, xrest, c₁', h₆, hlen, h₇, h₈⟩ := type_of_call_isInRange_inversion h₃
  rw [h₄]
  subst h₅ h₆
  refine ⟨empty_guarded_capabilities_invariant, ?_⟩
  obtain ⟨xr, xrs, rfl⟩ : ∃ xr xrs, xrest = xr :: xrs := by
    cases xrest with
    | nil => simp only [List.length_nil, gt_iff_lt, Nat.lt_irrefl] at hlen
    | cons a b => exact ⟨a, b, rfl⟩
  have key : ∀ xᵢ ∈ x₁ :: xr :: xrs, ∃ a, EvaluatesTo xᵢ request entities (.ext (.ipaddr a)) := by
    intro xᵢ hxᵢ
    obtain ⟨cᵢ, htyᵢ⟩ : ∃ cᵢ, (typeOf xᵢ c₁ env).typeOf = .ok (.ext .ipAddr, cᵢ) := by
      rcases List.mem_cons.mp hxᵢ with rfl | hmem
      · exact ⟨c₁', h₇⟩
      · exact h₈ xᵢ hmem
    split_type_of htyᵢ ; rename_i htyᵢ hl _
    have ⟨_, v, hev, hinst⟩ := (ih xᵢ hxᵢ) h₁ h₂ htyᵢ
    rw [hl] at hinst
    obtain ⟨a, rfl⟩ := instance_of_ipAddr_type_is_ipAddr hinst
    exact ⟨a, hev⟩
  simp only [EvaluatesTo, evaluate]
  rw [List.mapM₁_eq_mapM (fun x => evaluate x request entities)]
  cases hm : (x₁ :: xr :: xrs).mapM (fun x => evaluate x request entities) with
  | error e =>
    refine ⟨.prim (.bool false), ?_, bool_is_instance_of_anyBool false⟩
    obtain ⟨xᵢ, hmem, herr⟩ := List.mapM_error_implies_exists_error hm
    obtain ⟨_, hev⟩ := key xᵢ hmem
    simp only [Except.bind_err]
    simp only [EvaluatesTo, herr] at hev
    rcases hev with h | h | h | h <;> simp_all
  | ok vs =>
    simp only [Except.bind_ok]
    -- All evaluated values are ipaddrs.
    have hall_ip : ∀ v ∈ vs, ∃ a, v = .ext (.ipaddr a) := by
      intro v hv
      obtain ⟨x, hx_mem, hx_ok⟩ := List.mapM_ok_implies_all_from_ok hm v hv
      obtain ⟨a, hev⟩ := key x hx_mem
      simp only [EvaluatesTo, hx_ok] at hev
      rcases hev with h | h | h | h <;> simp only [reduceCtorEq, Except.ok.injEq] at h
      exact ⟨a, h⟩
    -- `vs` has at least two elements.
    have hlen_vs : 2 ≤ vs.length := by
      have hpl := List.mapM_preserves_length hm
      simp only [List.length_cons] at hpl
      omega
    rcases vs with _ | ⟨v₀, _ | ⟨v₁, vtail⟩⟩
    · simp only [List.length_nil] at hlen_vs; omega
    · simp only [List.length_cons, List.length_nil] at hlen_vs; omega
    · obtain ⟨a₀, rfl⟩ := hall_ip v₀ List.mem_cons_self
      simp only [call, Except.bind_ok]
      -- The ranges all extract to ipaddrs, so their `mapM` succeeds.
      have ⟨rs, hrs⟩ : ∃ rs, (v₁ :: vtail).mapM
          (fun x => match x with | .ext (.ipaddr a) => Except.ok a | _ => Except.error Error.typeError) = .ok rs := by
        apply List.all_ok_implies_mapM_ok
        intro w hw
        obtain ⟨aw, rfl⟩ := hall_ip w (List.mem_cons_of_mem _ hw)
        exact ⟨aw, rfl⟩
      refine ⟨.prim (.bool (rs.any (a₀.inRange ·))), ?_, bool_is_instance_of_anyBool _⟩
      right; right; right
      exact hrs ▸ rfl

def IsIpAddrRecognizer : ExtFun → Prop
  | .isIpv4
  | .isIpv6
  | .isLoopback
  | .isMulticast => True
  | _            => False


theorem typeOf_of_unary_call_inversion {xs : List Expr} {c : Capabilities} {env : TypeEnv} {ty₁ : TypedExpr}
  (h₁ : (xs.mapM₁ fun x => justType (typeOf x.val c env)) = Except.ok [ty₁]) :
  ∃ x₁ c₁,
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok (ty₁.typeOf, c₁)
:= by
  simp only [List.mapM₁_eq_mapM λ x => justType (typeOf x c env)] at h₁
  cases xs
  case nil =>
    simp only [List.mapM, List.mapM.loop, pure, Except.pure, List.reverse_nil,
      Except.ok.injEq, List.ne_cons_self] at h₁
  case cons hd₁ tl₁ =>
    cases tl₁
    case nil =>
      simp only [List.mapM_cons, List.mapM_nil, bind_pure_comp, map_pure] at h₁
      cases h₂ : justType (typeOf hd₁ c env)
      · simp_all only [justType, List.cons.injEq, and_true, exists_and_left, exists_eq_left', Except.map_error]
        simp at h₁
      · simp only [List.cons.injEq, and_true, exists_and_left, exists_eq_left'] at *
        simp_all only [Except.map_ok, Except.ok.injEq, List.cons.injEq, and_true]
        subst h₁ ; rename_i ty₁
        cases h₁ : typeOf hd₁ c env
        <;> simp only [justType, h₁, Except.map, Except.ok.injEq, reduceCtorEq] at h₂
        simp [h₂, ResultType.typeOf, Except.map.eq_2]
    case cons hd₂ tl₂ =>
      simp only [List.mapM_cons, bind_assoc, pure_bind] at h₁
      rw [justType, Except.map.eq_def] at h₁
      split at h₁ <;> simp at h₁
      rw [justType, Except.map.eq_def] at h₁
      split at h₁ <;> simp at h₁
      rename_i res₁ _ _ res₂ _
      cases h₂ : List.mapM (fun x => justType (typeOf x c env)) tl₂ <;> simp [h₂] at h₁

theorem type_of_call_toTime_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .toTime xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .duration ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (c₁ : Capabilities),
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁)
:= by
  simp [typeOf] at h₁
  simp_do_let (List.mapM₁ xs fun x => justType (typeOf x.val c env)) as h₂ at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq] at h₁
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₁
      have ⟨hl₁, hr₁⟩ := h₁
      rw [←hl₁]
      simp only [TypedExpr.typeOf, hr₁, List.empty_eq, true_and]
      rename_i h₃
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      rw [←h₃]
      apply typeOf_of_unary_call_inversion h₂
    }
  }

theorem type_of_call_toTime_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call .toTime xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .toTime xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .toTime xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₄, h₅, x₁, c₁', h₆, h₇⟩ := type_of_call_toTime_inversion h₃
  rw [h₄]
  subst h₅ h₆
  apply And.intro empty_guarded_capabilities_invariant
  simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
    List.mapM_nil, pure_bind, bind_assoc]
  have ih₁ := ih x₁
  simp only [List.mem_singleton, TypeOfIsSound, forall_const] at ih₁
  split_type_of h₇ ; rename_i h₇ hl₇ hr₇
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  simp only [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp only [hl₁, Except.bind_err, Except.error.injEq, reduceCtorEq, or_self, or_false, or_true,
    true_and] <;>
  try { exact type_is_inhabited_ext}
  rw [hl₇] at hr₁
  have ⟨dt₁, hr₁⟩ := instance_of_datetime_type_is_datetime hr₁
  subst hr₁
  simp only [call, gt_iff_lt, ge_iff_le, Except.bind_ok, reduceCtorEq, Except.ok.injEq, false_or,
    exists_eq_left']
  exact duration_is_instance_of_duration

theorem type_of_call_toDate_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .toDate xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .datetime ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (c₁ : Capabilities),
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁)
:= by
  simp only [typeOf] at h₁
  simp_do_let (List.mapM₁ xs fun x => justType (typeOf x.val c env)) as h₂ at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq] at h₁
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₁
      have ⟨hl₁, hr₁⟩ := h₁
      rw [←hl₁]
      simp only [TypedExpr.typeOf, hr₁, List.empty_eq, true_and]
      rename_i h₃
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      rw [←h₃]
      apply typeOf_of_unary_call_inversion h₂
    }
  }

theorem type_of_call_toDate_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call .toDate xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .toDate xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .toDate xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₄, h₅, x₁, c₁', h₆, h₇⟩ := type_of_call_toDate_inversion h₃
  rw [h₄]
  subst h₅ h₆
  apply And.intro empty_guarded_capabilities_invariant
  simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
    List.mapM_nil, pure_bind, bind_assoc]
  have ih₁ := ih x₁
  simp only [List.mem_singleton, TypeOfIsSound, forall_const] at ih₁
  split_type_of h₇ ; rename_i h₇ hl₇ hr₇
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  simp only [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp only [hl₁, Except.bind_err, Except.error.injEq, reduceCtorEq, or_self, or_false, or_true,
    true_and] <;>
  try { exact type_is_inhabited_ext}
  rw [hl₇] at hr₁
  have ⟨dt₁, hr₁⟩ := instance_of_datetime_type_is_datetime hr₁
  subst hr₁
  simp only [call, res, gt_iff_lt, ge_iff_le, Except.bind_ok]
  cases dt₁.toDate with
  | some v =>
    simp only [reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left']
    exact datetime_is_instance_of_datetime
  | none =>
    simp only [Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and]
    apply type_is_inhabited_ext

theorem type_of_call_offset_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .offset xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .datetime ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂: Capabilities),
    xs = [x₁, x₂] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁) ∧
    (typeOf x₂ c env).typeOf = .ok ((CedarType.ext .duration), c₂)
:= by
  simp only [typeOf] at h₁
  simp_do_let (List.mapM₁ xs fun x => justType (typeOf x.val c env)) as h₂ at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq] at h₁
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₁
      have ⟨hl₁, hr₁⟩ := h₁
      rw [←hl₁]
      simp only [TypedExpr.typeOf, hr₁, List.empty_eq, true_and]
      rename_i h₃
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      have ⟨ h₃ₗ, h₃ᵣ ⟩ := h₃
      rw (config := {occs := .pos [1]}) [←h₃ₗ]
      rw [←h₃ᵣ]
      apply typeOf_of_binary_call_inversion h₂
    }
  }

theorem type_of_call_offset_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call .offset xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .offset xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .offset xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
    have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_offset_inversion h₃
    rw [h₄]
    subst h₅ h₆
    apply And.intro empty_guarded_capabilities_invariant
    simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
      List.mapM_nil, pure_bind, bind_assoc]
    have ih₁ := ih x₁
    simp only [List.mem_cons, true_or, TypeOfIsSound, forall_const] at ih₁
    split_type_of h₇ ; rename_i h₇ hl₇ hr₇
    have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
    simp only [EvaluatesTo] at hl₁
    rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
    simp only [hl₁, Except.bind_err, Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and] <;>
    try { exact type_is_inhabited_ext}
    rw [hl₇] at hr₁
    have ⟨dt₁, hr₁⟩ := instance_of_datetime_type_is_datetime hr₁
    subst hr₁
    have ih₂ := ih x₂
    simp [TypeOfIsSound] at ih₂
    split_type_of h₈ ; rename_i h₈ hl₈ hr₈
    have ⟨_, v₂, hl₂, hr₂⟩ := ih₂ h₁ h₂ h₈
    simp only [EvaluatesTo] at ih₂
    rcases hl₂ with hl₂ | hl₂ | hl₂ | hl₂ <;>
    simp only [hl₂, Except.bind_err, Except.bind_ok, Except.error.injEq, reduceCtorEq, or_self,
      or_false, or_true, true_and] <;>
    try { exact type_is_inhabited_ext}
    rw [hl₈] at hr₂
    have ⟨dt₂, hr₂⟩ := instance_of_duration_type_is_duration hr₂
    subst hr₂
    simp only [call, res]
    cases dt₁.offset dt₂ with
    | some v =>
      simp only [reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left']
      exact datetime_is_instance_of_datetime
    | none =>
      simp only [Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and]
      apply type_is_inhabited_ext

theorem type_of_call_durationSince_inversion {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .durationSince xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .duration ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂: Capabilities),
    xs = [x₁, x₂] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁) ∧
    (typeOf x₂ c env).typeOf = .ok ((CedarType.ext .datetime), c₂)
:= by
  simp only [typeOf] at h₁
  simp_do_let (List.mapM₁ xs fun x => justType (typeOf x.val c env)) as h₂ at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq] at h₁
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp only [ok, Except.ok.injEq, Prod.mk.injEq, List.nil_eq] at h₁
      have ⟨hl₁, hr₁⟩ := h₁
      rw [←hl₁]
      simp only [TypedExpr.typeOf, hr₁, List.empty_eq, true_and]
      rename_i h₃
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      have ⟨ h₃ₗ, h₃ᵣ ⟩ := h₃
      rw (config := {occs := .pos [1]}) [←h₃ₗ]
      rw [←h₃ᵣ]
      apply typeOf_of_binary_call_inversion h₂
    }
  }

theorem type_of_call_durationSince_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call .durationSince xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .durationSince xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .durationSince xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
    have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_durationSince_inversion h₃
    rw [h₄]
    subst h₅ h₆
    apply And.intro empty_guarded_capabilities_invariant
    simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
      List.mapM_nil, pure_bind, bind_assoc]
    have ih₁ := ih x₁
    simp only [List.mem_cons, true_or, TypeOfIsSound, forall_const] at ih₁
    split_type_of h₇ ; rename_i h₇ hl₇ hr₇
    have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
    simp only [EvaluatesTo] at hl₁
    rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
    simp only [hl₁, Except.bind_err, Except.error.injEq, reduceCtorEq, or_self, or_false, or_true,
      true_and] <;>
    try { exact type_is_inhabited_ext}
    rw [hl₇] at hr₁
    have ⟨dt₁, hr₁⟩ := instance_of_datetime_type_is_datetime hr₁
    subst hr₁
    have ih₂ := ih x₂
    simp [TypeOfIsSound] at ih₂
    split_type_of h₈ ; rename_i h₈ hl₈ hr₈
    have ⟨_, v₂, hl₂, hr₂⟩ := ih₂ h₁ h₂ h₈
    simp only [EvaluatesTo] at hl₂
    rcases hl₂ with hl₂ | hl₂ | hl₂ | hl₂ <;>
    simp only [hl₂, Except.bind_err, Except.bind_ok, Except.error.injEq, reduceCtorEq, or_self,
      or_false, or_true, true_and] <;>
    try { exact type_is_inhabited_ext}
    rw [hl₈] at hr₂
    have ⟨dt₂, hr₂⟩ := instance_of_datetime_type_is_datetime hr₂
    subst hr₂
    simp only [call, res]
    cases dt₁.durationSince dt₂ with
    | some v =>
      simp only [reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left']
      exact duration_is_instance_of_duration
    | none =>
      simp only [Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and]
      apply type_is_inhabited_ext

theorem type_of_call_ipAddr_recognizer_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₀ : IsIpAddrRecognizer xfn)
  (h₁ : typeOf (Expr.call xfn xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .bool .anyBool ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (c₁ : Capabilities),
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok ((.ext .ipAddr), c₁)
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall] at h₁
  simp [IsIpAddrRecognizer] at h₀
  split at h₀
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp [ok] at h₁
      have ⟨hl₁, hr₁⟩ := h₁
      rw [←hl₁]
      simp only [TypedExpr.typeOf, hr₁, List.empty_eq, true_and]
      rename_i h₃
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      rw [←h₃]
      apply typeOf_of_unary_call_inversion h₂
    }
  }

theorem type_of_call_ipAddr_recognizer_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : IsIpAddrRecognizer xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₄, h₅, x₁, c₁', h₆, h₇⟩ := type_of_call_ipAddr_recognizer_inversion h₀ h₃
  rw [h₄]
  subst h₅ h₆
  apply And.intro empty_guarded_capabilities_invariant
  simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
    List.mapM_nil, pure_bind, bind_assoc]
  have ih₁ := ih x₁
  simp [TypeOfIsSound] at ih₁
  split_type_of h₇ ; rename_i h₇ hl₇ hr₇
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  simp [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp [hl₁] <;>
  try { exact type_is_inhabited_bool}
  rw [hl₇] at hr₁
  have ⟨ip₁, hr₁⟩ := instance_of_ipAddr_type_is_ipAddr hr₁
  subst hr₁
  simp [IsIpAddrRecognizer] at h₀
  split at h₀ <;>
  simp [call] <;> try { contradiction }
  all_goals {
    apply bool_is_instance_of_anyBool
  }

def IsDurationConverter : ExtFun → Prop
  | .toMilliseconds
  | .toSeconds
  | .toMinutes
  | .toHours
  | .toDays => True
  | _       => False

theorem type_of_call_duration_converter_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : TypeEnv} {ty : TypedExpr}
  (h₀ : IsDurationConverter xfn)
  (h₁ : typeOf (Expr.call xfn xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .int ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (c₁ : Capabilities),
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok ((.ext .duration), c₁)
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall] at h₁
  simp [IsDurationConverter] at h₀
  split at h₀
  all_goals {
    split at h₁ <;> try { contradiction }
    all_goals {
      simp [ok] at h₁
      have ⟨hl₁, hr₁⟩ := h₁
      rw [←hl₁]
      simp only [TypedExpr.typeOf, hr₁, List.empty_eq, true_and]
      rename_i h₃
      cases tys <;> try simp at h₃
      rename_i tys
      cases tys <;> try simp at h₃
      rw [←h₃]
      apply typeOf_of_unary_call_inversion h₂
    }
  }

theorem type_of_call_duration_converter_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : IsDurationConverter xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  have ⟨h₄, h₅, x₁, c₁', h₆, h₇⟩ := type_of_call_duration_converter_inversion h₀ h₃
  rw [h₄]
  subst h₅ h₆
  apply And.intro empty_guarded_capabilities_invariant
  simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
    List.mapM_nil, pure_bind, bind_assoc]
  have ih₁ := ih x₁
  simp [TypeOfIsSound] at ih₁
  split_type_of h₇ ; rename_i h₇ hl₇ hr₇
  have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
  simp [EvaluatesTo] at hl₁
  rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
  simp [hl₁] <;>
  try { exact type_is_inhabited_int}
  rw [hl₇] at hr₁
  have ⟨ip₁, hr₁⟩ := instance_of_duration_type_is_duration hr₁
  subst hr₁
  simp [IsDurationConverter] at h₀
  split at h₀ <;>
  simp only [call, reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left'] <;> try { contradiction }
  all_goals {
    apply InstanceOfType.instance_of_int
  }

theorem type_of_call_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : TypeEnv} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : InstanceOfWellFormedEnvironment request entities env)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType env v ty.typeOf
:= by
  match xfn with
  | .decimal            => exact type_of_call_decimal_is_sound h₃
  | .ip                 => exact type_of_call_ip_is_sound h₃
  | .datetime           => exact type_of_call_datetime_is_sound h₃
  | .duration           => exact type_of_call_duration_is_sound h₃
  | .lessThan
  | .lessThanOrEqual
  | .greaterThan
  | .greaterThanOrEqual => exact type_of_call_decimal_comparator_is_sound (by simp [IsDecimalComparator]) h₁ h₂ h₃ ih
  | .isInRange          => exact type_of_call_isInRange_comparator_is_sound h₁ h₂ h₃ ih
  | .isIpv4
  | .isIpv6
  | .isLoopback
  | .isMulticast        => exact type_of_call_ipAddr_recognizer_is_sound (by simp [IsIpAddrRecognizer]) h₁ h₂ h₃ ih
  | .offset             => exact type_of_call_offset_is_sound h₁ h₂ h₃ ih
  | .durationSince      => exact type_of_call_durationSince_is_sound h₁ h₂ h₃ ih
  | .toDate             => exact type_of_call_toDate_is_sound h₁ h₂ h₃ ih
  | .toTime             => exact type_of_call_toTime_is_sound h₁ h₂ h₃ ih
  | .toMilliseconds
  | .toSeconds
  | .toMinutes
  | .toHours
  | .toDays             => exact type_of_call_duration_converter_is_sound (by simp [IsDurationConverter]) h₁ h₂ h₃ ih

/- Used by `type_of_preserves_evaluation_results` -/
theorem type_of_preserves_evaluation_results_call {xfn ty c₂ request entities} {xs : List Expr} {tys : List TypedExpr} :
  typeOfCall xfn tys xs = Except.ok (ty, c₂) →
  List.mapM (fun x => evaluate x request entities) xs = List.mapM (fun y => evaluate y.toExpr request entities) tys →
  evaluate (Expr.call xfn xs) request entities = evaluate ty.toExpr request entities
:= by
  intro h₁ h₂
  simp [typeOfCall, typeOfIsInRange] at h₁
  split at h₁ <;>
  (try simp [ok, err, do_ok_eq_ok] at h₁)
  all_goals
    first
      | (try replace ⟨_, _, h₁⟩ := h₁
         try replace ⟨h₁, _⟩ := h₁
         subst h₁
         simp [TypedExpr.toExpr, evaluate, List.mapM₁_eq_mapM (evaluate · request entities), List.map₁_eq_map, List.mapM_map, h₂, Function.comp_def])
      -- isInRange: `typeOfIsInRange` leaves a match + inner `if`; split both, the non-ipAddr
      -- branches are contradictory, the all-ipAddr branch gives `... = ty`
      | (split at h₁ <;> (try (split at h₁ <;> simp at h₁)) <;>
         (first
           | contradiction
           | (obtain ⟨h₁, _⟩ := h₁
              subst h₁
              simp [TypedExpr.toExpr, evaluate, List.mapM₁_eq_mapM (evaluate · request entities), List.map₁_eq_map, List.mapM_map, h₂, Function.comp_def])))

end Cedar.Thm
