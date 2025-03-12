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

theorem type_of_call_decimal_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
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

theorem type_of_call_decimal_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .decimal xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .decimal xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .decimal xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  · apply InstanceOfType.instance_of_ext
    simp [InstanceOfExtType]

theorem type_of_call_datetime_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .datetime xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .datetime ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.Datetime.parse s).isSome
:= by
  simp only [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp only [h₂, Except.bind_err, reduceCtorEq] at h₁
  rename_i tys
  simp only [typeOfCall, typeOfConstructor, List.empty_eq, Except.bind_ok] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  simp only [h₁, List.empty_eq, List.cons.injEq, Expr.lit.injEq, Prim.string.injEq, and_true,
    exists_eq_left', true_and]
  rename_i h₃
  cases h₁ ; subst ty
  simp only [TypedExpr.typeOf, h₃, Option.isSome_some, and_self]

theorem type_of_call_datetime_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .datetime xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .datetime xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .datetime xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  · apply InstanceOfType.instance_of_ext
    simp [InstanceOfExtType]

theorem type_of_call_duration_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .duration xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .duration ∧
  c' = ∅ ∧
  ∃ (s : String),
    xs = [.lit (.string s)] ∧
    (Cedar.Spec.Ext.Datetime.duration s).isSome
:= by
  simp only [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp only [h₂, Except.bind_err, reduceCtorEq] at h₁
  rename_i tys
  simp only [typeOfCall, typeOfConstructor, List.empty_eq] at h₁
  split at h₁ <;> simp [ok, err] at h₁
  rename_i s
  split at h₁ <;> simp at h₁
  cases h₁ ; subst ty c'
  rename_i h₃
  simp [TypedExpr.typeOf, h₃]

theorem type_of_call_duration_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .duration xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .duration xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .duration xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  · apply InstanceOfType.instance_of_ext
    simp [InstanceOfExtType]

theorem type_of_call_ip_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
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

theorem type_of_call_ip_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : typeOf (Expr.call .ip xs) c₁ env = Except.ok (ty, c₂)) :
  GuardedCapabilitiesInvariant (Expr.call .ip xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .ip xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  · apply InstanceOfType.instance_of_ext
    simp [InstanceOfExtType]

theorem typeOf_of_binary_call_inversion {xs : List Expr} {c : Capabilities} {env : Environment} {ty₁ ty₂ : TypedExpr}
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
        simp only [List.attach_def, List.pmap, List.mapM_cons,
          List.mapM_pmap_subtype (fun x => justType (typeOf x c env)), bind_assoc, pure_bind] at h₁
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

theorem type_of_call_decimal_comparator_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
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

theorem type_of_call_decimal_comparator_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : IsDecimalComparator xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  rcases hl₂ with hl₂ | hl₂ | hl₂ | hl₂ <;>
  simp [hl₂] <;>
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
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


theorem type_of_call_isInRange_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .isInRange xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .bool .anyBool ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂ : Capabilities),
    xs = [x₁, x₂] ∧
    (typeOf x₁ c env).typeOf = .ok ((.ext .ipAddr), c₁) ∧
    (typeOf x₂ c env).typeOf = .ok ((.ext .ipAddr), c₂)
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp [h₂] at h₁
  rename_i tys
  simp [typeOfCall] at h₁
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
    rename_i tys
    cases tys <;> try simp at h₃
    have ⟨ h₃ₗ, h₃ᵣ ⟩ := h₃
    rw (config := {occs := .pos [1]}) [←h₃ₗ]
    rw [←h₃ᵣ]
    apply typeOf_of_binary_call_inversion h₂
  }

theorem type_of_call_isInRange_comparator_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call .isInRange xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .isInRange xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .isInRange xs) request entities v ∧ InstanceOfType v ty.typeOf
:= by
  have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_isInRange_inversion h₃
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
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  rcases hl₂ with hl₂ | hl₂ | hl₂ | hl₂ <;>
  simp [hl₂] <;>
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
  rw [hl₇] at hr₁
  have ⟨d₁, hr₁⟩ := instance_of_ipAddr_type_is_ipAddr hr₁
  rw [hl₈] at hr₂
  have ⟨d₂, hr₂⟩ := instance_of_ipAddr_type_is_ipAddr hr₂
  subst hr₁ hr₂
  simp [call]
  apply bool_is_instance_of_anyBool

def IsIpAddrRecognizer : ExtFun → Prop
  | .isIpv4
  | .isIpv6
  | .isLoopback
  | .isMulticast => True
  | _            => False


theorem typeOf_of_unary_call_inversion {xs : List Expr} {c : Capabilities} {env : Environment} {ty₁ : TypedExpr}
  (h₁ : (xs.mapM₁ fun x => justType (typeOf x.val c env)) = Except.ok [ty₁]) :
  ∃ x₁ c₁,
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok (ty₁.typeOf, c₁)
:= by
  simp only [List.mapM₁] at h₁
  cases xs
  case nil =>
    simp only [List.mapM, List.attach_nil, List.mapM.loop, pure, Except.pure, List.reverse_nil,
      Except.ok.injEq, List.ne_cons_self] at h₁
  case cons hd₁ tl₁ =>
    cases tl₁
    case nil =>
      simp only [List.attach_cons, List.attach_nil, List.map_nil, List.mapM_cons, List.mapM_nil,
        bind_pure_comp, map_pure] at h₁
      cases h₂ : justType (typeOf hd₁ c env)
      · simp_all only [justType, List.cons.injEq, and_true, exists_and_left, exists_eq_left', Except.map_error, Except.map_ok, Except.ok.injEq]
        simp at h₁
      · simp only [List.cons.injEq, and_true, exists_and_left, exists_eq_left'] at *
        simp_all only [Except.map_ok, Except.ok.injEq, List.cons.injEq, and_true]
        subst h₁ ; rename_i ty₁
        cases h₁ : typeOf hd₁ c env
        <;> simp only [justType, h₁, Except.map, Except.ok.injEq, reduceCtorEq] at h₂
        simp [h₂, ResultType.typeOf, Except.map.eq_2]
    case cons hd₂ tl₂ =>
      simp only [List.attach_def, List.pmap, List.mapM_cons,
        List.mapM_pmap_subtype (fun x => justType (typeOf x c env)), bind_assoc, pure_bind] at h₁
      rw [justType, Except.map.eq_def] at h₁
      split at h₁ <;> simp at h₁
      rw [justType, Except.map.eq_def] at h₁
      split at h₁ <;> simp at h₁
      rename_i res₁ _ _ res₂ _
      cases h₂ : List.mapM (fun x => justType (typeOf x c env)) tl₂ <;> simp [h₂] at h₁

theorem type_of_call_toTime_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .toTime xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .duration ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (c₁ : Capabilities),
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁)
:= by
  simp [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp only [h₂, Except.bind_err, reduceCtorEq] at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq, Except.bind_ok] at h₁
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

theorem type_of_call_toTime_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call .toTime xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .toTime xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .toTime xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  try { exact type_is_inhabited (CedarType.ext .duration)}
  rw [hl₇] at hr₁
  have ⟨dt₁, hr₁⟩ := instance_of_datetime_type_is_datetime hr₁
  subst hr₁
  simp only [call, gt_iff_lt, ge_iff_le, Except.bind_ok, reduceCtorEq, Except.ok.injEq, false_or,
    exists_eq_left']
  apply InstanceOfType.instance_of_ext
  simp only [InstanceOfExtType]

theorem type_of_call_toDate_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .toDate xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .datetime ∧
  c' = ∅ ∧
  ∃ (x₁ : Expr) (c₁ : Capabilities),
    xs = [x₁] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁)
:= by
  simp only [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp only [h₂, Except.bind_err, reduceCtorEq] at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq, Except.bind_ok] at h₁
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

theorem type_of_call_toDate_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call .toDate xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .toDate xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .toDate xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  try { exact type_is_inhabited (CedarType.ext .datetime)}
  rw [hl₇] at hr₁
  have ⟨dt₁, hr₁⟩ := instance_of_datetime_type_is_datetime hr₁
  subst hr₁
  simp only [call, res, gt_iff_lt, ge_iff_le, Except.bind_ok]
  cases dt₁.toDate with
  | some v =>
    simp only [reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left']
    apply InstanceOfType.instance_of_ext
    simp [InstanceOfExtType]
  | none =>
    simp only [Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and]
    apply type_is_inhabited

theorem type_of_call_offset_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .offset xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .datetime ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂: Capabilities),
    xs = [x₁, x₂] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁) ∧
    (typeOf x₂ c env).typeOf = .ok ((CedarType.ext .duration), c₂)
:= by
  simp only [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp only [h₂, Except.bind_err, reduceCtorEq] at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq, Except.bind_ok] at h₁
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

theorem type_of_call_offset_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call .offset xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .offset xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .offset xs) request entities v ∧ InstanceOfType v ty.typeOf
:= by
    have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_offset_inversion h₃
    rw [h₄]
    subst h₅ h₆
    apply And.intro empty_guarded_capabilities_invariant
    simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
      List.mapM_nil, pure_bind, bind_assoc]
    have ih₁ := ih x₁
    simp only [List.mem_cons, List.mem_singleton, true_or, TypeOfIsSound, forall_const] at ih₁
    split_type_of h₇ ; rename_i h₇ hl₇ hr₇
    have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
    simp only [EvaluatesTo] at hl₁
    rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
    simp only [hl₁, Except.bind_err, Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and] <;>
    try { exact type_is_inhabited (CedarType.ext .datetime)}
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
    try { exact type_is_inhabited (CedarType.ext .datetime)}
    rw [hl₈] at hr₂
    have ⟨dt₂, hr₂⟩ := instance_of_duration_type_is_duration hr₂
    subst hr₂
    simp only [call, res]
    cases dt₁.offset dt₂ with
    | some v =>
      simp only [reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left']
      apply InstanceOfType.instance_of_ext
      simp [InstanceOfExtType]
    | none =>
      simp only [Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and]
      apply type_is_inhabited

theorem type_of_call_durationSince_inversion {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
  (h₁ : typeOf (Expr.call .durationSince xs) c env = Except.ok (ty, c')) :
  ty.typeOf = .ext .duration ∧
  c' = ∅ ∧
  ∃ (x₁ x₂ : Expr) (c₁ c₂: Capabilities),
    xs = [x₁, x₂] ∧
    (typeOf x₁ c env).typeOf = .ok ((CedarType.ext .datetime), c₁) ∧
    (typeOf x₂ c env).typeOf = .ok ((CedarType.ext .datetime), c₂)
:= by
  simp only [typeOf] at h₁
  cases h₂ : List.mapM₁ xs fun x => justType (typeOf x.val c env) <;>
  simp only [h₂, Except.bind_err, reduceCtorEq] at h₁
  rename_i tys
  simp only [typeOfCall, List.empty_eq, Except.bind_ok] at h₁
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

theorem type_of_call_durationSince_is_sound {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call .durationSince xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call .durationSince xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call .durationSince xs) request entities v ∧ InstanceOfType v ty.typeOf
:= by
    have ⟨h₄, h₅, x₁, x₂, c₁', c₂', h₆, h₇, h₈⟩ := type_of_call_durationSince_inversion h₃
    rw [h₄]
    subst h₅ h₆
    apply And.intro empty_guarded_capabilities_invariant
    simp only [EvaluatesTo, evaluate, List.mapM₁, List.attach_def, List.pmap, List.mapM_cons,
      List.mapM_nil, pure_bind, bind_assoc]
    have ih₁ := ih x₁
    simp only [List.mem_cons, List.mem_singleton, true_or, TypeOfIsSound, forall_const] at ih₁
    split_type_of h₇ ; rename_i h₇ hl₇ hr₇
    have ⟨_, v₁, hl₁, hr₁⟩ := ih₁ h₁ h₂ h₇
    simp only [EvaluatesTo] at hl₁
    rcases hl₁ with hl₁ | hl₁ | hl₁ | hl₁ <;>
    simp only [hl₁, Except.bind_err, Except.error.injEq, reduceCtorEq, or_self, or_false, or_true,
      true_and] <;>
    try { exact type_is_inhabited (CedarType.ext .duration)}
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
    try { exact type_is_inhabited (CedarType.ext .duration)}
    rw [hl₈] at hr₂
    have ⟨dt₂, hr₂⟩ := instance_of_datetime_type_is_datetime hr₂
    subst hr₂
    simp only [call, res]
    cases dt₁.durationSince dt₂ with
    | some v =>
      simp only [reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left']
      apply InstanceOfType.instance_of_ext
      simp [InstanceOfExtType]
    | none =>
      simp only [Except.error.injEq, reduceCtorEq, or_self, or_false, or_true, true_and]
      apply type_is_inhabited

theorem type_of_call_ipAddr_recognizer_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
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

theorem type_of_call_ipAddr_recognizer_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : IsIpAddrRecognizer xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  try { exact type_is_inhabited (CedarType.bool BoolType.anyBool)}
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

theorem type_of_call_duration_converter_inversion {xfn : ExtFun} {xs : List Expr} {c c' : Capabilities} {env : Environment} {ty : TypedExpr}
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

theorem type_of_call_duration_converter_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₀ : IsDurationConverter xfn)
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType v ty.typeOf
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
  try { exact type_is_inhabited (.int)}
  rw [hl₇] at hr₁
  have ⟨ip₁, hr₁⟩ := instance_of_duration_type_is_duration hr₁
  subst hr₁
  simp [IsDurationConverter] at h₀
  split at h₀ <;>
  simp only [call, reduceCtorEq, Except.ok.injEq, false_or, exists_eq_left'] <;> try { contradiction }
  all_goals {
    apply InstanceOfType.instance_of_int
  }

theorem type_of_call_is_sound {xfn : ExtFun} {xs : List Expr} {c₁ c₂ : Capabilities} {env : Environment} {ty : TypedExpr} {request : Request} {entities : Entities}
  (h₁ : CapabilitiesInvariant c₁ request entities)
  (h₂ : RequestAndEntitiesMatchEnvironment env request entities)
  (h₃ : typeOf (Expr.call xfn xs) c₁ env = Except.ok (ty, c₂))
  (ih : ∀ (xᵢ : Expr), xᵢ ∈ xs → TypeOfIsSound xᵢ) :
  GuardedCapabilitiesInvariant (Expr.call xfn xs) c₂ request entities ∧
  ∃ v, EvaluatesTo (Expr.call xfn xs) request entities v ∧ InstanceOfType v ty.typeOf
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

end Cedar.Thm
